// PASS    | assign_frame
// ---------------------------------------------------------------------------
// USAGE   | assign_frame : assign_frame::Program -> 
//         |                discard_call_live::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with the spillled variable list discarded, with
//         | spills now being placed onto the frame.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass walks through the spills, and each spilled variable gets a
// frame location. We update the location vector for each binding to reflect
// these new locations.
//// ---------------------------------------------------------------------------

// use util::Binop;
// use util::Relop;
// use util::Label;
use util::Ident;
use util::Location;
// use util::mk_uvar;
use util::REGISTERS;

use alloc_lang::Program;
use alloc_lang::LetrecEntry;
use alloc_lang::RegAllocForm;
// use alloc_lang::RegAllocInfo;
use alloc_lang::Body;
// use alloc_lang::Exp;
// use alloc_lang::Pred;
// use alloc_lang::Effect;
// use alloc_lang::Variable;
// use alloc_lang::Triv;
use alloc_lang::RegConflict;

use std::collections::HashMap;

// ---------------------------------------------------------------------------
// INPUT / OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// #[derive(Debug)]
// pub enum Program { Letrec(Vec<LetrecEntry>, Body) }
//                                        // ^ Stores allocation info for the body 
// 
// #[derive(Debug)]
// pub struct LetrecEntry
//   { label : Label
//   , rhs   : Body
//   }
// 
// #[derive(Debug)]
// pub struct Body 
//   { alloc : RegAllocForm
//   , exp : Exp
//   }
// 
// pub enum RegAllocForm
// 	{ Allocated(HashMap<Ident, Location>)
//  , Unallocated(mut RegAllocInfo, mut HashMap<Ident, Location>)
//  }
// 
// pub struct RegAllocInfo 
//   { pub locals             : Vec<Ident>
//   , pub unspillables       : Vec<Ident>
//   , pub spills             : Vec<Ident>
//   , pub frame_conflicts    : Vec<(Ident, Vec<FrameConflict>)>
//   , pub register_conflicts : Vec<(Ident, Vec<RegConflict>)>
//   }
//
// pub enum Exp 
//   { Call(Triv, Vec<Location>)
//   , If(Pred,Box<Exp>,Box<Exp>)
//   , Begin(Vec<Effect>,Box<Exp>)
//   }
// 
// pub enum Pred
//   { True
//   , False
//   , Op(Relop,Triv,Triv)
//   , If(Box<Pred>,Box<Pred>,Box<Pred>)
//   , Begin(Vec<Effect>, Box<Pred>)
//   }
// 
// pub enum Effect
//   { SetOp(Triv, (Binop, Triv, Triv))
//   , Set(Triv, Triv)
//   , Nop
//   , MSet(Triv, Triv, Triv)
//   , ReturnPoint(Label, Exp, i64)
//   , If(Pred, Box<Effect>, Box<Effect>)
//   , Begin(Box<Vec<Effect>>, Box<Effect>)
//   }
// 
// pub enum Variable 
//   { Loc(Location)
//   , UVar(Ident)
//   }
// 
// pub enum Triv 
//   { Var(Variable)
//   , Num(i64) 
//   , Label(Label)
//   , MRef(Triv, Triv)
//   }
// 
//pub enum FrameConflict
//  { Var(Ident)
//  , FrameVar(i64)
//  }
//
// pub enum RegConflict
//   { Var(Ident)
//   , Reg(Ident)
//   }



// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn assign_registers(input : Program) -> Program {
  return match input 
  { Program::Letrec(letrecs, body_exp) =>  
      Program::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                     , body(body_exp))
  }  
}

fn letrec_entry(input : LetrecEntry) -> LetrecEntry {
  LetrecEntry 
  { label : input.label
  , rhs   : body(input.rhs)
  }
}

fn body(input: Body) -> Body {
  match input.alloc
  { RegAllocForm::Allocated(_)                  => Body { alloc : input.alloc , expression : input.expression }
  , RegAllocForm::Unallocated(mut alloc_info, mut locs) => {
      let (allocs, spills) = allocate(&mut alloc_info.register_conflicts, REGISTERS.clone());
      if spills.is_empty() {
        return Body { alloc : RegAllocForm::Allocated(allocs), expression : input.expression };
      } else {
        // It would be good to check for unspillability here.
        alloc_info.spills = spills;
        return Body { alloc : RegAllocForm::Unallocated(alloc_info, locs),  expression : input.expression };
      }
    }
  }
}

fn select_highest_incident_node(graph : &mut Vec<(Ident, Vec<RegConflict>)>) -> usize {
  let (first_node, ref first_edges) = graph[0];
  
  let mut index : usize                = 0;
  let mut highest_index : usize        = 0;
  let mut highest_incident : usize     = first_edges.len();

  while index < graph.len() {
    let (this_node, ref this_conflicts) = graph[index];
    let size = this_conflicts.len();

    if size > highest_incident {
      highest_incident                = size;
      highest_index                   = index;
    }
    index = index + 1;
  }

  highest_index
}

// Returns a set of new allocations and a set of newly-spilled variables.
fn allocate(conflicts : &mut Vec<(Ident, Vec<RegConflict>)>, registers : Vec<Location>) 
           -> (HashMap<Ident, Location>, Vec<Ident>) {

  if conflicts.is_empty() {
    return (HashMap::new(), Vec::new())
  }

  // pull out the node with the highest incident
  let index = select_highest_incident_node(conflicts);
  let (node, node_conflicts) = conflicts.remove(index);

  // recur without it
  let allocs_spills = allocate(conflicts, registers.clone());
  let mut allocations   = allocs_spills.0;
  let mut spills        = allocs_spills.1;

  // compute all the conflicts in our node's conflict entry that haven't been spilled
  let unspilled_conflicts : Vec<RegConflict> = node_conflicts.into_iter().filter(|id| !spills.contains(&regconflict_id(*id))).collect();

  // compute all the allocated registers for our conflicts
  let conflict_registers  : Vec<Location> = (&allocations).clone().into_iter()
                                                          .filter(|(id, loc)| unspilled_conflicts.contains(&RegConflict::Var(id.clone())))
                                                          .map(|(id, loc)| loc)
                                                           .collect();

  // This can be much nicer when Vec's remove_item stabilizes
  // Compute all the registers that we are allowed to use
  // (i.e., the registers that aren't assigned to our unspilled 
  //  variable conflicts, and that aren't part of our current own 
  //  conflict list)
  let possible_registers : Vec<Location> = registers.into_iter()
                                                    .filter(|reg| !unspilled_conflicts.contains(&loc_as_regconflict(reg.clone())))
                                                    .filter(|reg| !conflict_registers.contains(&&reg.clone()))
                                                    .collect();

  if possible_registers.is_empty() {
    spills.push(node);
  } else {
    allocations.insert(node, possible_registers[0]);
  }

  (allocations, spills)
}

fn regconflict_id(input : RegConflict) -> Ident {
  match input 
  { RegConflict::Var(v) => v
  , RegConflict::Reg(r) => r
  }
}

fn loc_as_regconflict(loc : Location) -> RegConflict {
  match loc 
  { Location::Reg(r)      => RegConflict::Reg(r)
  , Location::FrameVar(_) => panic!("Tried to convert a frame variable to a register conflict during register allocation!")
  }
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

pub mod test {

  macro_rules! mk_box {
    ($e:expr) => [Box::new($e)]
  }

  use util::index_fvar;
  use util::mk_uvar;
  use util::Binop;
  use util::Relop;
  use util::Label;
  use util::Ident;
  use util::Location;

  use alloc_lang::Program;
  use alloc_lang::LetrecEntry;
  use alloc_lang::RegAllocForm;
  use alloc_lang::RegAllocInfo;
  use alloc_lang::Exp;
  use alloc_lang::Pred;
  use alloc_lang::Body;
  use alloc_lang::Effect;
  use alloc_lang::Variable;
  use alloc_lang::Triv;
  use alloc_lang::RegConflict;
  use alloc_lang::reg_to_conflict;
  use alloc_lang::var_to_reg_conflict;

  use std::collections::HashMap;

  fn calle(call : Triv, args : Vec<Location>) -> Exp { Exp::Call(call, args) }

  fn ife(test : Pred, conseq : Exp, alt : Exp) -> Exp { Exp::If(test, mk_box!(conseq), mk_box!(alt)) }

  fn begine(args : Vec<Effect>, base : Exp) -> Exp { Exp::Begin(args, mk_box!(base)) }

  fn rop(op : Relop, t1 : Triv, t2 : Triv) -> Pred { Pred::Op(op, t1, t2) }

  fn ifp(test : Pred, conseq : Pred, alt : Pred) -> Pred { Pred::If(mk_box!(test), mk_box!(conseq), mk_box!(alt)) }

  fn beginp(args : Vec<Effect>, base : Pred) -> Pred { Pred::Begin(args, mk_box!(base)) }

  fn setopf(t1 : Triv, op : Binop, arg1 : Triv, arg2 : Triv) -> Effect { Effect::SetOp(t1, (op, arg1, arg2)) }

  fn setf(dest : Triv, src : Triv) -> Effect { Effect::Set(dest, src) }
  
  fn nopf() -> Effect { Effect::Nop }
  
  fn msetf(dest : Triv, src : Triv, offset : Triv) -> Effect { Effect::MSet(dest, src, offset) }
  
  fn retf(lbl : Label,  frame_size : i64, body : Exp) -> Effect { Effect::ReturnPoint(lbl, body, frame_size) }
  
  fn iff(test : Pred, conseq : Effect, alt : Effect) -> Effect { Effect::If(test, mk_box!(conseq), mk_box!(alt)) }
 
  fn beginf(args : Vec<Effect>, base : Effect) -> Effect { Effect::Begin(mk_box!(args), mk_box!(base)) }
  
  fn uv(name : Ident) -> Variable { Variable::UVar(name) }

  fn vt(name : Ident) -> Triv { Triv::Var(Variable::UVar(name)) }
  
  fn nt(val : i64) -> Triv { Triv::Num(val) }
  
  fn lt(lbl : Label) -> Triv { Triv::Label(lbl) }
  
  fn mreft(src : Triv, offset : Triv) -> Triv { Triv::MRef(mk_box!(src), mk_box!(offset)) }

  fn fvar(n: i64) -> Triv { Triv::Var(Variable::Loc(index_fvar(n))) }

  fn reg(s: &str) -> Triv { Triv::Var(Variable::Loc(Location::Reg(Ident::from_str(s)))) }
  
  fn regl(s: &str) -> Location { Location::Reg(Ident::from_str(s)) }

  fn mk_lbl(s : &str) -> Label { Label { label : Ident::from_str(s) } }

  fn mk_alloc_form(input_reg_conflicts : Vec<(Ident, Vec<RegConflict>)>) -> RegAllocInfo
  { RegAllocInfo
    { locals             : Vec::new()
    , unspillables       : Vec::new()
    , spills             : Vec::new()
    , frame_conflicts    : Vec::new()
    , register_conflicts : input_reg_conflicts
    }
  }

  pub fn test1() -> Program {

    let x0 = mk_uvar("x");
    let x1 = mk_uvar("x");
    let x2 = mk_uvar("x");
    let x3 = mk_uvar("x");
    let y4 = mk_uvar("y");

    let z5 = mk_uvar("z");
    let z6 = mk_uvar("z");
    let z7 = mk_uvar("z");
    let z8 = mk_uvar("z");
    let z9 = mk_uvar("z");

    let z10 = mk_uvar("z");
    let z11 = mk_uvar("z");
    let z12 = mk_uvar("z");

    let mut map = HashMap::new();
    map.insert(x0, regl("rbx"));
    map.insert(z6, Location::FrameVar(2));
    map.insert(x2, regl("r8"));
    map.insert(x3, regl("r9"));
    map.insert(y4, regl("r15"));

    let mut body_map = HashMap::new();
    body_map.insert(x2, regl("r8"));
    body_map.insert(x3, regl("r9"));

    let binding1_alloc = 
      mk_alloc_form(vec![ (x0, vec![var_to_reg_conflict(x1), var_to_reg_conflict(x2), reg_to_conflict(regl("rax"))])
                        , (x1, vec![var_to_reg_conflict(x0), reg_to_conflict(regl("r12")),  reg_to_conflict(regl("rbp"))])
                        , (x2, vec![var_to_reg_conflict(x0), reg_to_conflict(regl("r10")), reg_to_conflict(regl("r9"))])
                        , (x3, vec![reg_to_conflict(regl("r11")), reg_to_conflict(regl("r10")), reg_to_conflict(regl("r9"))])]);


    let binding1 = 
      LetrecEntry
      { label : mk_lbl("X1")
      , rhs : Body
              { alloc : RegAllocForm::Unallocated(binding1_alloc, map)
              , expression : ife(rop(Relop::LT, vt(x2), vt(x3))
                                , begine(vec![ setopf(vt(x1), Binop::Plus, vt(x1), nt(35)) 
                                             , msetf(vt(x0), nt(1), nt(40))
                                             , msetf(vt(x0), vt(y4), nt(25))
                                             , retf(mk_lbl("foo"), 4,
                                                    begine( vec![ setf(reg("rax"), fvar(1)) ]
                                                          , calle(lt(mk_lbl("X3")), vec![])) ) 
                                             , setf(vt(x0), mreft(reg("rax"), nt(1)))
                                             ]
                                        , calle(lt(mk_lbl("X2")), vec![]))
                                , begine(vec![ setopf(vt(x1), Binop::Plus, vt(x1), nt(35)) ]
                                        , calle(lt(mk_lbl("X2")), vec![])))
              }
      };

    let mut body_map = HashMap::new();
    body_map.insert(x2, regl("r8"));
    body_map.insert(x3, regl("r9"));


    let test_body = 
      Body 
      { alloc : RegAllocForm::Allocated(body_map)
      , expression : begine(vec![ setf(vt(x2), nt(0))
                                , setf(vt(x3), nt(1))
                                ]
                           , calle(lt(mk_lbl("X1")), vec![regl("rax"), regl("rbp")]))
      };

    Program::Letrec(vec![binding1], test_body)
  }

}
