// PASS    | assign_registers
// ---------------------------------------------------------------------------
// USAGE   | assign_registers : alloc_lang::Program -> 
//         |                    assign_frame::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with register alloctions (or updated spills).
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass performs a graph-coloring-style register allocation, wherein we
// recursively color the conflict graph nodes with register colors until either
// everything is colored or we have a list of variables to spill.
//
// If everything is colored, we finalize allocation. If not, we push spills
// into the spill form and continue.
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

use petgraph::graph::Graph;
use petgraph::graph::NodeIndex;
use petgraph::Undirected;

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
//   , pub call_lives         : Vec<Variable>
//   , pub frame_conflicts    : Vec<(Ident, Vec<FrameConflict>)>
//   , pub register_conflicts : Vec<(Ident, Vec<RegConflict>)>
//   , pub new_frames         : Vec<Vec<Ident>>
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
//   , Begin(Box<Vec<Effect>>)
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
  , RegAllocForm::Unallocated(mut alloc_info, locs) => {
      let mut variables = 
        alloc_info.register_conflicts.node_indices()
                                     .filter(|n| alloc_info.register_conflicts.node_weight(*n).unwrap().is_var())
                                     .collect();

      let (allocs, spills) = allocate(&mut variables, &mut alloc_info.register_conflicts, REGISTERS.clone());
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

// ---------------------------------------------------------------------------

// Returns a set of new allocations and a set of newly-spilled variables.
fn allocate(nodes : &mut Vec<NodeIndex>, conflicts : &mut Graph<RegConflict, (), Undirected>, registers : Vec<Location>) 
           -> (HashMap<Ident, Location>, Vec<Ident>) {

  if nodes.is_empty() {
    return (HashMap::new(), Vec::new())
  }

  let node : NodeIndex = select_highest_incident_node(&mut nodes.clone(), conflicts);
  let node_conflicts : Vec<RegConflict> = 
    conflicts.neighbors(node)
             .map(|n| conflicts.node_weight(n).unwrap().clone())
             .collect::<Vec<_>>();

  let node_id : RegConflict = conflicts.node_weight(node).unwrap().clone();

  let node_index = nodes.iter().position(|&r| r == node).unwrap();
  nodes.remove(node_index);
  conflicts.remove_node(node);

  // recur without it
  let allocs_spills = allocate(nodes, conflicts, registers.clone());
  let mut allocations   = allocs_spills.0;
  let mut spills        = allocs_spills.1;

  // compute all the conflicts in our node's conflict entry that haven't been spilled
  let unspilled_conflicts : Vec<RegConflict> = 
    node_conflicts.into_iter()
                  .filter(|conflict| !spills.contains(&regconflict_id(conflict.clone())))
                  .collect();

  // compute all the allocated registers for our conflicts
  let conflict_registers  : Vec<Location> = 
    (&allocations).clone().into_iter()
                          .filter(|(id, _loc)| unspilled_conflicts.contains(&RegConflict::Var(id.clone())))
                          .map(|(_id, loc)| loc)
                          .collect();

  // Compute all the registers that we are allowed to use (the registers that aren't assigned 
  // to unspilled variable conflicts, and aren't part of our current own conflict list).
  let possible_registers : Vec<Location> = 
    registers.into_iter()
             .filter(|reg| !unspilled_conflicts.contains(&loc_as_regconflict(reg.clone())))
             .filter(|reg| !conflict_registers.contains(&&reg.clone()))
             .collect();

  if possible_registers.is_empty() {
    spills.push(regconflict_id(node_id));
  } else {
    allocations.insert(regconflict_id(node_id), possible_registers[0]);
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

fn select_highest_incident_node(nodes: &mut Vec<NodeIndex>, conflicts : &mut Graph<RegConflict, (), Undirected>) -> NodeIndex {
  let mut best_node : NodeIndex = nodes.pop().unwrap();
  let mut best_size : usize     = conflicts.neighbors(best_node).count();

  for node in nodes {
    let new_size = conflicts.neighbors(node.clone()).count();
    if new_size > best_size {
      best_size = new_size;
      best_node = *node;
    }
  }

  best_node
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

  use petgraph::Undirected;
  use petgraph::graph::Graph;
  use std::collections::HashMap;

  #[allow(dead_code)]
  fn calle(call : Triv, args : Vec<Location>) -> Exp { Exp::Call(call, args) }

  #[allow(dead_code)]
  fn ife(test : Pred, conseq : Exp, alt : Exp) -> Exp { Exp::If(test, mk_box!(conseq), mk_box!(alt)) }

  #[allow(dead_code)]
  fn begine(args : Vec<Effect>, base : Exp) -> Exp { Exp::Begin(args, mk_box!(base)) }

  #[allow(dead_code)]
  fn rop(op : Relop, t1 : Triv, t2 : Triv) -> Pred { Pred::Op(op, t1, t2) }

  #[allow(dead_code)]
  fn ifp(test : Pred, conseq : Pred, alt : Pred) -> Pred { Pred::If(mk_box!(test), mk_box!(conseq), mk_box!(alt)) }

  #[allow(dead_code)]
  fn beginp(args : Vec<Effect>, base : Pred) -> Pred { Pred::Begin(args, mk_box!(base)) }

  #[allow(dead_code)]
  fn setopf(t1 : Triv, op : Binop, arg1 : Triv, arg2 : Triv) -> Effect { Effect::SetOp(t1, (op, arg1, arg2)) }

  #[allow(dead_code)]
  fn setf(dest : Triv, src : Triv) -> Effect { Effect::Set(dest, src) }
  
  #[allow(dead_code)]
  fn nopf() -> Effect { Effect::Nop }
  
  #[allow(dead_code)]
  fn msetf(dest : Triv, src : Triv, offset : Triv) -> Effect { Effect::MSet(dest, src, offset) }
  
  #[allow(dead_code)]
  fn retf(lbl : Label,  frame_size : i64, body : Exp) -> Effect { Effect::ReturnPoint(lbl, body, frame_size) }
  
  #[allow(dead_code)]
  fn iff(test : Pred, conseq : Effect, alt : Effect) -> Effect { Effect::If(test, mk_box!(conseq), mk_box!(alt)) }
 
  #[allow(dead_code)]
  fn beginf(args : Vec<Effect>) -> Effect { Effect::Begin(mk_box!(args)) }
  
  #[allow(dead_code)]
  fn uv(name : Ident) -> Variable { Variable::UVar(name) }

  #[allow(dead_code)]
  fn vt(name : Ident) -> Triv { Triv::Var(Variable::UVar(name)) }
  
  #[allow(dead_code)]
  fn nt(val : i64) -> Triv { Triv::Num(val) }
  
  #[allow(dead_code)]
  fn lt(lbl : Label) -> Triv { Triv::Label(lbl) }
  
  #[allow(dead_code)]
  fn mreft(src : Triv, offset : Triv) -> Triv { Triv::MRef(mk_box!(src), mk_box!(offset)) }

  #[allow(dead_code)]
  fn fvar(n: i64) -> Triv { Triv::Var(Variable::Loc(index_fvar(n))) }

  #[allow(dead_code)]
  fn reg(s: &str) -> Triv { Triv::Var(Variable::Loc(Location::Reg(Ident::from_str(s)))) }
  
  #[allow(dead_code)]
  fn regl(s: &str) -> Location { Location::Reg(Ident::from_str(s)) }

  #[allow(dead_code)]
  fn mk_lbl(s : &str) -> Label { Label { label : Ident::from_str(s) } }

  fn mk_alloc_form(input_reg_conflicts : Graph<RegConflict, (), Undirected>) -> RegAllocInfo
  { RegAllocInfo
    { locals             : Vec::new()
    , unspillables       : Vec::new()
    , spills             : Vec::new()
    , call_lives         : Vec::new()
    , frame_conflicts    : Graph::new_undirected()
    , register_conflicts : input_reg_conflicts
    , new_frames         : Vec::new()
    }
  }

  pub fn test1() -> Program {

    let x0 = mk_uvar("x");
    let x1 = mk_uvar("x");
    let x2 = mk_uvar("x");
    let x3 = mk_uvar("x");
    let y4 = mk_uvar("y");

    let z6 = mk_uvar("z");

    let mut map = HashMap::new();
    map.insert(x0, regl("rbx"));
    map.insert(z6, Location::FrameVar(2));
    map.insert(x2, regl("r8"));
    map.insert(x3, regl("r9"));
    map.insert(y4, regl("r15"));

    let mut body_map = HashMap::new();
    body_map.insert(x2, regl("r8"));
    body_map.insert(x3, regl("r9"));

    let mut rc_b1 : Graph<RegConflict, (), Undirected> = Graph::new_undirected();
    let x0n  = rc_b1.add_node(var_to_reg_conflict(x0));
    let x1n  = rc_b1.add_node(var_to_reg_conflict(x1));
    let x2n  = rc_b1.add_node(var_to_reg_conflict(x2));
    let x3n  = rc_b1.add_node(var_to_reg_conflict(x3));
    let nrax = rc_b1.add_node(reg_to_conflict(regl("rax")));
    let nrbp = rc_b1.add_node(reg_to_conflict(regl("rbp")));
    let nr10 = rc_b1.add_node(reg_to_conflict(regl("r10")));
    let nr11 = rc_b1.add_node(reg_to_conflict(regl("r11")));
    let nr12 = rc_b1.add_node(reg_to_conflict(regl("r12")));
    let nr9  = rc_b1.add_node(reg_to_conflict(regl("r9")));

    rc_b1.add_edge(x0n, x1n, ());
    rc_b1.add_edge(x0n, x2n, ());
    rc_b1.add_edge(x0n, nrax, ());
    rc_b1.add_edge(x1n, x0n, ());
    rc_b1.add_edge(x1n, nr12, ());
    rc_b1.add_edge(x1n, nrbp, ());
    rc_b1.add_edge(x2n, x0n, ());
    rc_b1.add_edge(x2n, nr10, ());
    rc_b1.add_edge(x2n, nr9, ());
    rc_b1.add_edge(x3n, nr11, ());
    rc_b1.add_edge(x3n, nr10, ());
    rc_b1.add_edge(x3n, nr9, ());

    println!("Graph: {:?}", rc_b1);

    let binding1_alloc = mk_alloc_form(rc_b1);

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
