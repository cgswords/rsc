// PASS    | assign_frame_variables
// ---------------------------------------------------------------------------
// USAGE   | assign_frame_variables : alloc_lang::Program -> 
//         |                          alloc_lang::Program
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
use util::frame_index;
use util::index_fvar;

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
use alloc_lang::FrameConflict;

use std::collections::HashMap;
use std::cmp::max;
use petgraph::graph::Graph;
use petgraph::Undirected;

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
//  , pub new_frames         : Vec<Vec<Ident>>
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
pub fn assign_frame_variables(input : Program) -> Program {
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
      let mut new_frame_locs = assign_frame_vars(&locs, &alloc_info.frame_conflicts, &alloc_info.spills);

      for (k,v) in new_frame_locs.into_iter() {
        locs.insert(k,v);
      }
      
      alloc_info.spills.clear();
      Body { alloc : RegAllocForm::Unallocated(alloc_info, locs)
           , expression : input.expression }
    }
  }
}

// ---------------------------------------------------------------------------

fn assign_frame_vars( cur_locs  : &HashMap<Ident, Location>
                    , conflicts : &Graph<FrameConflict, (), Undirected>
                    , spills    : &Vec<Ident>) ->
                    HashMap<Ident, Location> 
{
    let mut next_frame_index = max_frame_index(cur_locs, conflicts) + 1;
    let mut result = HashMap::new();

    for spill in spills {
      result.insert(spill.clone(), index_fvar(next_frame_index));
      next_frame_index += 1;
    }
     
    result
}

fn conflict_frame_index(input: &FrameConflict) -> i64 {
  match input 
  { FrameConflict::Var(_)     => -1
  , FrameConflict::FrameVar(i) => i.clone()
  }
}

fn max_frame_index(locs : &HashMap<Ident, Location>, conflicts : &Graph<FrameConflict, (), Undirected>) -> i64 {
  let location_max = locs.values().cloned().fold(0, |acc, x| max(acc, frame_index(x)));

  let conflict_max = conflicts.node_indices()
                              .map(|n| conflicts.node_weight(n).unwrap().clone())
                              .fold(0, |cur_max, conflict| max(cur_max, conflict_frame_index(&conflict)));

  max(conflict_max, location_max)
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
  use alloc_lang::FrameConflict;
  use alloc_lang::fvar_to_conflict;
  use alloc_lang::var_to_frame_conflict;

  use petgraph::graph::Graph;
  use petgraph::Undirected;
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

  fn mk_conflict(n : i64) -> FrameConflict { fvar_to_conflict(index_fvar(n)) }

  fn mk_spills_form(input_spills : Vec<Ident>, input_frame_conflicts : Graph<FrameConflict, (), Undirected>) -> RegAllocInfo
  { RegAllocInfo
    { locals             : Vec::new()
    , unspillables       : Vec::new()
    , spills             : input_spills
    , call_lives         : Vec::new()
    , frame_conflicts    : input_frame_conflicts
    , register_conflicts : Graph::new_undirected()
    , new_frames         : Vec::new()
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

    let fc0 = mk_conflict(0);
    let fc1 = mk_conflict(1);
    let fc2 = mk_conflict(2);
    let fc3 = mk_conflict(3);

    let mut cg_b1 : Graph<FrameConflict, (), Undirected> = Graph::new_undirected();
    let z5n = cg_b1.add_node(var_to_frame_conflict(z5));
    let z6n = cg_b1.add_node(var_to_frame_conflict(z6));
    let z7n = cg_b1.add_node(var_to_frame_conflict(z7));
    let z8n = cg_b1.add_node(var_to_frame_conflict(z8));
    let f0n = cg_b1.add_node(fc0);
    let f1n = cg_b1.add_node(fc1);
    let f2n = cg_b1.add_node(fc2);
    let f3n = cg_b1.add_node(fc3);

    cg_b1.add_edge(z5n, z6n, ());
    cg_b1.add_edge(z5n, z7n, ());
    cg_b1.add_edge(z5n, f0n, ());
    cg_b1.add_edge(z6n, z5n, ());
    cg_b1.add_edge(z6n, f1n, ());
    cg_b1.add_edge(z6n, f2n, ());
    cg_b1.add_edge(z7n, z5n, ());
    cg_b1.add_edge(z7n, z6n, ());
    cg_b1.add_edge(z7n, f3n, ());
    cg_b1.add_edge(z8n, f3n, ());
    cg_b1.add_edge(z8n, f2n, ());
    cg_b1.add_edge(z8n, f0n, ());

    let binding1_alloc = mk_spills_form(vec![z9, z10, z11, z12], cg_b1);

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
