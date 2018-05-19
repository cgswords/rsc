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

use util::Binop;
use util::Relop;
use util::Label;
use util::UniqueVar;
use util::Location;
use util::mk_uvar;

use alloc_lang::Program;
use alloc_lang::Letrec;
use alloc_lang::RegAllocForm;
use alloc_lang::RegAllocInfo;
use alloc_lang::Exp;
use alloc_lang::Pred;
use alloc_lang::Effect;
use alloc_lang::Variable;
use alloc_lang::Triv;
use alloc_lang::Offset;

use std::collections::HashMap;
use std::collections::HashSet;

// ---------------------------------------------------------------------------
// INPUT / OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// 
// #[derive(Debug)]
// pub enum Program { Letrec(Vec<Letrec>, RegAllocForm, Exp) }
//                                        // ^ Stores allocation info for the body 
// 
// #[derive(Debug)]
// pub enum Letrec 
// 	{ Entry(RegAllocForm, Exp) }
// 
// pub enum RegAllocForm
// 	{ Allocated(HashMap<UniqueVar, Location>, Exp)
//  , Unallocated(RegAllocInfo, HashMap<UniqueVar, Location>, Exp)
//  }
// 
// pub struct RegAllocInfo
//   { locals            : mut Vec<UniqueVar>
//   , unspillables      : mut Vec<UniqueVar>
//   , spills            : mut Vec<UniqueVar>
//   , frame_conflits    : mut Vec<(UniqueVar, mut Vec<UniqueVar>)>
//   , register_conflits : mut Vec<(UniqueVar, mut Vec<UniqueVar>)>
//   }
// 
// #[derive(Debug)]
// pub enum Exp 
//   { Call(Triv, Vec<Location>)
//   , If(Pred,Box<Exp>,Box<Exp>)
//   , Begin(Vec<Effect>,Box<Exp>)
//   }
// 
// #[derive(Debug)]
// pub enum Pred
//   { True
//   , False
//   , Op(Relop,Triv,Triv)
//   , If(Box<Pred>,Box<Pred>,Box<Pred>)
//   , Begin(Vec<Effect>, Box<Pred>)
//   }
// 
// #[derive(Debug)]
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
// #[derive(Debug)]
// pub enum Variable 
//   { Loc(Location)
//   , UVar(UniqueVar)
//   }
// 
// #[derive(Debug)]
// pub enum Triv 
//   { Var(Variable)
//   , Num(i64) 
//   , Label(Label)
//   , MRef(Triv, Triv)
//   }
// 
// #[derive(Debug)]
// pub enum Offset
//   { UVar(UniqueVar)
//   , Num(i64)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn assign_frame(input : Program) -> Program {
  return match input 
  { Program::Letrec(letrecs, alloc_info, body) =>  
      Program::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                     , alloc_info
                     , exp(body))
  }  
}

fn letrec_entry(input : Letrec) -> Letrec {
  return match input 
  { Letrec::Entry(lbl, alloc_info, rhs) => Letrec::Entry(lbl, alloc_info, exp(rhs)) }
} 

fn get_frame_index(input: &Location) -> i64 {
  match input
  { Location::Reg(_)      => 0
  , Location::FrameVar(n) => n
  }
}

fn conflict_union(conflicts : &Vec<(UniqueVar, Vec<UniqueVar>)) -> Vec<UniqueVar>
{
  let mut vars : HashSet
  // FIXME Implement this, and move it into alloc_lang probably
  return Vec::new();
  
}

fn assign_frame_vars( cur_locs  : mut HashMap<UniqueVar, Location>
                    , conflicts : &Vec<(UniqueVar, Vec<UniqueVar>)
                    , spills    : &Vec<UniqueVar>) ->
                    mut HashMap<UniqueVar, location> 
{
    // HASH SETS!
    let used_fvars = conflict_union(conflits);                  
                          
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

fn mk_num_lit(n: i64) -> Triv {
  return Triv::Num(n);
}

fn mk_fv_triv(n: i64) -> Triv {
  return mk_loc_triv(Location::FrameVar(n));
}

fn mk_reg(s: &str) -> Variable {
  return Variable::Loc(mk_loc_reg(s));
}

fn mk_loc_reg(s: &str) -> Location {
  return Location::Reg(s.to_string());
}

fn mk_call(s: &str) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)));
}

fn mk_lbl(s : &str) -> Label {
  return Label::Label(s.to_string());
}

fn mk_set_op(dest: Variable, op: Binop, t1 : Triv, t2: Triv) -> Effect {
  return Effect::SetOp(dest, (op, t1, t2));
}

fn mk_mset(dest: Variable, offset: Offset, val : Triv) -> Effect {
  return Effect::MSet(dest, offset, val);
}

fn mk_loc_triv(l : Location) -> Triv {
  return as_var_triv(loc_as_var(l));
}

fn mk_var(s : &str, index : i64) -> Variable {
  return Variable::UVar(UniqueVar { name : s.to_string(), id : index });
}

fn mk_var_triv(s : &str, index : i64) -> Triv {
  return as_var_triv(mk_var(s, index));
}

fn as_var_triv(v: Variable) -> Triv {
  return Triv::Var(v);
}

fn loc_as_var(l: Location) -> Variable {
  return Variable::Loc(l);
}

fn mk_set(dest: Variable, val: Triv) -> Effect {
  return Effect::Set(dest,val)
}

pub fn test1() -> Program {
  let mut map = HashMap::new();
  map.insert(mk_uvar("x",0), mk_loc_reg("rbx"));
  map.insert(mk_uvar("x",1), Location::FrameVar(2));
  map.insert(mk_uvar("x",2), mk_loc_reg("r8"));
  map.insert(mk_uvar("x",3), mk_loc_reg("r9"));
  map.insert(mk_uvar("y",4), mk_loc_reg("r15"));

  let mut body_map = HashMap::new();
  body_map.insert(mk_uvar("x",2), mk_loc_reg("r8"));
  body_map.insert(mk_uvar("x",3), mk_loc_reg("r9"));

  return Program::Letrec(
           vec![ Letrec::Entry(mk_lbl("X1")
                              , map 
                              , Exp::If(Pred::Op(Relop::LT, mk_var_triv("x",2), mk_var_triv("x",3)),
                                        Box::new(
                                          Exp::Begin(
                                            vec![ mk_set_op(mk_var("x", 1), Binop::Plus, mk_var_triv("x",1), mk_num_lit(35))
                                                , mk_mset(mk_var("x",0), Offset::Num(10), mk_num_lit(40))
                                                , mk_mset(mk_var("x",0), Offset::UVar(mk_uvar("y", 4)), mk_num_lit(25))
                                                , Effect::ReturnPoint(mk_lbl("foo"), 
                                                    Exp::Begin(
                                                       vec![ mk_set(mk_reg("rax"), mk_fv_triv(1)) ]
                                                      , mk_box!(mk_call("X1")))
                                                    , 16)
                                                , mk_set(mk_var("x",0), Triv::MRef(mk_reg("rax"),Offset::Num(10)))]
                                           , Box::new(mk_call("void"))))
                                       , Box::new(
                                           Exp::Begin(
                                             vec![mk_set_op(mk_reg("rax"), Binop::Plus, as_var_triv(mk_reg("rax")), mk_num_lit(10))]
                                            , Box::new(mk_call("void")))))
                              )
               ]
         , body_map
         , Exp::Begin(
            vec![ mk_set(mk_var("x",2), mk_num_lit(0))
                , mk_set(mk_var("x",3), mk_num_lit(1))
                ]
            , Box::new(mk_call("X1"))));
}
