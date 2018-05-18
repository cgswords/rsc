// PASS    | finalize_instruction_selection
// ---------------------------------------------------------------------------
// USAGE   | finalize_instruction_selection : reg_alloc::Program -> 
//         |                                  discard_allocation_info::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with the allocation information removed, leaving
//         | the variable-location HashMaps in its place.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass walks through the very top level of the expressions, discarding 
// the relevant forms.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::UniqueVar;
use util::Location;
use util::mk_uvar;

use alloc_lang::Program;
use alloc_lang::Letrec;
use alloc_lang::Exp;
use alloc_lang::Pred;
use alloc_lang::Effect;
use alloc_lang::Variable;
use alloc_lang::Triv;
use alloc_lang::Offset;

use std::collections::HashMap;

use discard_alloc_info::Program  as DAIProgram;
use discard_alloc_info::Letrec   as DAILetrec;
use discard_alloc_info::Exp      as DAIExp;
use discard_alloc_info::Effect   as DAIEffect;
use discard_alloc_info::Pred     as DAIPred;
use discard_alloc_info::Triv     as DAITriv;
use discard_alloc_info::Offset   as DAIOffset;
use discard_alloc_info::Var      as DAIVar;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------

// INPUT LANG is the register `alloc_lang`

// ---------------------------------------------------------------------------
// OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// #[derive(Debug)]
// pub enum Program { Letrec(Vec<Letrec>, RegAllocForm, Exp) }
//                                        // ^ Stores allocation info for the body 
// 
// #[derive(Debug)]
// pub enum Letrec 
// 	{ Entry(RegAllocForm, Exp) }
// 
// pub enum RegAllocForm
// 	{ Allocated(HashMap<UniqueVar, Location>)
//   , Unallocated(AllocInfo, HashMap<UniqueVar, Location>)
//   }
// 
// pub struct RegAllocInfo 
//   { locals : Vec<UniqueVar>
//   , unspillables : Vec<UniqueVar>
//   , spills : Vec<UniqueVar>
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
//   { SetOp(Variable, (Binop, Triv, Triv))
//   , Set(Variable, Triv)
//   , Nop
//   , MSet(Variable, Offset, Triv) // MSet takes a variable, an offset, and a triv; 
//                                  // Variable and Offset MUST be registers, not frame vars
//   , ReturnPoint(Label, Exp, i64) // Label, Expression for return point, frame size for call
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
//   , MRef(Variable, Offset)
//   }
// 
// #[derive(Debug)]
// pub enum Offset
//   { UVar(UniqueVar)
//   , Reg(String)
//   , Num(i64)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn finalize_instruction_selection(input : Program) -> DAIProgram {
  return match input 
  { Program::Letrec(letrecs, alloc_info, body) =>  
      DAIProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , alloc_info
                        , exp(body))
  }  
}


fn letrec_entry(input : Letrec) -> DAILetrec {
  return match input 
  { Letrec::Entry(lbl, alloc_info, rhs) => DAILetrec::Entry(lbl, alloc_info, exp(rhs)) }
} 

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp, Location>) -> DAIExp {
  return match input 
  { Exp::Call(t, call_lives)   => DAIExp::Call(triv(t))
  , Exp::If(test, conseq, alt) => DAIExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => DAIExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> DAIPred {
  return match input 
  { Pred::True                  => DAIPred::True
  , Pred::False                 => DAIPred::False
  , Pred::Op(op,t1,t2)          => DAIPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => DAIPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => DAIPred::Begin( effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn effect(input: Effect, map: &HashMap<UniqueVar, Location>) -> DAIEffect {
  return match input 
  { Effect::SetOp(dest, (op, t1, t2))   => DAIEffect::SetOp(triv_to_var(dest), (op, triv(t1), triv(t2)))
  , Effect::Set(dest, src)              => DAIEffect::Set(triv_to_var(dest), triv(src))
  , Effect::Nop                         => DAIEffect::Nop
  , Effect::MSet(base, off, val)        => DAIEffect::MSet(triv_to_var(base), triv_to_offset(off), triv(val)) 
  , Effect::ReturnPoint(lbl, body, off) => DAIEffect::ReturnPoint(lbl, exp(body), off)
  , Effect::If(test, conseq, alt)       => DAIEffect::If(pred(test), mk_box!(effect(*conseq)) , mk_box!(effect(*alt)))
  , Effect::Begin(effs, body)           => DAIEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e)).collect())
                                                           , mk_box!(effect(*body)))
  }
}

fn triv_to_var(input : Triv) -> DAIVariable {
  return match input
  { Triv::Var(v) => var(v)
    _            => panic!("Instruction selection has left a non-var triv in a var-only place!");
  }
}

fn triv_to_offset(input : Triv) -> DAIVariable {
  return match input
  { Triv::Var(Variable::Uvar(uv))              => DAIOffset::UVar(uv)
  , Triv::Var(Variable::Loc(Location::Reg(s))) => DAIOffset::Reg(s)
  , Triv::Num(n)                               => DAIOffset::Num(n)
    _                                          => panic!("Instruction selection has left a non-offset triv in an offset-only place!");
  }
}

fn loc(input : Location) -> Loc {
  return match input
  { Location::Reg(reg)    => DAILoc::Reg(reg)
  , Location::FrameVar(n) => DAILoc::FrameVar(n)
  }
}

fn var(input : Variable) -> DAIVar {
  return match input
  { Variable::Loc(l)   => loc(l)
  , Variable::UVar(uv) => DAIVar::UVar(uv)
  }
}

fn triv(input : Triv) -> DAITriv {
  return match input
  { Triv::Var(v)          => DAITriv::Loc(var(v))
  , Triv::Num(n)          => DAITriv::Num(n)
  , Triv::Label(l)        => DAITriv::Label(l)
  , Triv::MRef(base, off) => Triv::MRef(triv_to_var(base), triv_to_offset(off))
  } 
}

fn offset(input: Offset) -> DAIOffset {
  return match input
  { Offset::UVar(uv) => DAIOffset::UVar(uv)
  , Offset::Num(n)   => DAIOffset::Num(n)
  }
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
