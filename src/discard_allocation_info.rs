// PASS    | discard_allocation_info
// ---------------------------------------------------------------------------
// USAGE   | discard_allocation-info : discard_allocation_info::Program -> 
//         |                           discard_call_live::Program
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

use std::collections::HashMap;

use alloc_lang::RegAllocForm;

use discard_call_lives::Program  as DCLProgram;
use discard_call_lives::Letrec   as DCLLetrec;
use discard_call_lives::Exp      as DCLExp;
use discard_call_lives::Effect   as DCLEffect;
use discard_call_lives::Pred     as DCLPred;
use discard_call_lives::Triv     as DCLTriv;
use discard_call_lives::Offset   as DCLOffset;
use discard_call_lives::Var      as DCLVar;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum Program { Letrec(Vec<Letrec>, RegAllocForm, Exp) }
                                       // ^ Stores allocation info for the body 

#[derive(Debug)]
pub enum Letrec 
	{ Entry(RegAllocForm, Exp) }

#[derive(Debug)]
pub enum Exp 
  { Call(Triv, Vec<Location>)
  , If(Pred,Box<Exp>,Box<Exp>)
  , Begin(Vec<Effect>,Box<Exp>)
  }

#[derive(Debug)]
pub enum Pred
  { True
  , False
  , Op(Relop,Triv,Triv)
  , If(Box<Pred>,Box<Pred>,Box<Pred>)
  , Begin(Vec<Effect>, Box<Pred>)
  }

#[derive(Debug)]
pub enum Effect
  { SetOp(Variable, (Binop, Triv, Triv))
  , Set(Variable, Triv)
  , Nop
  , MSet(Variable, Offset, Triv) // MSet takes a variable, an offset, and a triv; 
                                 // Variable and Offset MUST be registers, not frame vars
  , ReturnPoint(Label, Exp, i64) // Label, Expression for return point, frame size for call
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>, Box<Effect>)
  }

#[derive(Debug)]
pub enum Variable 
  { Loc(Location)
  , UVar(UniqueVar)
  }

#[derive(Debug)]
pub enum Triv 
  { Var(Variable)
  , Num(i64) 
  , Label(Label)
  , MRef(Variable, Offset)
  }

#[derive(Debug)]
pub enum Offset
  { UVar(UniqueVar)
  , Reg(String)
  , Num(i64)
  }

// ---------------------------------------------------------------------------
// OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// #[derive(Debug)]
// pub enum Program { Letrec(Vec<Letrec>, HashMap<UniqueVar, Location>, Exp) }
//                                        // ^ Stores the var locs for the body 
// 
// #[derive(Debug)]
// pub enum Letrec { Entry(Label, HashMap<UniqueVar, Location>, Exp) }
//                                // ^ Stores the var locs for the RHS 
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
//   , Num(i64)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn discard_allocation_info(input : Program) -> DCLProgram {
  return match input 
  { Program::Letrec(letrecs, alloc_info, body) =>  
      DCLProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , alloc_to_locmap(alloc_info)
                        , exp(body))
  }  
}


fn letrec_entry(input : Letrec) -> DCLLetrec {
  return match input 
  { Letrec::Entry(lbl, alloc_info, rhs) => DCLLetrec::Entry(lbl, alloc_to_locmap(alloc_info), exp(rhs)) }
} 

fn alloc_to_locmap(input : RegAllocForm) -> HashMap<UniqueVar, Location> {
  match input
	{ RegAllocForm::Allocated(map)  => map
  , RegAllocForm::Unallocated(..) => panic!("Got past register allocation with an unallocated block.");
  }
}

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp, Location>) -> DCLExp {
  return match input 
  { Exp::Call(t, call_lives)   => DCLExp::Call(triv(t))
  , Exp::If(test, conseq, alt) => DCLExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => DCLExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> DCLPred {
  return match input 
  { Pred::True                  => DCLPred::True
  , Pred::False                 => DCLPred::False
  , Pred::Op(op,t1,t2)          => DCLPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => DCLPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => DCLPred::Begin( effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn effect(input: Effect, map: &HashMap<UniqueVar, Location>) -> DCLEffect {
  return match input 
  { Effect::SetOp(l, (op, t1, t2))      => DCLEffect::SetOp(var(l), (op, triv(t1), triv(t2)))
  , Effect::Set(l, t)                   => DCLEffect::Set(var(l), triv(t))
  , Effect::Nop                         => DCLEffect::Nop
  , Effect::MSet(base, off, val)        => DCLEffect::MSet(var(base), offset(off), triv(val)) 
  , Effect::ReturnPoint(lbl, body, off) => DCLEffect::ReturnPoint(lbl, exp(body), off)
  , Effect::If(test, conseq, alt)       => DCLEffect::If(pred(test), mk_box!(effect(*conseq)) , mk_box!(effect(*alt)))
  , Effect::Begin(effs, body)           => DCLEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e)).collect())
                                                           , mk_box!(effect(*body)))
  }
}

fn loc(input : Location) -> Loc {
  return match input
  { Location::Reg(reg)    => DCLLoc::Reg(reg)
  , Location::FrameVar(n) => DCLLoc::FrameVar(n)
  }
}

fn var(input : Variable) -> DCLVar {
  return match input
  { Variable::Loc(l)   => loc(l)
  , Variable::UVar(uv) => DCLVar::UVar(uv)
  }
}

fn triv(input : Triv) -> DCLTriv {
  return match input
  { Triv::Var(v)          => DCLTriv::Loc(var(v, map))
  , Triv::Num(n)          => DCLTriv::Num(n)
  , Triv::Label(l)        => DCLTriv::Label(l)
  , Triv::MRef(base, off) => Triv::MRef(var(base), offset(off))
  } 
}

fn offset(input: Offset) -> DCLOffset {
  return match input
  { Offset::UVar(uv) => DCLOffset::UVar(uv)
  , Offset::Num(n)   => DCLOffset::Num(n)
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
