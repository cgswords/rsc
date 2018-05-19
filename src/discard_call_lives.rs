// PASS    | discard_call_lives
// ---------------------------------------------------------------------------
// USAGE   | discard_call_life : discard_call_live::Program ->
//         |                     finalize_location::Program
// ---------------------------------------------------------------------------
// RETURNS | A program without any call-live variables, removing the lists.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass discards the call-live information for each procedure invocation,
// leaving them as Call forms to trivials without additional information.
//
// We do the obvious walk, dropping the information.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::UniqueVar;
use util::Location;
use util::mk_uvar;
use util::Ident;

use std::collections::HashMap;

use finalize_locations::Program  as FLProgram;
use finalize_locations::Letrec   as FLLetrec;
use finalize_locations::Exp      as FLExp;
use finalize_locations::Effect   as FLEffect;
use finalize_locations::Pred     as FLPred;
use finalize_locations::Triv     as FLTriv;
use finalize_locations::Offset   as FLOffset;
use finalize_locations::Variable as FLVar;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum Program { Letrec(Vec<Letrec>, HashMap<UniqueVar, Location>, Exp) }
                                       // ^ Stores the var locs for the body 

#[derive(Debug)]
pub enum Letrec { Entry(Label, HashMap<UniqueVar, Location>, Exp) }
                               // ^ Stores the var locs for the RHS 

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
  , Reg(Ident)
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
//   , Reg(Ident)
//   , Num(i64)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn discard_call_lives(input : Program) -> FLProgram {
  return match input 
  { Program::Letrec(letrecs, map, body) =>  
      FLProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , map
                        , exp(body))
  }  
}

fn letrec_entry(input : Letrec) -> FLLetrec {
  return match input 
  { Letrec::Entry(lbl, map, rhs) => FLLetrec::Entry(lbl, map, exp(rhs)) }
} 

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp) -> FLExp {
  return match input 
  { Exp::Call(t, call_lives)  => FLExp::Call(triv(t))
  , Exp::If(test, conseq, alt) => FLExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => FLExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> FLPred {
  return match input 
  { Pred::True                  => FLPred::True
  , Pred::False                 => FLPred::False
  , Pred::Op(op,t1,t2)          => FLPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => FLPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => FLPred::Begin( effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn effect(input: Effect) -> FLEffect {
  return match input 
  { Effect::SetOp(l, (op, t1, t2))      => FLEffect::SetOp(var(l), (op, triv(t1), triv(t2)))
  , Effect::Set(l, t)                   => FLEffect::Set(var(l), triv(t))
  , Effect::Nop                         => FLEffect::Nop
  , Effect::MSet(base, off, val)        => FLEffect::MSet(var(base), offset(off), triv(val)) 
  , Effect::ReturnPoint(lbl, body, off) => FLEffect::ReturnPoint(lbl, exp(body), off)
  , Effect::If(test, conseq, alt)       => FLEffect::If(pred(test), mk_box!(effect(*conseq)) , mk_box!(effect(*alt)))
  , Effect::Begin(effs, body)           => FLEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e)).collect())
                                                           , mk_box!(effect(*body)))
  }
}

fn loc(input : Location) -> Location {
  return input;
}

fn var(input : Variable) -> FLVar {
  return match input
  { Variable::Loc(l)   => FLVar::Loc(loc(l))
  , Variable::UVar(uv) => FLVar::UVar(uv)
  }
}

fn triv(input : Triv) -> FLTriv {
  return match input
  { Triv::Var(v)          => FLTriv::Var(var(v))
  , Triv::Num(n)          => FLTriv::Num(n)
  , Triv::Label(l)        => FLTriv::Label(l)
  , Triv::MRef(base, off) => FLTriv::MRef(var(base), offset(off))
  } 
}

fn offset(input: Offset) -> FLOffset {
  return match input
  { Offset::UVar(uv) => FLOffset::UVar(uv)
  , Offset::Reg(r)   => FLOffset::Reg(r)
  , Offset::Num(n)   => FLOffset::Num(n)
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
  return Location::Reg(Ident::from_str(s));
}

fn mk_call(s: &str, lives: Vec<Location>) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)), lives);
}

fn mk_lbl(s : &str) -> Label {
  return Label::new(Ident::from_str(s));
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
  return Variable::UVar(UniqueVar { name : Ident::from_str(s), id : index });
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
                                                      , mk_box!(mk_call("X1", Vec::new())))
                                                    , 16)
                                                , mk_set(mk_var("x",0), Triv::MRef(mk_reg("rax"),Offset::Num(10)))]
                                           , Box::new(mk_call("void", vec![mk_loc_reg("rax")]))))
                                       , Box::new(
                                           Exp::Begin(
                                             vec![mk_set_op(mk_reg("rax"), Binop::Plus, as_var_triv(mk_reg("rax")), mk_num_lit(10))]
                                            , Box::new(mk_call("void", vec![mk_loc_reg("rax"), mk_loc_reg("rbp")])))))
                              )
               ]
         , body_map
         , Exp::Begin(
            vec![ mk_set(mk_var("x",2), mk_num_lit(0))
                , mk_set(mk_var("x",3), mk_num_lit(1))
                ]
            , Box::new(mk_call("X1", vec![mk_loc_reg("rax"), mk_loc_reg("rbp")]))));
}
