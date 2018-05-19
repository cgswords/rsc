// PASS    | finalize_locations
// ---------------------------------------------------------------------------
// USAGE   | Converts every variable in the code to a location
// ---------------------------------------------------------------------------
// RETURNS | A program without unqiue variables, now using registers and frame 
//         | vars
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass discards the location information, using it to replace variables
// with their (newly assocaited) register and frame locations.
// 
// We just scoop up the location forms and do the obvious walk, swapping things
// out as we see them.
//
// TODO
// We should also take this moment to crush any useless assignments
// post-allocation, such as `(set! rax rax)`, by converting them into `nop`
// instructions. That is a separate pass, though.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::Ident;
use util::Location;
use util::mk_uvar;

use std::collections::HashMap;

use expose_frame_variables::Program  as EFVProgram;
use expose_frame_variables::Letrec   as EFVLetrec;
use expose_frame_variables::Exp      as EFVExp;
use expose_frame_variables::Effect   as EFVEffect;
use expose_frame_variables::Pred     as EFVPred;
use expose_frame_variables::Triv     as EFVTriv;
use expose_frame_variables::Offset   as EFVOffset;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub enum Program { Letrec(Vec<Letrec>, HashMap<Ident, Location>, Exp) }
                                       // ^ Stores the var locs for the body 

#[derive(Debug)]
pub enum Letrec { Entry(Label, HashMap<Ident, Location>, Exp) }
                               // ^ Stores the var locs for the RHS 

#[derive(Debug)]
pub enum Exp 
  { Call(Triv)
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
  , UVar(Ident)
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
  { UVar(Ident)
  , Reg(Ident)
  , Num(i64)
  }

// ---------------------------------------------------------------------------
// OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// pub enum Program { Letrec(Vec<Letrec>, Exp) }
// 
// pub enum Letrec { Entry(Label,Exp) }
// 
// pub enum Exp 
//   { Call(Triv)
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
//   { SetOp(Location, (Binop, Triv, Triv))
//   , Set(Location, Triv)
//   , Nop
//   , MSet(String, Offset, Triv) // MSet takes a register, an offset, and a triv 
//   , ReturnPoint(Label, Exp, i64) // Label, Expression for return point, frame size for call
//   , If(Pred, Box<Effect>, Box<Effect>)
//   , Begin(Box<Vec<Effect>>, Box<Effect>)
//   }
// 
// pub enum Triv 
//   { Loc(Location) 
//   , Num(i64) 
//   , Label(Label)
//   , MRef(String, Offset) // Memory reference of a register and an offset
//   }
// 
// pub enum Offset
//   { Reg(String)
//   , Num(i64)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn finalize_locations(input : Program) -> EFVProgram {
  return match input 
  { Program::Letrec(letrecs, map, body) =>  
      EFVProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , exp(body, &map))
  }  
}

fn letrec_entry(input : Letrec) -> EFVLetrec {
  return match input 
  { Letrec::Entry(lbl,map, rhs) => EFVLetrec::Entry(lbl, exp(rhs, &map)) }
} 

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp, map: &HashMap<Ident, Location>) -> EFVExp {
  return match input 
  { Exp::Call(t)               => EFVExp::Call(triv(t, map))
  , Exp::If(test, conseq, alt) => EFVExp::If( pred(test,           map)
                                            , mk_box!(exp(*conseq, map))
                                            , mk_box!(exp(*alt,    map)))
  , Exp::Begin(effs, body)     => EFVExp::Begin( effs.into_iter().map(|e| effect(e, map)).collect()
                                               , mk_box!(exp(*body, map)))
  }
}

fn pred(input : Pred, map: &HashMap<Ident, Location>) -> EFVPred {
  return match input 
  { Pred::True                  => EFVPred::True
  , Pred::False                 => EFVPred::False
  , Pred::Op(op,t1,t2)          => EFVPred::Op(op, triv(t1, map), triv(t2, map))
  , Pred::If(test, conseq, alt) => EFVPred::If(mk_box!(pred(*test,   map)),
                                               mk_box!(pred(*conseq, map)),
                                               mk_box!(pred(*alt,    map)))
  , Pred::Begin(effs, body)     => EFVPred::Begin( effs.into_iter().map(|e| effect(e, map)).collect()
                                                 , mk_box!(pred(*body, map)))
  }
}

fn effect(input: Effect, map: &HashMap<Ident, Location>) -> EFVEffect {
  return match input 
  { Effect::SetOp(l, (op, t1, t2))      => EFVEffect::SetOp(var(l, map), (op, triv(t1, map), triv(t2, map)))
  , Effect::Set(l, t)                   => EFVEffect::Set(var(l, map), triv(t, map))
  , Effect::Nop                         => EFVEffect::Nop
  , Effect::MSet(base, off, val)        => 
    { let new_base = var(base, map);
      if let Location::Reg(s) = new_base {
        EFVEffect::MSet(s, offset(off, map), triv(val, map))
      } else {
        panic!("Tried to place an ref base on the stack.");
      }
    }
  , Effect::ReturnPoint(lbl, body, off) => EFVEffect::ReturnPoint(lbl, exp(body, map), off)
  , Effect::If(test, conseq, alt)       => EFVEffect::If( pred(test, map)
                                                        , mk_box!(effect(*conseq, map))
                                                        , mk_box!(effect(*alt, map)))
  , Effect::Begin(effs, body)           => EFVEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e, map)).collect())
                                                           , mk_box!(effect(*body, map)))
  }
}

fn loc(input : Location) -> Location {
  return input;
}

fn uvar(uvar: Ident, map: &HashMap<Ident, Location>) -> Location {
  if let Some(location) = map.get(&uvar) {
    let thisLoc : Location = location.clone();
    loc(thisLoc)
  } else {
    panic!("Failed to find location for uvar: {:?}", uvar);
  } 
}

fn var(input : Variable, map: &HashMap<Ident, Location>) -> Location {
  return match input
  { Variable::Loc(l)   => loc(l)
  , Variable::UVar(uv) => uvar(uv, map) 
  }
}

fn triv(input : Triv, map: &HashMap<Ident, Location>) -> EFVTriv {
  return match input
  { Triv::Var(v)          => EFVTriv::Loc(var(v, map))
  , Triv::Num(n)          => EFVTriv::Num(n)
  , Triv::Label(l)        => EFVTriv::Label(l)
  , Triv::MRef(base, off) => 
    { let new_base = var(base, map);
      if let Location::Reg(s) = new_base {
        EFVTriv::MRef(s, offset(off, map))
      } else {
        panic!("Tried to place an ref base on the stack.")
      }
    }
  } 
}

fn offset(input: Offset, map: &HashMap<Ident, Location>) -> EFVOffset {
  return match input
  { Offset::UVar(uv) => if let Location::Reg(s) = uvar(uv, map) {
                          EFVOffset::Reg(s)
                        } else {
                          panic!("Tried to place an offset variable on the stack.")
                        }
  , Offset::Reg(s)   => EFVOffset::Reg(s)
  , Offset::Num(n)   => EFVOffset::Num(n)
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

fn mk_call(s: &str) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)));
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

fn mk_var(id: Ident) -> Variable {
  return Variable::UVar(id);
}

fn mk_var_triv(id: Ident) -> Triv {
  return as_var_triv(mk_var(id));
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
  let x0 = mk_uvar("x");
  let x1 = mk_uvar("x");
  let x2 = mk_uvar("x");
  let x3 = mk_uvar("x");
  let y4 = mk_uvar("y");

  let mut map = HashMap::new();
  map.insert(x0, mk_loc_reg("rbx"));
  map.insert(x1, Location::FrameVar(2));
  map.insert(x2, mk_loc_reg("r8"));
  map.insert(x3, mk_loc_reg("r9"));
  map.insert(y4, mk_loc_reg("r15"));

  let mut body_map = HashMap::new();
  body_map.insert(x2, mk_loc_reg("r8"));
  body_map.insert(x3, mk_loc_reg("r9"));

  return Program::Letrec(
           vec![ Letrec::Entry(mk_lbl("X1")
                              , map 
                              , Exp::If(Pred::Op(Relop::LT, mk_var_triv(x2), mk_var_triv(x3)),
                                        Box::new(
                                          Exp::Begin(
                                            vec![ mk_set_op(mk_var(x1), Binop::Plus, mk_var_triv(x1), mk_num_lit(35))
                                                , mk_mset(mk_var(x0), Offset::Num(10), mk_num_lit(40))
                                                , mk_mset(mk_var(x0), Offset::UVar(y4), mk_num_lit(25))
                                                , Effect::ReturnPoint(mk_lbl("foo"), 
                                                    Exp::Begin(
                                                       vec![ mk_set(mk_reg("rax"), mk_fv_triv(1)) ]
                                                      , mk_box!(mk_call("X1")))
                                                    , 16)
                                                , mk_set(mk_var(x1), Triv::MRef(mk_reg("rax"),Offset::Num(10)))]
                                           , Box::new(mk_call("void"))))
                                       , Box::new(
                                           Exp::Begin(
                                             vec![mk_set_op(mk_reg("rax"), Binop::Plus, as_var_triv(mk_reg("rax")), mk_num_lit(10))]
                                            , Box::new(mk_call("void")))))
                              )
               ]
         , body_map
         , Exp::Begin(
            vec![ mk_set(mk_var(x2), mk_num_lit(0))
                , mk_set(mk_var(x3), mk_num_lit(1))
                ]
            , Box::new(mk_call("X1"))));
}
