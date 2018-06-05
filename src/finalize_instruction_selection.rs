// PASS    | finalize_instruction_selection
// ---------------------------------------------------------------------------
// USAGE   | finalize_instruction_selection : alloc_lang::Program -> 
//         |                                  discard_allocation_info::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with the MSet and MRef forms converted to use
//         | Offset forms. We depart from alloc_lang here, finishing up the
//         | register and stack frame allocation phase of compilation.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass performs a tree walk, reconstructing the appropriate MSet and
// MRef forms at it finds them.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::Ident;
use util::Location;
use util::mk_uvar;

use alloc_lang::Program;
use alloc_lang::LetrecEntry;
use alloc_lang::RegAllocForm;
use alloc_lang::Exp;
use alloc_lang::Pred;
use alloc_lang::Body;
use alloc_lang::Effect;
use alloc_lang::Variable;
use alloc_lang::Triv;

use std::collections::HashMap;

use discard_allocation_info::Program     as DAIProgram;
use discard_allocation_info::LetrecEntry as DAILetrecEntry;
use discard_allocation_info::Body        as DAIBody;
use discard_allocation_info::Exp         as DAIExp;
use discard_allocation_info::Effect      as DAIEffect;
use discard_allocation_info::Pred        as DAIPred;
use discard_allocation_info::Triv        as DAITriv;
use discard_allocation_info::Offset      as DAIOffset;
use discard_allocation_info::Variable    as DAIVar;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------
//
// INPUT LANG is `alloc_lang`, the register allocation language.
//
// pub enum Program { Letrec(Vec<LetrecEntry>, Body) }
// 
// pub struct LetrecEntry
//   { pub label : Label
//   , pub rhs   : Body
//   }
// 
// pub struct Body 
//   { pub alloc : RegAllocForm
//   , pub expression : Exp
//   }
// 
// pub enum RegAllocForm
// 	{ Allocated(HashMap<Ident, Location>)
//   , Unallocated(RegAllocInfo, HashMap<Ident, Location>)
//   }
// 
// pub struct RegAllocInfo 
//   { locals            : Vec<Ident>
//   , unspillables      : Vec<Ident>
//   , spills            : Vec<Ident>
//   , frame_conflits    : Vec<(Ident, Vec<Ident>)>
//   , register_conflits : Vec<(Ident, Vec<Ident>)>
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
//   , MRef(Box<Triv>, Box<Triv>)
//   }

// ---------------------------------------------------------------------------
// OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// pub enum Program { Letrec(Vec<LetrecEntry>, Body) }
// 
// pub struct LetrecEntry
//   { pub label : Label
//   , pub rhs   : Body
//   }
// 
// pub struct Body 
//   { pub alloc : RegAllocForm
//   , pub expression : Exp
//   }
// 
// pub enum RegAllocForm
// 	{ Allocated(HashMap<Ident, Location>)
//   , Unallocated(RegAllocInfo, HashMap<Ident, Location>)
//   }
// 
// pub struct RegAllocInfo 
//   { locals            : Vec<Ident>
//   , unspillables      : Vec<Ident>
//   , spills            : Vec<Ident>
//   , frame_conflits    : Vec<(Ident, Vec<Ident>)>
//   , register_conflits : Vec<(Ident, Vec<Ident>)>
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
//   { SetOp(Variable, (Binop, Triv, Triv))
//   , Set(Variable, Triv)
//   , Nop
//   , MSet(Variable, Offset, Triv) // MSet takes a variable, an offset, and a triv; 
//                                  // Variable and Offset MUST be registers, not frame vars
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
//   , MRef(Variable, Offset)
//   }
// 
// pub enum Offset
//   { UVar(Ident)
//   , Reg(Ident)
//   , Num(i64)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn finalize_instruction_selection(input : Program) -> DAIProgram {
  return match input 
  { Program::Letrec(letrecs, pgm_body) =>  
      DAIProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , body(pgm_body))
  }  
}


fn letrec_entry(input : LetrecEntry) -> DAILetrecEntry {
  DAILetrecEntry { label : input.label , rhs : body(input.rhs) }
} 

fn body(input : Body) -> DAIBody {
  DAIBody { alloc : input.alloc , expression : exp(input.expression) }
}

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp) -> DAIExp {
  match input 
  { Exp::Call(t, call_lives)   => DAIExp::Call(triv(t), call_lives.into_iter().map(|l| loc(l)).collect())
  , Exp::If(test, conseq, alt) => DAIExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => DAIExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> DAIPred {
  match input 
  { Pred::True                  => DAIPred::True
  , Pred::False                 => DAIPred::False
  , Pred::Op(op,t1,t2)          => DAIPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => DAIPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => DAIPred::Begin( effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn effect(input: Effect) -> DAIEffect {
  match input 
  { Effect::SetOp(dest, (op, t1, t2))   => DAIEffect::SetOp(triv_to_var(dest), (op, triv(t1), triv(t2)))
  , Effect::Set(dest, src)              => DAIEffect::Set(triv_to_var(dest), triv(src))
  , Effect::Nop                         => DAIEffect::Nop
  , Effect::MSet(base, off, val)        => DAIEffect::MSet(triv_to_var(base), triv_to_offset(off), triv(val)) 
  , Effect::ReturnPoint(lbl, body, off) => DAIEffect::ReturnPoint(lbl, exp(body), off)
  , Effect::If(test, conseq, alt)       => DAIEffect::If(pred(test), mk_box!(effect(*conseq)) , mk_box!(effect(*alt)))
  , Effect::Begin(effs)                 => {
      if (*effs).len() == 0 {
        DAIEffect::Nop
      } else {
        let mut eff_iter = (*effs).into_iter().rev();
        if let Some(last_eff) = eff_iter.next() {
          DAIEffect::Begin( mk_box!(eff_iter.rev().map(|e| effect(e)).collect())
                          , mk_box!(effect(last_eff)))
        } else {
          panic!("Tried to retrieve from a non-empty iter and failed.");
        }
      }
    }
  }
}

fn triv_to_var(input : Triv) -> DAIVar {
  match input
  { Triv::Var(v) => var(v)
  , _            => panic!("Instruction selection has left a non-var triv in a var-only place!")
  }
}

fn triv_to_offset(input : Triv) -> DAIOffset {
  match input
  { Triv::Var(Variable::UVar(uv))              => DAIOffset::UVar(uv)
  , Triv::Var(Variable::Loc(Location::Reg(s))) => DAIOffset::Reg(s)
  , Triv::Num(n)                               => DAIOffset::Num(n)
  , _                                          => panic!("Instruction selection has left a non-offset triv in an offset-only place!")
  }
}

fn loc(input : Location) -> Location {
  match input
  { Location::Reg(reg)    => Location::Reg(reg)
  , Location::FrameVar(n) => Location::FrameVar(n)
  }
}

fn var(input : Variable) -> DAIVar {
  match input
  { Variable::Loc(l)   => DAIVar::Loc(loc(l))
  , Variable::UVar(uv) => DAIVar::UVar(uv)
  }
}

fn triv(input : Triv) -> DAITriv {
  match input
  { Triv::Var(v)          => DAITriv::Var(var(v))
  , Triv::Num(n)          => DAITriv::Num(n)
  , Triv::Label(l)        => DAITriv::Label(l)
  , Triv::MRef(base, off) => DAITriv::MRef(triv_to_var(*base), triv_to_offset(*off))
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

fn mk_reg(s: &str) -> Triv {
  return Triv::Var(Variable::Loc(mk_loc_reg(s)));
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

fn mk_set_op(dest: Triv, op: Binop, t1 : Triv, t2: Triv) -> Effect {
  return Effect::SetOp(dest, (op, t1, t2));
}

fn mk_mset(dest: Triv, offset: Triv, val : Triv) -> Effect {
  return Effect::MSet(dest, offset, val);
}

fn mk_loc_triv(l : Location) -> Triv {
  return as_var_triv(loc_as_var(l));
}

fn mk_var(id : Ident) -> Triv {
  return as_var_triv(Variable::UVar(id));
}

fn as_var_triv(v: Variable) -> Triv {
  return Triv::Var(v);
}

fn loc_as_var(l: Location) -> Variable {
  return Variable::Loc(l);
}

fn mk_set(dest: Triv, val: Triv) -> Effect {
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
           vec![ LetrecEntry{ label : mk_lbl("X1")
                            , rhs : Body 
                                    { alloc : RegAllocForm::Allocated(map)
                                    , expression : Exp::If(Pred::Op(Relop::LT, mk_var(x2), mk_var(x3)),
                                                   Box::new(
                                                     Exp::Begin(
                                                       vec![ mk_set_op(mk_var(x1), Binop::Plus, mk_var(x1), mk_num_lit(35))
                                                           , mk_mset(mk_var(x0), mk_num_lit(1), mk_num_lit(40))
                                                           , mk_mset(mk_var(x0), mk_var(y4), mk_num_lit(25))
                                                           , Effect::ReturnPoint(mk_lbl("foo"), 
                                                               Exp::Begin(
                                                                  vec![ mk_set(mk_reg("rax"), mk_fv_triv(1)) ]
                                                                 , mk_box!(mk_call("X1", Vec::new())))
                                                               , 16)
                                                           , mk_set(mk_var(x0), Triv::MRef( mk_box!(mk_reg("rax"))
                                                                                          , mk_box!(mk_num_lit(1))))]
                                                      , Box::new(mk_call("void", vec![mk_loc_reg("rax")]))))
                                                  , Box::new(
                                                      Exp::Begin(
                                                        vec![mk_set_op(mk_reg("rax"), Binop::Plus, mk_reg("rax"), mk_num_lit(10))]
                                                       , Box::new(mk_call("void", vec![mk_loc_reg("rax"), mk_loc_reg("rbp")])))))
                                    }
                            }
               ]
         , Body 
           { alloc : RegAllocForm::Allocated(body_map)
           , expression : Exp::Begin(
                            vec![ mk_set(mk_var(x2), mk_num_lit(0))
                                , mk_set(mk_var(x3), mk_num_lit(1))
                                ]
                                , Box::new(mk_call("X1", vec![mk_loc_reg("rax"), mk_loc_reg("rbp")])))
           });
}
