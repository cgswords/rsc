// PASS    | expose_frame_pointer
// ---------------------------------------------------------------------------
// USAGE   | Convert return-point forms into return-point forms without 
//         | frame bumps.
// ---------------------------------------------------------------------------
// RETURNS | The new program with explicit frame pointers
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass converts each return-point form into a similar form without the
// explicit frame offset. To do this, we create explicit SetOp terms that
// manually adjust the frame pointer in the frame pointer register.
//
// Design Consideration: The frame pointer always points to the base of the
// current frame, so frame variables in the current frame live above it:
//
//  | UNUSED |
//  | MEMORY |
//  |        |
//  |        |
//  |--------|
//  | FV2    |
//  |--------|
//  | FV1    |
//  |--------|
//  | FV0    |
//  |--------| <-- FRAME POINTER
//  | OLDER  |
//  | STACK  |
//  |        |
//   \/\/\/\/ 
//  |\/\/\/\/|
//  |        |
//  |--------|
//
// The implementation is a straightforward walk, locating and modifying the
// return-point forms.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::Ident;
use util::X86Loc;
use util::FRAME_PTR_REG;

use expose_memory_operands::Program  as EMOProgram;
use expose_memory_operands::Letrec   as EMOLetrec;
use expose_memory_operands::Exp      as EMOExp;
use expose_memory_operands::Effect   as EMOEffect;
use expose_memory_operands::Pred     as EMOPred;
use expose_memory_operands::Triv     as EMOTriv;
use expose_memory_operands::Offset   as EMOOffset;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------
#[derive(Debug)]
pub enum Program { Letrec(Vec<Letrec>, Exp) }

#[derive(Debug)]
pub enum Letrec { Entry(Label,Exp) }

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
  { SetOp(X86Loc, (Binop, Triv, Triv))
  , Set(X86Loc, Triv)
  , Nop
  , MSet(Ident, Offset, Triv) // MSet takes a register, an offset, and a triv 
  , ReturnPoint(Label, Exp, i64) // Label, Expression for return point, frame size for call
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>, Box<Effect>)
  }

#[derive(Debug)]
pub enum Triv 
  { Loc(X86Loc) 
  , Num(i64) 
  , Label(Label)
  , MRef(Ident, Offset) // Memory reference of a register and an offset
  }

#[derive(Debug)]
pub enum Offset
  { Reg(Ident)
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
//   { SetOp(X86Loc, (Binop, Triv, Triv))
//   , Set(X86Loc, Triv)
//   , Nop
//   , ReturnPoint(Label, Exp)
//   , If(Pred, Box<Effect>, Box<Effect>)
//   , Begin(Box<Vec<Effect>>, Box<Effect>)
//   }
// 
// pub enum X86Loc 
//   { Reg(Ident)
//   , DisplaceOperand(Ident, i64) 
//   }
// 
// pub enum Triv 
//   { Loc(X86Loc) 
//   , Num(i64) 
//   , Label(Label)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn expose_frame_pointer(input : Program) -> EMOProgram {
  return match input 
  { Program::Letrec(letrecs, body) =>  
      EMOProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , exp(body))
  }  
}

fn letrec_entry(input : Letrec) -> EMOLetrec {
  return match input 
  { Letrec::Entry(lbl,rhs) => EMOLetrec::Entry(lbl, exp(rhs)) }
} 

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp) -> EMOExp {
  return match input 
  { Exp::Call(t)               => EMOExp::Call(triv(t))
  , Exp::If(test, conseq, alt) => EMOExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => EMOExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> EMOPred {
  return match input 
  { Pred::True                  => EMOPred::True
  , Pred::False                 => EMOPred::False
  , Pred::Op(op,t1,t2)          => EMOPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => EMOPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => EMOPred::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn mk_emo_reg_loc(s : Ident) -> X86Loc {
  return X86Loc::Reg(s);
}

fn mk_emo_reg_triv(s : Ident) -> EMOTriv {
  return EMOTriv::Loc(mk_emo_reg_loc(s));
}

fn mk_emo_num_lit(n : i64) -> EMOTriv {
  return EMOTriv::Num(n);
}

fn effect(input: Effect) -> EMOEffect {
  let frame_ptr_reg = Ident::from_str(FRAME_PTR_REG);

  return match input 
  { Effect::SetOp(l, (op, t1, t2)) => EMOEffect::SetOp(loc(l), (op, triv(t1), triv(t2)))
  , Effect::Set(l, t)              => EMOEffect::Set(loc(l), triv(t))
  , Effect::Nop                    => EMOEffect::Nop
  , Effect::MSet(base,off,val)     => EMOEffect::MSet(base, offset(off), triv(val))
  , Effect::ReturnPoint(lbl, body, new_offset) => 
      EMOEffect::Begin(mk_box!(vec![ EMOEffect::SetOp( mk_emo_reg_loc(frame_ptr_reg)
                                                     , (Binop::Plus, mk_emo_reg_triv(frame_ptr_reg), mk_emo_num_lit(new_offset)))
                                   , EMOEffect::ReturnPoint(lbl, exp(body))
                                   ])
                      , mk_box!( EMOEffect::SetOp(mk_emo_reg_loc(frame_ptr_reg)
                               , (Binop::Minus, mk_emo_reg_triv(frame_ptr_reg), mk_emo_num_lit(new_offset))))) 
  , Effect::If(test, conseq, alt)  => EMOEffect::If(pred(test), mk_box!(effect(*conseq)), mk_box!(effect(*alt)))
  , Effect::Begin(effs, body)      => EMOEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e)).collect())
                                                      , mk_box!(effect(*body)))
  }
}

fn loc(input : X86Loc) -> X86Loc {
  return input;
}

fn triv(input : Triv) -> EMOTriv {
  return match input
  { Triv::Loc(l)          => EMOTriv::Loc(loc(l))
  , Triv::Num(n)          => EMOTriv::Num(n)
  , Triv::Label(l)        => EMOTriv::Label(l)
  , Triv::MRef(base, off) => EMOTriv::MRef(base, offset(off))
  } 
}

fn offset(input: Offset) -> EMOOffset {
  return match input
  { Offset::Reg(s) => EMOOffset::Reg(s)
  , Offset::Num(n) => EMOOffset::Num(n)
  }
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

fn mk_num_lit(n: i64) -> Triv {
  return Triv::Num(n);
}

fn mk_reg(s: &str) -> X86Loc {
  return X86Loc::Reg(Ident::from_str(s));
}

fn mk_loc_reg(s: &str) -> Triv {
  return mk_loc_triv(mk_reg(s));
}

fn mk_call(s: &str) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)));
}

fn mk_lbl(s : &str) -> Label {
  return Label::new(Ident::from_str(s));
}

fn mk_set_op(dest: X86Loc, op: Binop, t1 : Triv, t2: Triv) -> Effect {
  return Effect::SetOp(dest, (op, t1, t2));
}

fn mk_mset(dest: Ident, offset: Offset, val : Triv) -> Effect {
  return Effect::MSet(dest, offset, val);
}

fn mk_loc_triv(l : X86Loc) -> Triv {
  return Triv::Loc(l);
}

fn mk_set(dest: X86Loc, val: Triv) -> Effect {
  return Effect::Set(dest,val)
}

pub fn test1() -> Program {

  let rax = Ident::from_str("rax");
  let rbx = Ident::from_str("rbx");
  let r15 = Ident::from_str("rbx");

  return Program::Letrec(
           vec![ Letrec::Entry(mk_lbl("X1")
                                   , Exp::If(Pred::Op(Relop::LT ,mk_loc_triv(mk_reg("r9")), mk_loc_triv(mk_reg("r8"))),
                                             Box::new(
                                               Exp::Begin(
                                                 vec![ mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_reg("rax"), mk_num_lit(10))
                                                     , mk_mset(rbx, Offset::Num(10), mk_num_lit(40))
                                                     , mk_mset(rbx, Offset::Reg(r15), mk_num_lit(40))
                                                     , Effect::ReturnPoint(mk_lbl("foo"), 
                                                         Exp::Begin(
                                                            vec![ mk_set_op(mk_reg("rax")
                                                                   , Binop::Plus
                                                                   , mk_loc_reg("rax")
                                                                   , mk_num_lit(10))
                                                                ]
                                                           , mk_box!(mk_call("X1"))),
                                                           16)
                                                     , mk_set(mk_reg("rbx"), Triv::MRef(rax, Offset::Num(10)))]
                                                , Box::new(mk_call("void"))))
                                            , Box::new(
                                                Exp::Begin(
                                                  vec![mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_triv(mk_reg("rax")), mk_num_lit(10))]
                                                 , Box::new(mk_call("void"))))))
               ]
         , Exp::Begin(
            vec![ mk_set(mk_reg("r9"), mk_num_lit(0))
                , mk_set(mk_reg("r8"), mk_num_lit(1))]
            , Box::new(mk_call("X1"))));
}
