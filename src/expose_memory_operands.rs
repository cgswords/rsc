// PASS    | expose_memory_operands
// ---------------------------------------------------------------------------
// USAGE   | Swap mset operations with set! operations, converting frame
//         | variables to displacement operands
// ---------------------------------------------------------------------------
// RETURNS | A pre-flattened, block-exposed program
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass replaces every MSet effect expression and MRef binary operation
// with equivalent expressions in terms of Set effect expressions and
// displacement trivials.
//
// The implementation is a straightforward walk, replacing the appropriate
// terms.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;

use expose_basic_blocks::Program  as EBBProgram;
use expose_basic_blocks::Letrec   as EBBLetrec;
use expose_basic_blocks::Exp      as EBBExp;
use expose_basic_blocks::Effect   as EBBEffect;
use expose_basic_blocks::Pred     as EBBPred;
use expose_basic_blocks::Location as EBBLoc;
use expose_basic_blocks::Triv     as EBBTriv;

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
  { SetOp(Location, (Binop, Triv, Triv))
  , Set(Location, Triv)
  , Nop
  , MSet(String, Offset, Triv) // MSet takes a register, an offset, and a triv 
  , ReturnPoint(Label, Exp)
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>, Box<Effect>)
  }

#[derive(Debug)]
pub enum Location 
  { Reg(String)
  , DisplaceOperand(String, i64) // base register and offset value
  }

#[derive(Debug)]
pub enum Triv 
  { Loc(Location) 
  , Num(i64) 
  , Label(Label)
  , MRef(String, Offset) // Memory reference of a register and an offset
  }

#[derive(Debug)]
pub enum Offset
  { Reg(String)
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
//   , ReturnPoint(Label, Exp)
//   , If(Pred, Box<Effect>, Box<Effect>)
//   , Begin(Box<Vec<Effect>>, Box<Effect>)
//   }
// 
// pub enum Location 
//   { Reg(String)
//   , DisplaceOperand(String, i64) // base register and offset value
//   , IndexOperand(String, String) // base register and offset register
//   }
// 
// pub enum Triv 
//   { Loc(Location) 
//   , Num(i64) 
//   , Label(Label)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn expose_memory_operands(input : Program) -> EBBProgram {
  return match input 
  { Program::Letrec(letrecs, body) =>  
      EBBProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , exp(body))
  }  
}

fn letrec_entry(input : Letrec) -> EBBLetrec {
  return match input 
  { Letrec::Entry(lbl,rhs) => EBBLetrec::Entry(lbl, exp(rhs)) }
} 

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp) -> EBBExp {
  return match input 
  { Exp::Call(t)               => EBBExp::Call(triv(t))
  , Exp::If(test, conseq, alt) => EBBExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => EBBExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> EBBPred {
  return match input 
  { Pred::True                  => EBBPred::True
  , Pred::False                 => EBBPred::False
  , Pred::Op(op,t1,t2)          => EBBPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => EBBPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => EBBPred::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn mk_index_operand(reg1 : String, reg2 : String) -> EBBLoc {
  return EBBLoc::IndexOperand(reg1, reg2);
}

fn mk_displacement_operand(reg : String, offset : i64) -> EBBLoc {
  return EBBLoc::DisplaceOperand(reg, offset);
}

fn effect(input: Effect) -> EBBEffect {
  return match input 
  { Effect::SetOp(l, (op, t1, t2)) => EBBEffect::SetOp (loc(l), (op, triv(t1), triv(t2)))
  , Effect::Set(l, t)              => EBBEffect::Set(loc(l),triv(t))
  , Effect::Nop                    => EBBEffect::Nop
  , Effect::MSet(base,offset,val)  =>
      match offset
      { Offset::Reg(reg) => EBBEffect::Set(mk_index_operand(base, reg), triv(val))
      , Offset::Num(num) => EBBEffect::Set(mk_displacement_operand(base, num), triv(val))
      }
  , Effect::ReturnPoint(lbl, body) => EBBEffect::ReturnPoint(lbl, exp(body))
  , Effect::If(test, conseq, alt)  => EBBEffect::If(pred(test), mk_box!(effect(*conseq)), mk_box!(effect(*alt)))
  , Effect::Begin(effs, body)      => EBBEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e)).collect())
                                                      , mk_box!(effect(*body)))
    
  }
}

fn loc(input : Location) -> EBBLoc {
  return match input
  { Location::Reg(reg)                     => EBBLoc::Reg(reg)
  , Location::DisplaceOperand(reg, offset) => EBBLoc::DisplaceOperand(reg, offset) 
  }
}

fn triv(input : Triv) -> EBBTriv {
  return match input
  { Triv::Loc(l)          => EBBTriv::Loc(loc(l))
  , Triv::Num(n)          => EBBTriv::Num(n)
  , Triv::Label(l)        => EBBTriv::Label(l)
  , Triv::MRef(base, offset) => 
      match offset
      { Offset::Reg(reg) => EBBTriv::Loc(mk_index_operand(base, reg))
      , Offset::Num(num) => EBBTriv::Loc(mk_displacement_operand(base, num))
      }
  } 
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

fn mk_num_lit(n: i64) -> Triv {
  return Triv::Num(n);
}

fn mk_reg(s: &str) -> Location {
  return Location::Reg(s.to_string());
}

fn mk_call(s: &str) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)));
}

fn mk_lbl(s : &str) -> Label {
  return Label::Label(s.to_string());
}

fn mk_set_op(dest: Location, op: Binop, t1 : Triv, t2: Triv) -> Effect {
  return Effect::SetOp(dest, (op, t1, t2));
}

fn mk_mset(dest: String, offset: Offset, val : Triv) -> Effect {
  return Effect::MSet(dest, offset, val);
}

fn mk_loc_triv(l : Location) -> Triv {
  return Triv::Loc(l);
}

fn mk_set(dest: Location, val: Triv) -> Effect {
  return Effect::Set(dest,val)
}

pub fn test1() -> Program {
  return Program::Letrec(
           vec![ Letrec::Entry(mk_lbl("X1")
                                   , Exp::If(Pred::Op(Relop::LT ,mk_loc_triv(mk_reg("r9")), mk_loc_triv(mk_reg("r8"))),
                                             Box::new(
                                               Exp::Begin(
                                                 vec![ mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_triv(mk_reg("rax")), mk_num_lit(10))
                                                     , mk_mset("rbx".to_string(), Offset::Num(10), mk_num_lit(40))
                                                     , mk_mset("rbx".to_string(), Offset::Reg("r15".to_string()), mk_num_lit(40))
                                                     , mk_set(mk_reg("rbx"), Triv::MRef("rax".to_string(),Offset::Num(10)))]
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
