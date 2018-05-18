// PASS    | expose_frame_variables
// ---------------------------------------------------------------------------
// USAGE   | Deal with frame variables, computing offsets and converting them
// ---------------------------------------------------------------------------
// RETURNS | A program with each frame variable converted to a displace triv.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass converts every frame variable into a displacement trivial. The
// most relevant note is that this is where the compile switches from using
// the Location form to the X86Loc form for representing locations.
// 
// The main intricacy is that return points can allocate additional frame space
// and then use frame variables in their body. These frame variables need their
// displacement adjusted by the return point's allocation bump. To accomplish
// this, we thread an extra frame offset through and use it when translating
// the frame variables.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::Location;
use util::X86Loc;
use util::FRAME_PTR_REG;
use util::WORD_SIZE;

use expose_frame_pointer::Program  as EFPProgram;
use expose_frame_pointer::Letrec   as EFPLetrec;
use expose_frame_pointer::Exp      as EFPExp;
use expose_frame_pointer::Effect   as EFPEffect;
use expose_frame_pointer::Pred     as EFPPred;
use expose_frame_pointer::Triv     as EFPTriv;
use expose_frame_pointer::Offset   as EFPOffset;

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
  , ReturnPoint(Label, Exp, i64) // Label, Expression for return point, frame size for call
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>, Box<Effect>)
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
//   , ReturnPoint(Label, Exp, i64)
//   , If(Pred, Box<Effect>, Box<Effect>)
//   , Begin(Box<Vec<Effect>>, Box<Effect>)
//   }
// 
// pub enum Location 
//   { Reg(String)
//   , DisplaceOperand(String, i64) // base register and offset value
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
pub fn expose_frame_variables(input : Program) -> EFPProgram {
  return match input 
  { Program::Letrec(letrecs, body) =>  
      EFPProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , exp(body, 0))
  }  
}

fn letrec_entry(input : Letrec) -> EFPLetrec {
  return match input 
  { Letrec::Entry(lbl,rhs) => EFPLetrec::Entry(lbl, exp(rhs, 0)) }
} 

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp, frame_offset: i64) -> EFPExp {
  return match input 
  { Exp::Call(t)               => EFPExp::Call(triv(t, frame_offset))
  , Exp::If(test, conseq, alt) => EFPExp::If( pred(test,           frame_offset)
                                            , mk_box!(exp(*conseq, frame_offset))
                                            , mk_box!(exp(*alt,    frame_offset)))
  , Exp::Begin(effs, body)     => EFPExp::Begin( effs.into_iter().map(|e| effect(e, frame_offset)).collect()
                                               , mk_box!(exp(*body, frame_offset)))
  }
}

fn pred(input : Pred, frame_offset : i64) -> EFPPred {
  return match input 
  { Pred::True                  => EFPPred::True
  , Pred::False                 => EFPPred::False
  , Pred::Op(op,t1,t2)          => EFPPred::Op(op, triv(t1, frame_offset), triv(t2, frame_offset))
  , Pred::If(test, conseq, alt) => EFPPred::If(mk_box!(pred(*test,   frame_offset)),
                                               mk_box!(pred(*conseq, frame_offset)),
                                               mk_box!(pred(*alt,    frame_offset)))
  , Pred::Begin(effs, body)     => EFPPred::Begin( effs.into_iter().map(|e| effect(e, frame_offset)).collect()
                                                 , mk_box!(pred(*body, frame_offset)))
  }
}

fn effect(input: Effect, frame_offset: i64) -> EFPEffect {
  return match input 
  { Effect::SetOp(l, (op, t1, t2)) => EFPEffect::SetOp( loc(l, frame_offset)
                                                      , (op, triv(t1, frame_offset), triv(t2, frame_offset)))
  , Effect::Set(l, t)              => EFPEffect::Set(loc(l, frame_offset), triv(t, frame_offset))
  , Effect::Nop                    => EFPEffect::Nop
  , Effect::MSet(base, off, val)   => EFPEffect::MSet(base, offset(off), triv(val, frame_offset))
  , Effect::ReturnPoint(lbl, body, new_offset) => EFPEffect::ReturnPoint(lbl, exp(body, frame_offset + new_offset), new_offset)
  , Effect::If(test, conseq, alt)  => EFPEffect::If( pred(test, frame_offset)
                                                   , mk_box!(effect(*conseq, frame_offset))
                                                   , mk_box!(effect(*alt, frame_offset)))
  , Effect::Begin(effs, body)      => EFPEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e, frame_offset)).collect())
                                                      , mk_box!(effect(*body, frame_offset)))
  }
}

fn loc(input : Location, frame_offset : i64) -> X86Loc {
  return match input
  { Location::Reg(reg)    => X86Loc::Reg(reg)
  , Location::FrameVar(n) => X86Loc::DisplaceOperand(FRAME_PTR_REG.to_string(), (n << WORD_SIZE) - frame_offset)
  // We compute the offset by shifting the variable index by the word_size, then
  // subtract the frame offset so that if the FV is bumped, we get to the right
  // place anyway.
  }
}

fn triv(input : Triv, frame_offset : i64) -> EFPTriv {
  return match input
  { Triv::Loc(l)          => EFPTriv::Loc(loc(l, frame_offset))
  , Triv::Num(n)          => EFPTriv::Num(n)
  , Triv::Label(l)        => EFPTriv::Label(l)
  , Triv::MRef(base, off) => EFPTriv::MRef(base, offset(off))
  } 
}

fn offset(input: Offset) -> EFPOffset {
  return match input
  { Offset::Reg(s) => EFPOffset::Reg(s)
  , Offset::Num(n) => EFPOffset::Num(n)
  }
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

fn mk_num_lit(n: i64) -> Triv {
  return Triv::Num(n);
}

fn mk_fv_triv(n: i64) -> Triv {
  return Triv::Loc(Location::FrameVar(n));
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
                                                 vec![ mk_set_op(Location::FrameVar(2), Binop::Plus, mk_fv_triv(2), mk_num_lit(35))
                                                     , mk_mset("rbx".to_string(), Offset::Num(10), mk_num_lit(40))
                                                     , mk_mset("rbx".to_string(), Offset::Reg("r15".to_string()), mk_num_lit(25))
                                                     , Effect::ReturnPoint(mk_lbl("foo"), 
                                                         Exp::Begin(
                                                            vec![ mk_set(mk_reg("rax"), mk_fv_triv(1)) ]
                                                           , mk_box!(mk_call("X1")))
                                                         , 16)
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
