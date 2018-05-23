use util::Label;
use util::Location;
use util::Ident;
use util::Relop;
use util::Binop;

use std::collections::HashMap;

// ---------------------------------------------------------------------------
#[derive(Debug)]
pub enum Program { Letrec(Vec<LetrecEntry>, Body) }

#[derive(Debug)]
pub struct LetrecEntry
  { pub label : Label
  , pub rhs   : Body
  }

#[derive(Debug)]
pub struct Body 
  { pub alloc : RegAllocForm
  , pub expression : Exp
  }

#[derive(Debug)]
pub enum RegAllocForm
	{ Allocated(HashMap<Ident, Location>)
  , Unallocated(RegAllocInfo, HashMap<Ident, Location>)
  }

#[derive(Debug)]
pub struct RegAllocInfo 
  { locals            : Vec<Ident>
  , unspillables      : Vec<Ident>
  , spills            : Vec<Ident>
  , frame_conflicts   : Vec<(Ident, Vec<FrameConflict>)>
  , register_conflits : Vec<(Ident, Vec<RegConflict>)>
  }

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
  { SetOp(Triv, (Binop, Triv, Triv))
  , Set(Triv, Triv)
  , Nop
  , MSet(Triv, Triv, Triv)
  , ReturnPoint(Label, Exp, i64)
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
  , MRef(Box<Triv>, Box<Triv>)
  }

// ---------------------------------------------------------------------------
#[derive(Debug, Clone, Copy)]
pub enum FrameConflict
  { Var(Ident)
  , FrameVar(i64)
  }

pub fn framevar_to_conflict(l : Location) -> FrameConflict {
  match l
  { Location::FrameVar(n) => FrameConflict::FrameVar(n)
  , Location::Reg(r)      => panic!("Tried to convert register {:?} to a frame variable", r)
  }
}

pub fn var_to_frame_conflict(id : Ident) -> FrameConflict {
  FrameConflict::Reg(id)
}

#[derive(Debug, Clone, Copy)]
pub enum RegConflict
  { Var(Ident)
  , Reg(Ident)
  }

pub fn var_to_reg_conflict(id : Ident) -> RegConflict {
  RegConflict::Reg(id)
}

pub fn reg_to_conflict(l : Location) -> RegConflict {
  match l
  { Location::FrameVar(n) =>  panic!("Tried to convert frame var {:?} to a frame variable", n)
  , Location::Reg(r)      => RegConflict:Reg(r)
  }
}
