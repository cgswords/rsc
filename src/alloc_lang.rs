use util::Label;
use util::Location;
use util::Ident;
use util::Relop;
use util::Binop;

use std::collections::HashMap;

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
  , frame_conflits    : Vec<(Ident, Vec<Ident>)>
  , register_conflits : Vec<(Ident, Vec<Ident>)>
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
