#[derive(Debug)]
pub enum Program { Letrec(Vec<Letrec>, RegAllocForm, Exp) }
                                       // ^ Stores allocation info for the body 

#[derive(Debug)]
pub enum Letrec 
	{ Entry(RegAllocForm, Exp) }

pub enum RegAllocForm
	{ Allocated(HashMap<UniqueVar, Location>, Exp)
  , Unallocated(mut RegAllocInfo, mut HashMap<UniqueVar, Location>, Exp)
  }

pub struct RegAllocInfo 
  { locals            : mut Vec<UniqueVar>
  , unspillables      : mut Vec<UniqueVar>
  , spills            : mut Vec<UniqueVar>
  , frame_conflits    : mut Vec<(UniqueVar, mut Vec<UniqueVar>)>
  , register_conflits : mut Vec<(UniqueVar, mut Vec<UniqueVar>)>
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
  , UVar(UniqueVar)
  }

#[derive(Debug)]
pub enum Triv 
  { Var(Variable)
  , Num(i64) 
  , Label(Label)
  , MRef(Triv, Triv)
  }

#[derive(Debug)]
pub enum Offset
  { UVar(UniqueVar)
  , Num(i64)
  }
