#[derive(Debug)]
pub enum Program { Letrec(Vec<LetrecEntry>, Body) }
                                       // ^ Stores allocation info for the body 

#[derive(Debug)]
pub struct LetrecEntry
  { label : Label
  , rhs   : Body
  }

#[derive(Debug)]
pub struct Body 
  { alloc : RegAllocForm
  , exp : Exp
  }

#[derive(Debug)]
pub enum RegAllocForm
	{ Allocated(HashMap<Ident, Location>, Exp)
  , Unallocated(mut RegAllocInfo, mut HashMap<Ident, Location>, Exp)
  }

#[derive(Debug)]
pub struct RegAllocInfo 
  { locals            : mut Vec<Ident>
  , unspillables      : mut Vec<Ident>
  , spills            : mut Vec<Ident>
  , frame_conflits    : mut Vec<(Ident, mut Vec<Ident>)>
  , register_conflits : mut Vec<(Ident, mut Vec<Ident>)>
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
  , MRef(Triv, Triv)
  }

#[derive(Debug)]
pub enum Offset
  { UVar(Ident)
  , Num(i64)
  }
