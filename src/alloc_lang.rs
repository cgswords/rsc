use std::fmt;
use std::collections::HashMap;
use petgraph::graph::Graph;
use petgraph::Undirected;

use util::Label;
use util::Location;
use util::Ident;
use util::Relop;
use util::Binop;

// ---------------------------------------------------------------------------
#[derive(Debug)]
pub enum Program { Letrec(Vec<LetrecEntry>, Body) }

// impl fmt::Debug for Program {
//   fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//     match &self {
//       Program::Letrec(bindings, body) => {
//         write!(f, "Program\n");
//         for binding in bindings {
//           write!(f, "{:?}", binding);
//         }
//         write!(f, "\n{:?}", body);
//         return f;
//       }  
//     }
//   }
// }

pub struct LetrecEntry
  { pub label : Label
  , pub rhs   : Body
  }

impl fmt::Debug for LetrecEntry {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "\n\t[{:?}\n\t{:?}]\n", self.label, self.rhs)
  }
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

pub struct RegAllocInfo 
  { pub locals             : Vec<Ident>
  , pub register_conflicts : Graph<RegConflict, (), Undirected>
  , pub unspillables       : Vec<Ident>
  , pub spills             : Vec<Ident>
  , pub call_lives         : Vec<Variable>
  , pub new_frames         : Vec<Vec<Ident>>
  , pub frame_conflicts    : Graph<FrameConflict, (), Undirected>
  }

impl fmt::Debug for RegAllocInfo {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "\n\t\tAllocInfo\n\t\t  locals: {:?}\n\t\t  unspillables: {:?}]\n\t\t  spills: {:?}\n\t\t  framecs:  {:?}\n\t\t  regs: {:?}\n", 
              self.locals, self.unspillables, self.spills, self.frame_conflicts, self.register_conflicts)
  }
}

#[derive(Debug,Clone)]
pub enum Exp 
  { Call(Triv, Vec<Location>)
  , If(Pred,Box<Exp>,Box<Exp>)
  , Begin(Vec<Effect>,Box<Exp>)
  }

#[allow(dead_code)]
#[derive(Debug,Clone)]
pub enum Pred
  { True
  , False
  , Op(Relop,Triv,Triv)
  , If(Box<Pred>,Box<Pred>,Box<Pred>)
  , Begin(Vec<Effect>, Box<Pred>)
  }

#[derive(Clone)]
pub enum Effect
  { SetOp(Triv, (Binop, Triv, Triv))
  , Set(Triv, Triv)
  , Nop
  , MSet(Triv, Triv, Triv) // dest, offset, src
  , ReturnPoint(Label, Exp, i64)
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>)
  }

impl fmt::Debug for Effect {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self
    { Effect::SetOp(t1, (op, t2, t3))     => write!(f, "set {:?} ({:?} {:?} {:?})", t1, op, t2, t3)
    , Effect::Set(t1, t2)                 => write!(f, "set {:?} {:?}", t1, t2)
    , Effect::Nop                         => write!(f, "nop")
    , Effect::MSet(t1, t2, t3)            => write!(f, "mset {:?} {:?} {:?}", t1, t2, t3)
    , Effect::ReturnPoint(lbl, exp, size) => write!(f, "ret_pnt {:?} {:?} {:?}", lbl.label, size, exp)
    , Effect::If(test, con, alt)          => write!(f, "if {:?} {:?} {:?}", test, con, alt)
    , Effect::Begin(es)                   => write!(f, "(begin {:?})", es)
    }
  }
}

#[derive(Clone,PartialEq,Eq)]
pub enum Variable 
  { Loc(Location)
  , UVar(Ident)
  }

impl fmt::Debug for Variable {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self
    { Variable::Loc(l)  => write!(f, "{:?}", l)
    , Variable::UVar(v) => write!(f, "v_{:?}", v)
    }
  }
}

#[derive(Clone,PartialEq,Eq)]
pub enum Triv 
  { Var(Variable)
  , Num(i64) 
  , Label(Label)
  , MRef(Box<Triv>, Box<Triv>) // src, offset
  }

impl fmt::Debug for Triv {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match &self
    { Triv::Var(v)       => write!(f, "{:?}", v)
    , Triv::Num(n)       => write!(f, "{:?}", n)
    , Triv::Label(n)     => write!(f, "lbl_{:?}", n.label)
    , Triv::MRef(t1, t2) => write!(f, "(mref {:?} {:?})", t1, t2)
    }
  }
}

impl Triv {
  pub fn is_var(&self) -> bool {
    match self
    { Triv::Var(_) => true
    , _            => false
    }
  }

  pub fn is_uvar(&self) -> bool {
    match self
    { Triv::Var(Variable::UVar(_)) => true
    , _                            => false
    }
  }

  pub fn is_fvar(&self) -> bool {
    match self
    { Triv::Var(Variable::Loc(Location::FrameVar(_))) => true
    , _                                               => false
    }
  }

  pub fn is_reg(&self) -> bool {
    match self
    { Triv::Var(Variable::Loc(Location::Reg(_))) => true
    , _                                          => false
    }
  }

  pub fn is_label(&self) -> bool {
    match self
    { Triv::Label(_) => true
    , _              => false
    }
  }

  pub fn is_int(&self) -> bool {
    match self
    { Triv::Num(_) => true
    , _            => false
    }
  }

  // conservative!
  pub fn is_int32(&self) -> bool {
    match self
    { Triv::Num(n) => (-2147483648 < *n) && (2147483647 > *n)
    , _            => false
    }
  }
}


// ---------------------------------------------------------------------------
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FrameConflict
  { Var(Ident)
  , FrameVar(i64)
  }

pub fn fvar_to_conflict(l : Location) -> FrameConflict {
  match l
  { Location::FrameVar(n) => FrameConflict::FrameVar(n)
  , Location::Reg(r)      => panic!("Tried to convert register {:?} to a frame variable", r)
  }
}

pub fn var_to_frame_conflict(id : Ident) -> FrameConflict {
  FrameConflict::Var(id)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RegConflict
  { Var(Ident)
  , Reg(Ident)
  }

impl RegConflict {
  pub fn is_var(&self) -> bool {
    match self
    { RegConflict::Var(_) => true
    , RegConflict::Reg(_) => false
    }
  }

  pub fn is_reg(&self) -> bool { !self.is_var() }
}

pub fn loc_is_reg(loc : &Location) -> bool {
  match loc
  { Location::Reg(_)      => true
  , Location::FrameVar(_) => false
  }
}

pub fn var_to_reg_conflict(id : Ident) -> RegConflict {
  RegConflict::Var(id)
}

pub fn reg_to_conflict(l : Location) -> RegConflict {
  match l
  { Location::FrameVar(n) =>  panic!("Tried to convert frame var {:?} to a frame variable", n)
  , Location::Reg(r)      => RegConflict::Reg(r)
  }
}

// ---------------------------------------------------------------------------
// Checks is every block has allocation bindings (instead of unallocation
// bindings).

pub fn everybody_home(pgm : &Program) -> bool {
  fn is_home(entry : &Body) -> bool {
    match entry.alloc
    { RegAllocForm::Allocated(_)      => true
    , RegAllocForm::Unallocated(_, _) => false
    }
  }

  match pgm
  { Program::Letrec(bindings, main) => 
    { let bindings_home = bindings.into_iter().fold(true, |acc, binding| acc && is_home(&binding.rhs));
      bindings_home && is_home(&main)
    }
  }
}
