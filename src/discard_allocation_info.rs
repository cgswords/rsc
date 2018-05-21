// PASS    | discard_allocation_info
// ---------------------------------------------------------------------------
// USAGE   | discard_allocation_info : discard_allocation_info::Program -> 
//         |                           discard_call_live::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with the allocation information removed, leaving
//         | the variable-location HashMaps in its place.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass walks through the very top level of the expressions, discarding 
// the relevant forms.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::Location;
use util::Ident;
use util::mk_uvar;

use std::collections::HashMap;

use discard_call_lives::Program     as DCLProgram;
use discard_call_lives::LetrecEntry as DCLLetrecEntry;
use discard_call_lives::Body        as DCLBody;
use discard_call_lives::Exp         as DCLExp;
use discard_call_lives::Effect      as DCLEffect;
use discard_call_lives::Pred        as DCLPred;
use discard_call_lives::Triv        as DCLTriv;
use discard_call_lives::Offset      as DCLOffset;
use discard_call_lives::Variable    as DCLVar;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------
pub enum Program { Letrec(Vec<LetrecEntry>, Body) }

pub struct LetrecEntry
  { pub label : Label
  , pub rhs   : Body
  }

pub struct Body 
  { pub alloc : RegAllocForm
  , pub expression : Exp
  }

pub enum RegAllocForm
	{ Allocated(HashMap<Ident, Location>)
  , Unallocated(RegAllocInfo, HashMap<Ident, Location>)
  }

pub struct RegAllocInfo 
  { locals            : Vec<Ident>
  , unspillables      : Vec<Ident>
  , spills            : Vec<Ident>
  , frame_conflits    : Vec<(Ident, Vec<Ident>)>
  , register_conflits : Vec<(Ident, Vec<Ident>)>
  }

pub enum Exp 
  { Call(Triv, Vec<Location>)
  , If(Pred,Box<Exp>,Box<Exp>)
  , Begin(Vec<Effect>,Box<Exp>)
  }

pub enum Pred
  { True
  , False
  , Op(Relop,Triv,Triv)
  , If(Box<Pred>,Box<Pred>,Box<Pred>)
  , Begin(Vec<Effect>, Box<Pred>)
  }

pub enum Effect
  { SetOp(Variable, (Binop, Triv, Triv))
  , Set(Variable, Triv)
  , Nop
  , MSet(Variable, Offset, Triv) // MSet takes a variable, an offset, and a triv; 
                                 // Variable and Offset MUST be registers, not frame vars
  , ReturnPoint(Label, Exp, i64)
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>, Box<Effect>)
  }

pub enum Variable 
  { Loc(Location)
  , UVar(Ident)
  }

pub enum Triv 
  { Var(Variable)
  , Num(i64) 
  , Label(Label)
  , MRef(Variable, Offset)
  }

pub enum Offset
  { UVar(Ident)
  , Num(i64)
  }

// ---------------------------------------------------------------------------
// OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// 
// pub enum Program { Letrec(Vec<LetrecEntry>, Body) }
// 
// pub struct LetrecEntry
//   { pub label : Label
//   , pub rhs : Body
//   }
// 
// pub struct Body
//   { pub locations : HashMap<Ident, Location> // variable locations for the rhs
//   , pub exp : Exp
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
//   , ReturnPoint(Label, Exp, i64) // Label, Expression for return point, frame size for call
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
pub fn discard_allocation_info(input : Program) -> DCLProgram {
  return match input 
  { Program::Letrec(letrecs, pgm_body) =>  
      DCLProgram::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                        , body(pgm_body))
  }  
}


fn letrec_entry(input : LetrecEntry) -> DCLLetrecEntry {
  DCLLetrecEntry { label : input.label, rhs : body(input.rhs) }
} 

fn body(input: Body) -> DCLBody {
  match input.alloc
	{ RegAllocForm::Allocated(map)  => DCLBody { locations : map, expression : exp(input.expression) }
  , RegAllocForm::Unallocated(..) => panic!("Got past register allocation with an unallocated block.")
  }
}

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}

fn exp(input : Exp) -> DCLExp {
  return match input 
  { Exp::Call(t, call_lives)   => DCLExp::Call(triv(t), call_lives.into_iter().map(|l| loc(l)).collect())
  , Exp::If(test, conseq, alt) => DCLExp::If(pred(test), mk_box!(exp(*conseq)), mk_box!(exp(*alt)))
  , Exp::Begin(effs, body)     => DCLExp::Begin(effs.into_iter().map(|e| effect(e)).collect(), mk_box!(exp(*body)))
  }
}

fn pred(input : Pred) -> DCLPred {
  return match input 
  { Pred::True                  => DCLPred::True
  , Pred::False                 => DCLPred::False
  , Pred::Op(op,t1,t2)          => DCLPred::Op(op, triv(t1), triv(t2))
  , Pred::If(test, conseq, alt) => DCLPred::If(mk_box!(pred(*test)), mk_box!(pred(*conseq)), mk_box!(pred(*alt)))
  , Pred::Begin(effs, body)     => DCLPred::Begin( effs.into_iter().map(|e| effect(e)).collect(), mk_box!(pred(*body)))
  }
}

fn effect(input: Effect) -> DCLEffect {
  return match input 
  { Effect::SetOp(l, (op, t1, t2))      => DCLEffect::SetOp(var(l), (op, triv(t1), triv(t2)))
  , Effect::Set(l, t)                   => DCLEffect::Set(var(l), triv(t))
  , Effect::Nop                         => DCLEffect::Nop
  , Effect::MSet(base, off, val)        => DCLEffect::MSet(var(base), offset(off), triv(val)) 
  , Effect::ReturnPoint(lbl, body, off) => DCLEffect::ReturnPoint(lbl, exp(body), off)
  , Effect::If(test, conseq, alt)       => DCLEffect::If(pred(test), mk_box!(effect(*conseq)) , mk_box!(effect(*alt)))
  , Effect::Begin(effs, body)           => DCLEffect::Begin( mk_box!((*effs).into_iter().map(|e| effect(e)).collect())
                                                           , mk_box!(effect(*body)))
  }
}

fn loc(input : Location) -> Location {
  input
}

fn var(input : Variable) -> DCLVar {
  return match input
  { Variable::Loc(l)   => DCLVar::Loc(loc(l))
  , Variable::UVar(uv) => DCLVar::UVar(uv)
  }
}

fn triv(input : Triv) -> DCLTriv {
  return match input
  { Triv::Var(v)          => DCLTriv::Var(var(v))
  , Triv::Num(n)          => DCLTriv::Num(n)
  , Triv::Label(l)        => DCLTriv::Label(l)
  , Triv::MRef(base, off) => DCLTriv::MRef(var(base), offset(off))
  } 
}

fn offset(input: Offset) -> DCLOffset {
  return match input
  { Offset::UVar(uv) => DCLOffset::UVar(uv)
  , Offset::Num(n)   => DCLOffset::Num(n)
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

fn mk_call(s: &str, lives: Vec<Location>) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)), lives);
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

fn mk_var(id : Ident) -> Variable {
  return Variable::UVar(id);
}

fn mk_var_triv(id: Ident) -> Triv {
  return as_var_triv(Variable::UVar(id));
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
           vec![ LetrecEntry{ label : mk_lbl("X1")
                            , rhs : Body 
                                    { alloc : RegAllocForm::Allocated(map)
                                    , expression : Exp::If(Pred::Op(Relop::LT, mk_var_triv(x2), mk_var_triv(x3)),
                                                   Box::new(
                                                     Exp::Begin(
                                                       vec![ mk_set_op(mk_var(x1), Binop::Plus, mk_var_triv(x1), mk_num_lit(35))
                                                           , mk_mset(mk_var(x0), Offset::Num(10), mk_num_lit(40))
                                                           , mk_mset(mk_var(x0), Offset::UVar(y4), mk_num_lit(25))
                                                           , Effect::ReturnPoint(mk_lbl("foo"), 
                                                               Exp::Begin(
                                                                  vec![ mk_set(mk_reg("rax"), mk_fv_triv(1)) ]
                                                                 , mk_box!(mk_call("X1", Vec::new())))
                                                               , 16)
                                                           , mk_set(mk_var(x0), Triv::MRef(mk_reg("rax"), Offset::Num(10)))]
                                                      , Box::new(mk_call("void", vec![mk_loc_reg("rax")]))))
                                                  , Box::new(
                                                      Exp::Begin(
                                                        vec![mk_set_op(mk_reg("rax"), Binop::Plus, as_var_triv(mk_reg("rax")), mk_num_lit(10))]
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
