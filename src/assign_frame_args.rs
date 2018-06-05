// PASS    | assign_frame_args
// ---------------------------------------------------------------------------
// USAGE   | assign_frame_args : alloc_lang::Program -> 
//         |                     alloc_lang::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with all of the call_lives placed appropriately.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass walks through expression, ensuring each variable in the call_live form
// is correctly located and then discarding the call_live entry.
// 
// We also introduce frame-pointer operations for the return-point form.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
// use util::Label;
use util::Ident;
use util::Location;
use util::frame_index;
use util::index_fvar;
use util::FRAME_PTR_REG;
use util::WORD_SIZE;

use alloc_lang::Program;
use alloc_lang::LetrecEntry;
use alloc_lang::RegAllocForm;
use alloc_lang::RegAllocInfo;
use alloc_lang::Body;
use alloc_lang::Exp;
use alloc_lang::Pred;
use alloc_lang::Effect;
use alloc_lang::Variable;
use alloc_lang::Triv;
use alloc_lang::RegConflict;
use alloc_lang::loc_is_reg;
use alloc_lang::reg_to_conflict;
use alloc_lang::var_to_reg_conflict;

use petgraph::graph::Graph;
use petgraph::graph::NodeIndex;
use petgraph::Undirected;

use std::collections::HashMap;
use std::collections::HashSet;
use std::cmp::max;

// ---------------------------------------------------------------------------
// INPUT / OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// #[derive(Debug)]
// pub enum Program { Letrec(Vec<LetrecEntry>, Body) }
//                                        // ^ Stores allocation info for the body 
// 
// #[derive(Debug)]
// pub struct LetrecEntry
//   { label : Label
//   , rhs   : Body
//   }
// 
// #[derive(Debug)]
// pub struct Body 
//   { alloc : RegAllocForm
//   , exp : Exp
//   }
// 
// pub enum RegAllocForm
//  { Allocated(HashMap<Ident, Location>)
//  , Unallocated(mut RegAllocInfo, mut HashMap<Ident, Location>)
//  }
// 
// pub struct RegAllocInfo 
//   { pub locals             : Vec<Ident>
//   , pub unspillables       : Vec<Ident>
//   , pub spills             : Vec<Ident>
//   , pub call_lives         : Vec<Variable>
//   , pub frame_conflicts    : Vec<(Ident, Vec<FrameConflict>)>
//   , pub register_conflicts : Vec<(Ident, Vec<RegConflict>)>
//   , pub new_frames         : Vec<Vec<Ident>>;
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
//   , MSet(Triv, Triv, Triv) // dest, offset, src
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
//   , MRef(Triv, Triv) // src, offset
//   }
// 
//pub enum FrameConflict
//  { Var(Ident)
//  , FrameVar(i64)
//  }
//
// pub enum RegConflict
//   { Var(Ident)
//   , Reg(Ident)
//   }

macro_rules! mk_box {
  ($e:expr) => [Box::new($e)]
}


// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn assign_frame_args(input : Program) -> Program {
  return match input 
  { Program::Letrec(letrecs, body_exp) =>  
      Program::Letrec( letrecs.into_iter().map(|x| letrec_entry(x)).collect()
                     , body(body_exp))
  }  
}

fn letrec_entry(input : LetrecEntry) -> LetrecEntry {
  LetrecEntry 
  { label : input.label
  , rhs   : body(input.rhs)
  }
}

fn body(input: Body) -> Body {
  match input.alloc
  { RegAllocForm::Allocated(vmap)      => Body { alloc : RegAllocForm::Allocated(vmap), expression : input.expression }
  , RegAllocForm::Unallocated(info, mut vmap) => {

      let mut frame_size = { (&info.call_lives).into_iter().fold(0, |acc, x| max(acc, var_findex(x.clone(), &vmap))) + 1 };

      let mut new_fvars = HashSet::new();

      let mut new_locations = for frame in &info.new_frames {
        let mut new_index = frame_size;
        for var in frame {
          new_fvars.insert(var.clone());
          vmap.insert(var.clone(), index_fvar(new_index));
          new_index += 1;
        }
      };

      let mut new_info = info;

      new_info.locals = new_info.locals.into_iter().collect::<HashSet<_>>().difference(&new_fvars).map(|e| e.clone()).collect();
      new_info.call_lives = Vec::new();
      new_info.new_frames = Vec::new();

      Body { alloc : RegAllocForm::Unallocated(new_info, vmap), expression : exp(input.expression, frame_size) }

    }
  }
}

fn exp(input : Exp, frame_size : i64) -> Exp { 
  match input
  { Exp::Call(target, lives) => Exp::Call(target, lives) 
  , Exp::If(test, con, alt)  => Exp::If(pred(test, frame_size), mk_box!(exp(*con, frame_size)), mk_box!(exp(*alt, frame_size)))
  , Exp::Begin(effs, tail)   => Exp::Begin(effs.into_iter().map(|e| effect(e, frame_size)).collect(), mk_box!(exp(*tail, frame_size)))
  }
}

fn pred(input : Pred, frame_size : i64) -> Pred {
  match input
  { Pred::True                  => Pred::True
  , Pred::False                 => Pred::False
  , Pred::Op(op, triv1, triv2)  => Pred::Op(op, triv1, triv2)
  , Pred::If(test, conseq, alt) => Pred::If( mk_box!(pred(*test, frame_size))
                                           , mk_box!(pred(*conseq, frame_size))
                                           , mk_box!(pred(*alt, frame_size)))
  , Pred::Begin(effs, test)     => Pred::Begin(effs.into_iter().map(|e| effect(e, frame_size)).collect(), mk_box!(pred(*test, frame_size)))
  }
}

fn effect(input : Effect, frame_size : i64) -> Effect {
  match input
  { Effect::SetOp(dest, (op, arg1, arg2)) => Effect::SetOp(dest, (op, arg1, arg2))
  , Effect::Set(dest, src)                => Effect::Set(dest, src) 
  , Effect::Nop                           => Effect::Nop
  , Effect::MSet(dest, offset, src)       => Effect::MSet(dest, offset, src)
  , Effect::ReturnPoint(lbl, body, size)  => 
      Effect::Begin(mk_box!(vec![ Effect::SetOp(fv_as_triv(), (Binop::Plus, fv_as_triv(), Triv::Num(frame_size << WORD_SIZE)))
                                , Effect::ReturnPoint(lbl, exp(body, frame_size), frame_size)
                                , Effect::SetOp(fv_as_triv(), (Binop::Minus, fv_as_triv(), Triv::Num(frame_size << WORD_SIZE)))]))
  , Effect::If(test, conseq, alt)         => Effect::If( pred(test, frame_size)
                                                       , mk_box!(effect(*conseq, frame_size))
                                                       , mk_box!(effect(*alt, frame_size)))
  , Effect::Begin(effs)                   => Effect::Begin(mk_box!((*effs).into_iter().map(|e| effect(e, frame_size)).collect()))
  }
} 

// ---------------------------------------------------------------------------
fn fv_as_triv() -> Triv {
  Triv::Var(Variable::Loc(Location::Reg(Ident::from_str(FRAME_PTR_REG))))
}

fn var_findex(v : Variable, vmap : &HashMap<Ident, Location>) -> i64 {
  match v
  { Variable::Loc(l)  => frame_index(l)
  , Variable::UVar(v) => if let Some(loc) = vmap.get(&v) { return frame_index(loc.clone()); } else { return -1; }
  }
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

pub mod test {

  macro_rules! mk_box {
    ($e:expr) => [Box::new($e)]
  }

  use util::index_fvar;
  use util::mk_uvar;
  use util::Binop;
  use util::Relop;
  use util::Label;
  use util::Ident;
  use util::Location;

  use alloc_lang::Program;
  use alloc_lang::LetrecEntry;
  use alloc_lang::RegAllocForm;
  use alloc_lang::RegAllocInfo;
  use alloc_lang::Exp;
  use alloc_lang::Pred;
  use alloc_lang::Body;
  use alloc_lang::Effect;
  use alloc_lang::Variable;
  use alloc_lang::Triv;

  use petgraph::graph::Graph;
  use std::collections::HashMap;

  #[allow(dead_code)]
  fn calle(call : Triv, args : Vec<Location>) -> Exp { Exp::Call(call, args) }

  #[allow(dead_code)]
  fn ife(test : Pred, conseq : Exp, alt : Exp) -> Exp { Exp::If(test, mk_box!(conseq), mk_box!(alt)) }

  #[allow(dead_code)]
  fn begine(args : Vec<Effect>, base : Exp) -> Exp { Exp::Begin(args, mk_box!(base)) }

  #[allow(dead_code)]
  fn rop(op : Relop, t1 : Triv, t2 : Triv) -> Pred { Pred::Op(op, t1, t2) }

  #[allow(dead_code)]
  fn ifp(test : Pred, conseq : Pred, alt : Pred) -> Pred { Pred::If(mk_box!(test), mk_box!(conseq), mk_box!(alt)) }

  #[allow(dead_code)]
  fn beginp(args : Vec<Effect>, base : Pred) -> Pred { Pred::Begin(args, mk_box!(base)) }

  #[allow(dead_code)]
  fn setopf(t1 : Triv, op : Binop, arg1 : Triv, arg2 : Triv) -> Effect { Effect::SetOp(t1, (op, arg1, arg2)) }

  #[allow(dead_code)]
  fn setf(dest : Triv, src : Triv) -> Effect { Effect::Set(dest, src) }
  
  #[allow(dead_code)]
  fn nopf() -> Effect { Effect::Nop }
  
  #[allow(dead_code)]
  fn msetf(dest : Triv, src : Triv, offset : Triv) -> Effect { Effect::MSet(dest, src, offset) }
  
  #[allow(dead_code)]
  fn retf(lbl : Label,  frame_size : i64, body : Exp) -> Effect { Effect::ReturnPoint(lbl, body, frame_size) }
  
  #[allow(dead_code)]
  fn iff(test : Pred, conseq : Effect, alt : Effect) -> Effect { Effect::If(test, mk_box!(conseq), mk_box!(alt)) }
 
  #[allow(dead_code)]
  fn beginf(args : Vec<Effect>) -> Effect { Effect::Begin(mk_box!(args)) }
  
  #[allow(dead_code)]
  fn uv(name : Ident) -> Variable { Variable::UVar(name) }

  #[allow(dead_code)]
  fn vt(name : Ident) -> Triv { Triv::Var(Variable::UVar(name)) }
  
  #[allow(dead_code)]
  fn nt(val : i64) -> Triv { Triv::Num(val) }
  
  #[allow(dead_code)]
  fn lt(lbl : Label) -> Triv { Triv::Label(lbl) }
  
  #[allow(dead_code)]
  fn mreft(src : Triv, offset : Triv) -> Triv { Triv::MRef(mk_box!(src), mk_box!(offset)) }

  #[allow(dead_code)]
  fn fvar(n: i64) -> Triv { Triv::Var(Variable::Loc(index_fvar(n))) }

  #[allow(dead_code)]
  fn reg(s: &str) -> Triv { Triv::Var(Variable::Loc(Location::Reg(Ident::from_str(s)))) }
  
  #[allow(dead_code)]
  fn regl(s: &str) -> Location { Location::Reg(Ident::from_str(s)) }

  #[allow(dead_code)]
  fn mk_lbl(s : &str) -> Label { Label { label : Ident::from_str(s) } }

  fn mk_alloc_form() -> RegAllocInfo
  { RegAllocInfo
    { locals             : Vec::new()
    , unspillables       : Vec::new()
    , spills             : Vec::new()
    , frame_conflicts    : Graph::new_undirected()
    , register_conflicts : Graph::new_undirected()
    , call_lives         : Vec::new()
    , new_frames         : vec![vec![Ident::from_str("nfv10"), Ident::from_str("nfv11")]]
    }
  }

  pub fn test1() -> Program {

    let x0 = mk_uvar("x");
    let x1 = mk_uvar("x");
    let x2 = mk_uvar("x");
    let x3 = mk_uvar("x");
    let y4 = mk_uvar("y");

    let z5 = mk_uvar("z");
    let z6 = mk_uvar("z");
    let z7 = mk_uvar("z");
    let z8 = mk_uvar("z");
    let z9 = mk_uvar("z");

    let z10 = mk_uvar("z");
    let z11 = mk_uvar("z");
    let z12 = mk_uvar("z");

    let mut map = HashMap::new();
    map.insert(x0, regl("rbx"));
    map.insert(z6, Location::FrameVar(2));
    map.insert(x2, regl("r8"));
    map.insert(x3, regl("r9"));
    map.insert(y4, regl("r15"));

    let mut body_map = HashMap::new();
    body_map.insert(x2, regl("r8"));
    body_map.insert(x3, regl("r9"));

    let binding1_alloc = mk_alloc_form();

    let binding1 = 
      LetrecEntry
      { label : mk_lbl("X1")
      , rhs : Body
              { alloc : RegAllocForm::Unallocated(binding1_alloc, map)
              , expression : ife(rop(Relop::LT, vt(x2), vt(x3))
                                , begine(vec![ setopf(fvar(1), Binop::Plus, fvar(1), fvar(2)) 
                                             , msetf(vt(x0), nt(1), nt(40))
                                             , msetf(vt(x0), vt(y4), nt(25))
                                             , retf(mk_lbl("foo"), 0,
                                                    begine( vec![ setf(reg("rax"), fvar(1)) ]
                                                          , calle(lt(mk_lbl("X3")), vec![])) ) 
                                             , setf(vt(x0), mreft(reg("rax"), nt(1)))
                                             ]
                                        , calle(lt(mk_lbl("X2")), vec![]))
                                , begine(vec![ setopf(vt(x1), Binop::Plus, vt(x1), nt(35)) ]
                                        , calle(lt(mk_lbl("X2")), vec![])))
              }
      };

    let mut body_map = HashMap::new();
    body_map.insert(x2, regl("r8"));
    body_map.insert(x3, regl("r9"));


    let test_body = 
      Body 
      { alloc : RegAllocForm::Allocated(body_map)
      , expression : begine(vec![ setf(vt(x2), nt(0))
                                , setf(vt(x3), nt(1))
                                ]
                           , calle(lt(mk_lbl("X1")), vec![regl("rax"), regl("rbp")]))
      };

    Program::Letrec(vec![binding1], test_body)
  }

}
