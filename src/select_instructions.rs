// PASS    | uncover_register_conflicts
// ---------------------------------------------------------------------------
// USAGE   | uncover_register_conflicts : alloc_lang::Program -> 
//         |                              alloc_lang::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with an updated register conflict graph.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass walks through entire expression, analyzing each binding to
// determine the register and variable conflcits for the register conflict
// graph. After computing said graph, the pass updates the appropriate
// allocation information and returns.
//// ---------------------------------------------------------------------------

// use util::Binop;
// use util::Relop;
// use util::Label;
use util::Ident;
use util::Location;
// use util::mk_uvar;

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
// 	{ Allocated(HashMap<Ident, Location>)
//  , Unallocated(mut RegAllocInfo, mut HashMap<Ident, Location>)
//  }
// 
// pub struct RegAllocInfo 
//   { pub locals             : Vec<Ident>
//   , pub unspillables       : Vec<Ident>
//   , pub spills             : Vec<Ident>
//   , pub frame_conflicts    : Vec<(Ident, Vec<FrameConflict>)>
//   , pub register_conflicts : Vec<(Ident, Vec<RegConflict>)>
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
//   , MSet(Triv, Triv, Triv)
//   , ReturnPoint(Label, Exp, i64)
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
//   , MRef(Triv, Triv)
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

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn uncover_register_conflicts(input : Program) -> Program {
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
  Body { alloc      : input.alloc
       , expression : exp(input.expression)
       }
}

fn exp(input : Exp) -> Exp { 
  match input
  { Exp::Call(_, _)         => input 
  , Exp::If(test, con, alt) => Exp::If(pred(test), con(exp), con(exp))
  , Exp::Begin(effs, tail)  => Exp::Begin(effs.map(|e| effect(e)).collect(), exp(tail))
  }
}

fn pred(input : Pred) -> Pred {
  match input
  { Pred::True                  => Pred::True
  , Pred::False                 => Pred::False
  , Pred::Op(op, triv1, triv2)  => relop(op, triv1, triv2) 
  , Pred::If(test, conseq, alt) => Pred::If(pred(*test), pred(*conseq), pred(*alt))
  , Pred::Begin(effs, test)     => Pred::Begin(effs.map(|e| effect(e)), pred(*test))
  }
}

fn relop(op : Relop, arg1 : Triv, arg2 : Triv) -> Pred {
  if arg1.is_var() {
  } else if ar2.is_var() {
    
  } else {
    
  }
}

fn effects( input : &Vec<Effect>, liveset : HashSet<RegConflict>
          , gs : &mut Graph<RegConflict, (), Undirected>, nm : &mut HashMap<RegConflict, NodeIndex>) -> HashSet<RegConflict> {
  let mut cur_liveset = liveset;
  
  // We process the effects from the bottom up to keep track of the
  // live set: everything live is everything used below this effect
  for eff in input.into_iter().rev() {
    cur_liveset = effect(eff, cur_liveset, gs, nm);
  }

  cur_liveset
}

fn effect( input : &Effect, liveset : HashSet<RegConflict>
         , gs : &mut Graph<RegConflict, (), Undirected>, nm : &mut HashMap<RegConflict, NodeIndex>) -> HashSet<RegConflict> {
  match input
  { Effect::SetOp(dest, (op, src1, src2)) => {
      let mut dest_lives = triv(dest, gs, nm);
      add_conflicts(&dest_lives, &liveset, gs, nm);

      let mut src1_lives = triv(src1, gs, nm);
      let mut src2_lives = triv(src2, gs, nm);

      return liveset.difference(&dest_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src1_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src2_lives).map(|e| e.clone()).collect();
    }
  , Effect::Set(dest, src)                => {
      let mut dest_lives = triv(src, gs, nm);
      add_conflicts(&dest_lives, &liveset, gs, nm);
      
      let mut src_lives = triv(src, gs, nm);
      
      return liveset.difference(&dest_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src_lives).map(|e| e.clone()).collect();
    }
  , Effect::Nop                           => liveset
  , Effect::MSet(dest, src1, src2)        => {
      let mut dest_lives = triv(dest, gs, nm);
      add_conflicts(&dest_lives, &liveset, gs, nm); 

      let mut src1_lives = triv(src1, gs, nm);
      add_conflicts(&src1_lives, &liveset, gs, nm);

      let mut src2_lives = triv(src2, gs, nm);
      add_conflicts(&src1_lives, &liveset, gs, nm); 

      return liveset.union(&dest_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src1_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src2_lives).map(|e| e.clone()).collect();
    }
  , Effect::ReturnPoint(lbl, e, size)     => exp(e, gs, nm)
  , Effect::If(test, conseq, alt)         => {
      let con_lives = effect(conseq, liveset.clone(), gs, nm);
      let alt_lives = effect(alt, liveset.clone(), gs, nm);
      return pred(test, con_lives, alt_lives, gs, nm);
    }
  , Effect::Begin(effs, eff)              => effects(effs, effect(eff, liveset, gs, nm), gs, nm)
  }
}

fn triv( input : &Triv
       , gs : &mut Graph<RegConflict, (), Undirected>, nm : &mut HashMap<RegConflict, NodeIndex>) -> HashSet<RegConflict> {
  match input
  { Triv::Var(Variable::UVar(id))               => vec![RegConflict::Var(id.clone())].into_iter().collect()
  , Triv::Var(Variable::Loc(Location::Reg(id))) => vec![RegConflict::Reg(id.clone())].into_iter().collect()
  , Triv::Var(_)   => HashSet::new()
  , Triv::Num(_)   => HashSet::new()
  , Triv::Label(_) => HashSet::new()
  , Triv::MRef(triv1, triv2) => {
      let mut triv1_lives = triv(&*triv1, gs, nm);
      let mut triv2_lives = triv(&*triv2, gs, nm);

      add_conflicts(&triv1_lives, &triv2_lives, gs, nm);
      
      return triv1_lives.union(&triv2_lives).map(|e| e.clone()).collect();
    }
  }
}


// ---------------------------------------------------------------------------

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

  fn calle(call : Triv, args : Vec<Location>) -> Exp { Exp::Call(call, args) }

  fn ife(test : Pred, conseq : Exp, alt : Exp) -> Exp { Exp::If(test, mk_box!(conseq), mk_box!(alt)) }

  fn begine(args : Vec<Effect>, base : Exp) -> Exp { Exp::Begin(args, mk_box!(base)) }

  fn rop(op : Relop, t1 : Triv, t2 : Triv) -> Pred { Pred::Op(op, t1, t2) }

  fn ifp(test : Pred, conseq : Pred, alt : Pred) -> Pred { Pred::If(mk_box!(test), mk_box!(conseq), mk_box!(alt)) }

  fn beginp(args : Vec<Effect>, base : Pred) -> Pred { Pred::Begin(args, mk_box!(base)) }

  fn setopf(t1 : Triv, op : Binop, arg1 : Triv, arg2 : Triv) -> Effect { Effect::SetOp(t1, (op, arg1, arg2)) }

  fn setf(dest : Triv, src : Triv) -> Effect { Effect::Set(dest, src) }
  
  fn nopf() -> Effect { Effect::Nop }
  
  fn msetf(dest : Triv, src : Triv, offset : Triv) -> Effect { Effect::MSet(dest, src, offset) }
  
  fn retf(lbl : Label,  frame_size : i64, body : Exp) -> Effect { Effect::ReturnPoint(lbl, body, frame_size) }
  
  fn iff(test : Pred, conseq : Effect, alt : Effect) -> Effect { Effect::If(test, mk_box!(conseq), mk_box!(alt)) }
 
  fn beginf(args : Vec<Effect>, base : Effect) -> Effect { Effect::Begin(mk_box!(args), mk_box!(base)) }
  
  fn uv(name : Ident) -> Variable { Variable::UVar(name) }

  fn vt(name : Ident) -> Triv { Triv::Var(Variable::UVar(name)) }
  
  fn nt(val : i64) -> Triv { Triv::Num(val) }
  
  fn lt(lbl : Label) -> Triv { Triv::Label(lbl) }
  
  fn mreft(src : Triv, offset : Triv) -> Triv { Triv::MRef(mk_box!(src), mk_box!(offset)) }

  fn fvar(n: i64) -> Triv { Triv::Var(Variable::Loc(index_fvar(n))) }

  fn reg(s: &str) -> Triv { Triv::Var(Variable::Loc(Location::Reg(Ident::from_str(s)))) }
  
  fn regl(s: &str) -> Location { Location::Reg(Ident::from_str(s)) }

  fn mk_lbl(s : &str) -> Label { Label { label : Ident::from_str(s) } }

  fn mk_alloc_form() -> RegAllocInfo
  { RegAllocInfo
    { locals             : Vec::new()
    , unspillables       : Vec::new()
    , spills             : Vec::new()
    , frame_conflicts    : Graph::new_undirected()
    , register_conflicts : Graph::new_undirected()
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
                                , begine(vec![ setopf(vt(x1), Binop::Plus, vt(x1), nt(35)) 
                                             , msetf(vt(x0), nt(1), nt(40))
                                             , msetf(vt(x0), vt(y4), nt(25))
                                             , retf(mk_lbl("foo"), 4,
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
