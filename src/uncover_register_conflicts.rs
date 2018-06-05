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
// use util::Ident;
use util::Location;
// use util::mk_uvar;

use alloc_lang::Program;
use alloc_lang::LetrecEntry;
use alloc_lang::RegAllocForm;
// use alloc_lang::RegAllocInfo;
use alloc_lang::Body;
use alloc_lang::Exp;
use alloc_lang::Pred;
use alloc_lang::Effect;
use alloc_lang::Variable;
use alloc_lang::Triv;
use alloc_lang::RegConflict;
use alloc_lang::loc_is_reg;
use alloc_lang::reg_to_conflict;
//use alloc_lang::var_to_reg_conflict;

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
  match input.alloc
  { RegAllocForm::Allocated(_)                  => Body { alloc : input.alloc , expression : input.expression }
  , RegAllocForm::Unallocated(mut alloc_info, locs) => {
      let mut conflicts : Graph<RegConflict, (), Undirected> = Graph::new_undirected();
      let mut node_map  : HashMap<RegConflict, NodeIndex>    = HashMap::new();

      exp(&input.expression, &mut conflicts, &mut node_map);

      alloc_info.register_conflicts = conflicts;

      return Body { alloc      : RegAllocForm::Unallocated(alloc_info, locs)
                  , expression : input.expression };

    }
  }
}

fn exp( input : &Exp
      , gs : &mut Graph<RegConflict, (), Undirected>
      , nm : &mut HashMap<RegConflict, NodeIndex>) 
      -> HashSet<RegConflict> {
  match input
  { Exp::Call(call, lives)  => {
      let liveset : HashSet<RegConflict> = lives.into_iter()
                                                .filter(|&r| loc_is_reg(r))
                                                .map(|r| reg_to_conflict(*r))
                                                .collect();
      let mut target_liveset = triv(call, gs, nm);
      add_conflicts(&target_liveset, &liveset, gs, nm);

      return target_liveset.union(&liveset)
                           .map(|live| live.clone())
                           .collect();
    }
  , Exp::If(test, con, alt) => {
      let con_liveset = exp(&*con, gs, nm);
      let alt_liveset = exp(&*alt, gs, nm);
      return pred(test, con_liveset, alt_liveset, gs, nm);
    }
  , Exp::Begin(effs, tail)   => {
      let liveset = exp(&*tail, gs, nm);
      return effects(effs, liveset, gs, nm);
    }
  }
}

fn pred( input : &Pred, con_lives : HashSet<RegConflict>, alt_lives : HashSet<RegConflict>
       , gs : &mut Graph<RegConflict, (), Undirected>, nm : &mut HashMap<RegConflict, NodeIndex>) -> HashSet<RegConflict> {
  match input
  { Pred::True                  => con_lives.union(&alt_lives).map(|e| e.clone()).collect()
  , Pred::False                 => con_lives.union(&alt_lives).map(|e| e.clone()).collect()
  , Pred::Op(_op, triv1, triv2)  => {
      let mut triv1_lives = triv(triv1, gs, nm);
      let mut triv2_lives = triv(triv2, gs, nm);

      add_conflicts(&triv1_lives, &triv2_lives, gs, nm);

      return con_lives.union(&alt_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                      .union(&triv1_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                      .union(&triv2_lives).map(|e| e.clone()).collect();
    }
  , Pred::If(test, conseq, alt) => {
      let mut new_con_liveset = pred(&*conseq, con_lives.clone(), alt_lives.clone(), gs, nm);
      let mut new_alt_liveset = pred(&*alt, con_lives.clone(), alt_lives.clone(), gs, nm);
      return pred(&*test, new_con_liveset, new_alt_liveset, gs, nm);
    }
  , Pred::Begin(effs, test)     => {
      let new_lives = pred(test, con_lives, alt_lives, gs, nm);
      return effects(effs, new_lives, gs, nm); // TODO Gross. Better option?
    }
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
  { Effect::SetOp(dest, (_op, src1, src2)) => {
      let mut dest_lives = triv(dest, gs, nm);
      add_conflicts(&dest_lives, &liveset, gs, nm);

      let mut src1_lives = triv(src1, gs, nm);
      let mut src2_lives = triv(src2, gs, nm);

      return liveset.difference(&dest_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src1_lives).map(|e| e.clone()).collect::<HashSet<_>>()
                    .union(&src2_lives).map(|e| e.clone()).collect();
    }
  , Effect::Set(dest, src)                => {
      let mut dest_lives = triv(dest, gs, nm);
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
  , Effect::ReturnPoint(_lbl, e, _size)   => exp(e, gs, nm)
  , Effect::If(test, conseq, alt)         => {
      let con_lives = effect(conseq, liveset.clone(), gs, nm);
      let alt_lives = effect(alt, liveset.clone(), gs, nm);
      return pred(test, con_lives, alt_lives, gs, nm);
    }
  , Effect::Begin(effs)                   => effects(effs, liveset, gs, nm)
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
fn as_node( input : &RegConflict
          , conflicts : &mut Graph<RegConflict, (), Undirected>
          , node_map : &mut HashMap<RegConflict, NodeIndex>) 
          -> NodeIndex 
{ if node_map.contains_key(input) {
    return node_map.get(input).unwrap().clone();
  } else {
    let new_index = conflicts.add_node(input.clone());
    node_map.insert(input.clone(), new_index);
    return new_index;
  }
}

fn add_conflicts( conflict1 : &HashSet<RegConflict>, conflict2 : &HashSet<RegConflict>
                , conflicts : &mut Graph<RegConflict, (), Undirected>, nmap : &mut HashMap<RegConflict, NodeIndex>) {
  let new_nodes_c1 : HashSet<_> = conflict1.into_iter().map(|&n| as_node(&n, conflicts, nmap)).collect();
  let new_nodes_c2 : HashSet<_> = conflict2.into_iter().map(|&n| as_node(&n, conflicts, nmap)).collect();
  for node1 in new_nodes_c1 {
    for node2 in new_nodes_c2.clone() {
      conflicts.add_edge(node1, node2, ());
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
    }
  }

  pub fn test1() -> Program {

    let x0 = mk_uvar("x");
    let x1 = mk_uvar("x");
    let x2 = mk_uvar("x");
    let x3 = mk_uvar("x");
    let y4 = mk_uvar("y");

    let z6 = mk_uvar("z");


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
