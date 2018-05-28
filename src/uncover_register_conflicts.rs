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
use util::frame_index;
use util::index_fvar;

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
use alloc_lang::FrameConflict;

use petgraph::graph::Graph;

use std::collections::HashMap;
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
pub fn assign_frame(input : Program) -> Program {
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
  , RegAllocForm::Unallocated(mut alloc_info, mut locs) => {
      let mut conflicts : Graph<RegConflict, (), Undirected> = Graph::new_undirected();
      let mut node_map  : HashMap<Ident, NodeIndex>          = HashMap::new();

      exp(&body.expression, &node_map, &conflicts);

      aloc_info.register_conflicts = conflicts;
      
      Body { alloc      : RegAllocForm::Unallocated(alloc_info, locs)
           , expression : input.expression }

      // We define each of these so that we don't have to pass the map and graph
      // everywhere. It's a lousy hack, but better than the alternative.

      fn exp(input : &Exp) -> Vec<RegConflict> {
        match input
        { Exp::Call(call, lives)  => 
        , Exp::If(test, con, alt) => {
            let con_liveset = exp(*con);
            let alt_liveset = exp(*alt);
            pred(test, con_liveset, alt_liveset)
          }
        , Exp::Begin(effs, tail)   => {
            let liveset = exp(*tail);
            effects(effs, liveset);
          }
        }
      }

      fn pred(input : &Pred, con_lives : mut Vec<RegConflict>, alt_lives : mut Vec<RegConflict>) -> Vec<RegConflict> {
        match input
        { Pred::True                  => {
            con_lives.append(alt_lives);
            return con_lives;
          }
        , Pred::False                 => {
            con_lives.append(alt_lives);
            return con_lives;
          }
        , Pred::Op(op, triv1, triv2)  => {
            let mut triv1_lives = triv(triv1);
            let mut triv2_lives = triv(triv2);

            add_conflicts(&triv1_lives, &triv2_lives);

            con_lives.append(alt_lives);
            con_lives.append(triv1_lives);
            con_lives.append(triv2_lives);
          }
        , Pred::If(test, conseq, alt) => {
            let mut new_con_liveset = pred(*conseq, con_lives.clone(), alt_lives.clone());
            let mut new_alt_liveset = pred(*alt, con_lives.clone(), alt_lives.clone());
            pred(*test, new_con_liveset, new_alt_liveset);
          }
        , Pred::Begin(effs, test)     => {
            let new_lives = pred(test, con_lives, alt_lives);
            effects(effs, new_lives); // TODO Gross. Better option?
          }
        }
      }

      fn effects(input : &Vec<Effect>, liveset : mut Vec<RegConflict>) -> Vec<RegConflict> {
        let mut cur_liveset = liveset;
        
        // We process the effects from the bottom up to keep track of the
        // live set: everything live is everything used below this effect
        for eff in input.into_iter().reverse() {
          cur_liveset = effect(eff, &cur_liveset);
        }

        cur_liveset
      }

      fn effect(input : &Effect, liveset : mut Vec<RegConflict>) -> Vec<RegConflict> {
        match input
        { Effect::SetOp(dest, (op, src1, src1)) =>
        , Effect::Set(dest, src)                =>
        , Effect::Nop                           =>
        , Effect::MSet(dest, src1, src2)        =>
        , Effect::ReturnPoint(lbl, e, size)     =>
        , Effect::If(text, conseq, alt)         =>
        , Effect::Begin(effs, eff)              =>
        }
      }

      fn triv(input : &Triv) -> Vec<RegConflict> {
        match input
        { Triv::Var(Variable::Uvar(id))               => vec![RegConflict::Var(id)]
        , Triv::Var(Variable::Loc(Location::Reg(id))) => vec![RegConflict::Reg(id)]
        , Triv::Var(_)   => vec![]
        , Triv::Num(_)   => vec![]
        , Triv::Label(_) => vec![]
        , Triv::MRef(triv1, triv2) => {
            let mut triv1_lives = triv(*triv1);
            let mut triv2_lives = triv(*triv2);

            add_conflicts(&triv1_lives, &triv2_lives);
            
            return triv1_lives.append(triv2_lives);
          }
        }
      }
    }
  }
}



// ---------------------------------------------------------------------------

fn lookup(node_map : HashMap<Ident, NodeIndex>, graph : Graph<RegConflict, (), Undirected>, id : Ident) -> NodeIndex {
  if node_map.contains_key(id) {
    node_map.get(id).unwrap()
  } else {
    new_node = graph.add_node(var_to_reg_conflict(id));
    node_map.insert(id, new_node.clone());
    new_node
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
  use alloc_lang::FrameConflict;
  use alloc_lang::fvar_to_conflict;
  use alloc_lang::var_to_frame_conflict;

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

  fn mk_conflict(n : i64) -> FrameConflict { fvar_to_conflict(index_fvar(n)) }

  fn mk_spills_form(input_spills : Vec<Ident>, input_frame_conflicts : Vec<(Ident, Vec<FrameConflict>)>) -> RegAllocInfo
  { RegAllocInfo
    { locals             : Vec::new()
    , unspillables       : Vec::new()
    , spills             : input_spills
    , frame_conflicts    : input_frame_conflicts
    , register_conflicts : Vec::new()
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

    let fc0 = mk_conflict(0);
    let fc1 = mk_conflict(1);
    let fc2 = mk_conflict(2);
    let fc3 = mk_conflict(3);

    let binding1_alloc = 
      mk_spills_form( vec![z9, z10, z11, z12]
                    , vec![ (z5, vec![var_to_frame_conflict(z6), var_to_frame_conflict(z7), fc0])
                          , (z6, vec![var_to_frame_conflict(z5), fc1, fc2])
                          , (z7, vec![var_to_frame_conflict(z5), var_to_frame_conflict(z6), fc3])
                          , (z8, vec![fc3, fc2, fc0])]);


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
