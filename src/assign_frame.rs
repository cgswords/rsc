// PASS    | assign_frame
// ---------------------------------------------------------------------------
// USAGE   | assign_frame : assign_frame::Program -> 
//         |                discard_call_live::Program
// ---------------------------------------------------------------------------
// RETURNS | The expression with the spillled variable list discarded, with
//         | spills now being placed onto the frame.
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass walks through the spills, and each spilled variable gets a
// frame location. We update the location vector for each binding to reflect
// these new locations.
//// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;
use util::Ident;
use util::Location;
use util::mk_uvar;
use util::frame_index;

use alloc_lang::Program;
use alloc_lang::Letrec;
use alloc_lang::RegAllocForm;
use alloc_lang::RegAllocInfo;
use alloc_lang::Exp;
use alloc_lang::Pred;
use alloc_lang::Effect;
use alloc_lang::Variable;
use alloc_lang::Triv;
use alloc_lang::Offset;

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
// #[derive(Debug)]
// pub enum RegAllocForm
// 	{ Allocated(HashMap<Ident, Location>)
//  , Unallocated(mut RegAllocInfo, mut HashMap<Ident, Location>)
//  }
// 
// #[derive(Debug)]
// pub struct RegAllocInfo 
//   { locals            : mut Vec<Ident>
//   , unspillables      : mut Vec<Ident>
//   , spills            : mut Vec<Ident>
//   , frame_conflits    : mut Vec<(Ident, mut Vec<Ident>)>
//   , register_conflits : mut Vec<(Ident, mut Vec<Ident>)>
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
// pub enum Offset
//   { UVar(Ident)
//   , Num(i64)
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

fn letrec_entry(input : Letrec) -> LetrecEntry {
  LetrecEntry 
  { label : input.label
  , rhs   : body(rhs)
  }
}

fn body(input: Body) -> Body {
  match input.alloc
  { RegAllocForm::Allocated(_, _)               => Body { alloc : input.alloc , exp : input.exp }
  , RegAllocForm::Unallocated(alloc_info, locs) => {
      let mut new_frame_locs = assign_frame_vars(&locs, &alloc_info.frame_conflicts, &alloc_info.spills);
      locs.append(new_frame_locs);
      alloc_info.spills.clear();
      Body { alloc : RegAllocForm(alloc_info, locs, rhs) , exp : input.exp }
    }
  }
}

fn var_frame_index(v: &FrameConflict) -> i64 {
  match input 
  { FrameConflict::UVar(l)     => -1
  , FrameConflict::FrameVar(i) => i
  }
}

fn max_frame_index(locs : &HashSet<Ident, Location>, conflicts : &Vec<(Ident, Vec<Ident>)) -> i64 {
  let location_max = locs.values().cloned().fold(0, |acc, x| max(acc, frame_index(x)));

  let conflict_max = conflicts.iter().fold(0, |cur_max, (var, conflict)| 
                                                max(cur_max, 
                                                    conflict.iter().fold(0, |acc, x| max(acc, var_frame_index(x)))));

  return max(conflict_max, location_max);
}

fn assign_frame_vars( cur_locs  : &HashMap<Ident, Location>
                    , conflicts : &Vec<(Ident, Vec<Variable>)
                    , spills    : &Vec<Ident>) ->
                    mut HashMap<Ident, location> 
{
    let next_frame_index = max_frame_index(cur_locs, conflicts) + 1;

    let mut result = HashMap::new();

    for spill in spills {
      result.insert(spill, index_fvar(next_frame_index));
      next_frame_index += 1;
    }
     
    result
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------

mod test {

  use alloc_lang::framevar_to_conflict;

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
  
  fn mreft(src : Triv, offset : Triv) -> Triv { Triv::(mk_box!(src), mk_box!(offset)) }

  fn fv(n: i64) -> Triv { return Triv::Var(Variable::Loc(Location::FrameVar(Ident::from_str(s)))); }

  fn reg(s: &str) -> Triv { return Triv::Var(Variable::Loc(Location::Reg(Ident::from_str(s)))); }

  fn mk_lbl(s : &str) -> Label { return Label::Label(s.to_string()); }

  fn mk_spills_form(input_spills : Vec<Ident>, input_frame_conflicts : Vec<(Ident, Vec<Ident>)>) -> RegAllocInfo
  { RegAllocInfo
    { locsl              : Vec::new()
    , unspillables       : Vec::new()
    , spills             : input_spills
    , frame_conflicts    : input_frame_conflicts
    , register_conflicts : Vec::new()
    }
  }

  fn test1() -> Program {

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
    map.insert(x0, mk_loc_reg("rbx"));
    map.insert(x1, Location::FrameVar(2));
    map.insert(x2, mk_loc_reg("r8"));
    map.insert(x3, mk_loc_reg("r9"));
    map.insert(y4, mk_loc_reg("r15"));

    let mut body_map = HashMap::new();
    body_map.insert(x2, mk_loc_reg("r8"));
    body_map.insert(x3, mk_loc_reg("r9"));

    let [fc0, fc1, fc2, fc3] = vec![0, 1, 2, 3, 4].into_iter().map(|e| framevar_to_conflict(index_fvar(e))).collect();

    let binding1_alloc = 
      mk_spills_form( vec![z9, z10, z11, z12]
                    , vec![ (z5, vec![z6, z7, fc0])
                          , (z6, vec![z5, z7, fc1, fc3])
                          , (z7, vec![z5, z6, fc3])
                          , (z8, vec![fc3, fc4])]);


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
                                                          , calle(mk_lbl("X3"), vec![])) ) 
                                             , mset(vt(x0), mreft(reg("rax"), nt(1)))
                                             ]
                                        , calle(mk_lbl("X2"), vec![])))
                                , begine(vec![ setopf(vt(x1), Binop::Plus, vt(x1), nt(35)) ]
                                        , calle(mk_lbl("X2"), vec![]))
              }
      };

    let mut body_map = HashMap::new();
    body_map.insert(x2, mk_loc_reg("r8"));
    body_map.insert(x3, mk_loc_reg("r9"));


    let test_body = 
      Body 
      { alloc : RegAllocForm::Allocated(body_map)
      , expression : begine(vec![ setf(vt(x2), nt(0))
                                , setf(vt(x3), nt(1))
                                ]
                           , calle(mk_lbl("X1"), vec![reg("rax"), reg("rbp")]))
      };

    Program::Letrec(vec![binding1], test_body)
  }

}
