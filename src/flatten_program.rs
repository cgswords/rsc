// PASS    | flatten-program
// ---------------------------------------------------------------------------
// USAGE   | Flattens the result of exposing basic blocs into a
//         | program ready to be turned into x86-64 assembly
// ---------------------------------------------------------------------------
// RETURNS | An x86Lang program
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass flattens out the now slightly nested structure of our source
// language into one that more closely resembles assembly language, no letrec,
// no begin forms, calls turned into explicit jumps, and the names of
// procedures turned into label forms. It produces a single code form
// containing a sequence of labels, effect expressions, and jumps, with the
// code for the body of the letrec appearing first followed by the body of each
// lambda expression in turn, prefixed by its label.  
// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::Label;

use generate_x86_64::X86Exp;
use generate_x86_64::X86LangStmt;
use generate_x86_64::Program as X86Program;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------
#[derive(Debug)]
pub enum Program { Letrec(Vec<Letrec>, Exp) }

#[derive(Debug)]
pub enum Letrec { Entry(Label,Exp) }

#[derive(Debug)]
pub enum Exp 
  { Call(Triv)
  , If(Relop,Triv,Triv,Label,Label)
  , Begin(Vec<Effect>,Box<Exp>)
  }

#[derive(Debug)]
pub enum Effect
  { SetOp(Location, (Binop, Triv, Triv))
  , Set(Location, Triv)
  }

#[derive(Debug)]
pub enum Location 
  { Reg(String)
  , Displace(String, i64) // Register and Offset
  }

#[derive(Debug)]
pub enum Triv 
  { Loc(Location) 
  , Num(i64) 
  , Label(Label)
  }

// ---------------------------------------------------------------------------
// OUTPUT LANGUAGE
// ---------------------------------------------------------------------------
// pub enum X86Exp
//   { ExpLabel(String)
//   , ExpReg(String)
//   , ExpDisplace(String, i64) // Register and Offset
//   , ExpNum(i64)
//   }
// 
// pub enum X86LangStmt 
//   { Lbl(String)
//   , SetOp(X86Exp, (Binop, X86Exp, X86Exp))
//   , SetLoad(X86Exp, X86Exp)
//   , IfNot(Relop, X86Exp, X86Exp, X86Exp)
//   , If(Relop, X86Exp, X86Exp, X86Exp)
//   , Jump(X86Exp) 
//   }
// 
// pub enum X86Lang { Program(Vec<X86LangStmt>) }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn flatten_program(input : Program) -> X86Program {
  match input {
    Program::Letrec(letrecs, body) => {
      let mut output = Vec::new();
      output.append(&mut exp(body));
      for binding in letrecs {
        output.append(&mut letrec_entry(binding));
      }
      return X86Program::Program(output);
    }
  }
}

fn letrec_entry(input : Letrec) -> Vec<X86LangStmt> {
  match input
  { Letrec::Entry(Label::Label(s),rhs) =>
    { let mut output_vec = exp(rhs);
      output_vec.insert(0,X86LangStmt::Lbl(s));
      return output_vec;
    }
  }
}

// Optional optimization:
// pass in the next label here, and avoid generating jumps with the if branches
// whenever the next label is the appropriate place to jump anyway
// The IfNot form is for flipping labels to allow this even more often
fn exp(input : Exp) -> Vec<X86LangStmt> {
  return match input 
  { Exp::Call(t)                => vec![X86LangStmt::Jump(triv(t))] // Let's hope this isn't an integer trivial
  , Exp::If(op, t1, t2, l1, l2) => vec![X86LangStmt::If(op, triv(t1), triv(t2), label(l1)), X86LangStmt::Jump(label(l2))]
  , Exp::Begin(effects, last)   => 
    { let mut output : Vec<X86LangStmt> = effects.into_iter().map(|e| effect(e)).collect();
      output.append(&mut exp(*last));
      return output;
    }
  }
}

fn effect(input : Effect) -> X86LangStmt {
  return match input 
  { Effect::SetOp(location, (binop, t1, t2)) => X86LangStmt::SetOp(loc(location), (binop, triv(t1), triv(t2)))
  , Effect::Set(location, trivial) => X86LangStmt::SetLoad(loc(location),triv(trivial))
  }
}

fn loc(input : Location) -> X86Exp {
  return match input 
  { Location::Reg(s)        => X86Exp::ExpReg(s)
  , Location::Displace(s,n) => X86Exp::ExpDisplace(s,n)
  }
}

fn triv(input : Triv) -> X86Exp {
  return match input
  { Triv::Loc(l)   => loc(l)
  , Triv::Num(n)   => X86Exp::ExpNum(n)
  , Triv::Label(l) => label(l) 
  } 
}

fn label(input : Label) -> X86Exp {
  return match input { 
    Label::Label(s) => X86Exp::ExpLabel(s)
  }
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------
fn mk_num_lit(n: i64) -> Triv {
  return Triv::Num(n);
}
fn mk_reg(s: &str) -> Location {
  return Location::Reg(s.to_string());
}
fn mk_call(s: &str) -> Exp {
  return Exp::Call(Triv::Label(mk_lbl(s)));
}
fn mk_lbl(s : &str) -> Label {
  return Label::Label(s.to_string());
}
fn mk_set_op(dest: Location, op: Binop, t1 : Triv, t2: Triv) -> Effect {
  return Effect::SetOp(dest, (op, t1, t2));
}

fn mk_loc_triv(l : Location) -> Triv {
  return Triv::Loc(l);
}

fn mk_set(dest: Location, val: Triv) -> Effect {
  return Effect::Set(dest,val)
}

pub fn test1() -> Program {
  return Program::Letrec(
           vec![ Letrec::Entry(mk_lbl("X2")
                                   , Exp::Begin(
                                        vec![mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_triv(mk_reg("rax")), mk_num_lit(10))]
                                       , Box::new(mk_call("X3"))))
               , Letrec::Entry(mk_lbl("X1")
                                   , Exp::If(Relop::LT ,mk_loc_triv(mk_reg("r9")), mk_loc_triv(mk_reg("r8")), 
                                             mk_lbl("X2"),mk_lbl("X3")))
               , Letrec::Entry(mk_lbl("X3")
                                   , Exp::Begin(
                                        vec![mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_triv(mk_reg("rax")), mk_num_lit(10))]
                                       , Box::new(mk_call("void"))))
               ] 
         , Exp::Begin(
            vec![ mk_set(mk_reg("r9"), mk_num_lit(0)) 
                , mk_set(mk_reg("r8"), mk_num_lit(1))]
            , Box::new(mk_call("X1"))));
}
