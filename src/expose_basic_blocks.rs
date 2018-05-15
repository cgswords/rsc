// PASS    | expose-basic-blocks
// ---------------------------------------------------------------------------
// USAGE   | Unravels the basic blocks of each program into additional 
//         | bindings, exposing each individual basic block
// ---------------------------------------------------------------------------
// RETURNS | A pre-flattened, block-exposed program
// ---------------------------------------------------------------------------
// DESCRIPTION
// ---------------------------------------------------------------------------
// This pass performs a backwards walk across each binding body (and main 
// body) of the program, hoisting out basic blocks and replacing them with
// jumps, resulting in a program with basic blocks as top-level bindings and
// control flow as jumps between them.
// ---------------------------------------------------------------------------

use util::Binop;
use util::Relop;
use util::unique_label;
use util::Label;

use flatten_program::Program  as FPProgram;
use flatten_program::Letrec   as FPLetrec;
use flatten_program::Exp      as FPExp;
use flatten_program::Effect   as FPEffect;
use flatten_program::Location as FPLoc;
use flatten_program::Triv     as FPTriv;

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
  { SetOp(Location, (Binop, Triv, Triv))
  , Set(Location, Triv)
  , Nop
  , ReturnPoint(Label, Exp)
  , If(Pred, Box<Effect>, Box<Effect>)
  , Begin(Box<Vec<Effect>>, Box<Effect>)
  }

#[derive(Debug)]
pub enum Location 
  { Reg(String)
  , DisplaceOperand(String, i64) // base register and offset value
  , IndexOperand(String, String) // base register and offset register
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
// pub enum Program { Letrec(Vec<Letrec>, Exp) }
// 
// pub enum Letrec { Entry(Label,Exp) }
// 
// pub enum Label { Label(String) }
// 
// pub enum Exp 
//   { Call(Triv)
//   , If(Relop,Triv,Triv,Label,Label)
//   , Begin(Vec<Effect>,Box<Exp>)
//   }
// 
// pub enum Effect
//   { SetOp(Location, (Binop, Triv, Triv))
//   , Set(Location, Triv)
//   }
// 
// pub enum Location 
//   { Reg(String)
//   , DisplaceOperand(String, i64) // base register and offset value
//   , IndexOperand(String, String) // base register and offset register
//   }
// 
// pub enum Triv 
//   { Loc(Location) 
//   , Num(i64) 
//   , Label(Label)
//   }

// ---------------------------------------------------------------------------
// IMPLEMENTATION
// ---------------------------------------------------------------------------
pub fn expose_basic_blocks(input : Program) -> FPProgram {
  match input {
    Program::Letrec(letrecs, body) => {
      let mut output_letrec = Vec::new();
      for binding in letrecs {
        output_letrec.append(&mut letrec_entry(binding));
      }
      let (new_body, mut body_bindings) = exp(body);
      output_letrec.append(&mut body_bindings);

      return FPProgram::Letrec(output_letrec,new_body);
    }
  }
}

fn letrec_entry(input : Letrec) -> Vec<FPLetrec> {
  match input
  { Letrec::Entry(lbl,rhs) => 
    { let (new_rhs, mut new_bindings) = exp(rhs);

      let mut output_letrec = Vec::new();
      output_letrec.push(FPLetrec::Entry(lbl, new_rhs));
      output_letrec.append(&mut new_bindings);

      return output_letrec;
    }
  }
} 

fn exp(input : Exp) -> (FPExp, Vec<FPLetrec>) {
  return match input 
  { Exp::Call(t)               => (FPExp::Call(triv(t)),Vec::new())
  , Exp::If(test, conseq, alt) => 
    { let con_label = unique_label("C");
      let alt_label = unique_label("A");

      let (pred_body, mut pred_bindings) = pred(test, con_label.clone(), alt_label.clone());
      let (con_body, mut con_bindings) = exp(*conseq);
      let (alt_body, mut alt_bindings) = exp(*alt);

      let mut output_letrec = Vec::new();
      output_letrec.append(&mut pred_bindings);
      output_letrec.push(FPLetrec::Entry(con_label, con_body));
      output_letrec.append(&mut con_bindings);
      output_letrec.push(FPLetrec::Entry(alt_label, alt_body));
      output_letrec.append(&mut alt_bindings);

      return (pred_body, output_letrec);
    }
  , Exp::Begin(effects, last) => 
    { let (body, mut body_bindings) = exp(*last);
      let (effs, mut effs_bindings) = effect_star(effects, body, &mut Vec::new());
      
      let mut output_letrec = Vec::new();
      output_letrec.append(&mut body_bindings);
      output_letrec.append(&mut effs_bindings);

      return (effs, output_letrec);
    }
  }
}

fn mk_fp_call(lbl : Label) -> FPExp {
  return FPExp::Call(FPTriv::Label(lbl));
}

fn pred(input : Pred, con_lbl : Label, alt_lbl : Label) -> (FPExp, Vec<FPLetrec>) {
  return match input 
  { Pred::True => (mk_fp_call(con_lbl), Vec::new())
  , Pred::False => (mk_fp_call(alt_lbl), Vec::new())
  , Pred::Op(op,t1,t2) => (FPExp::If(op, triv(t1), triv(t2), con_lbl, alt_lbl), Vec::new())
  , Pred::If(test, conseq, alt) =>
    { let new_con_label = unique_label("C");
      let new_alt_label = unique_label("A");

      let (pred_body, mut pred_bindings) = pred(*test, new_con_label.clone(), new_alt_label.clone());
      let (con_body, mut con_bindings) = pred(*conseq, con_lbl.clone(), alt_lbl.clone());
      let (alt_body, mut alt_bindings) = pred(*alt, con_lbl, alt_lbl);

      let mut output_letrec = Vec::new();
      output_letrec.append(&mut pred_bindings);
      output_letrec.push(FPLetrec::Entry(new_con_label, make_begin(con_body)));
      output_letrec.append(&mut con_bindings);
      output_letrec.push(FPLetrec::Entry(new_alt_label, make_begin(alt_body)));
      output_letrec.append(&mut alt_bindings);

      return (pred_body, output_letrec);
    }
  , Pred::Begin(effects, body) => {
      let (pred_body, mut pred_bindings) = pred(*body, con_lbl, alt_lbl);
      return effect_star(effects, pred_body, &mut pred_bindings);
    }
  }
}

fn make_begin(input : FPExp) -> FPExp {
  // TODO: Do we need this?
  return input; 
}

// This would be nicer with tail recursion...
fn effect_star(input : Vec<Effect>, last : FPExp, input_bindings : &mut Vec<FPLetrec>) -> (FPExp, Vec<FPLetrec>) {
  let mut bindings = Vec::new();
  bindings.append(input_bindings);

  let mut effects : Vec<Effect> = input.into_iter().rev().collect();
  let mut tail = last;

  while (effects.is_empty() == false) {
    if let Some(effect) = effects.pop() {
      match effect 
      { Effect::SetOp(location, (bop, t1, t2)) => 
        { tail = FPExp::Begin(vec![FPEffect::SetOp(loc(location), (bop, triv(t1), triv(t2)))], Box::new(tail));  }
      , Effect::Set(location,trivial) => 
        { tail = FPExp::Begin(vec![FPEffect::Set(loc(location), triv(trivial))], Box::new(tail)); }
      , Effect::Nop => {}
      , Effect::ReturnPoint(lbl, rhs) =>
        { let (new_tail, mut tail_bindings) = exp(rhs);
          bindings.append(&mut tail_bindings);
          bindings.push(FPLetrec::Entry(lbl, make_begin(tail)));
          tail = new_tail;
        }
      , Effect::If(test, conseq, alt) => 
        { let new_con_label = unique_label("C");
          let new_alt_label = unique_label("A");
          let new_phi_label = unique_label("PHI");
          let (pred_body, mut pred_bindings) = pred(test, new_con_label.clone(), new_alt_label.clone());

          let (con_body, mut con_bindings) = effect_star(vec![*conseq], mk_fp_call(new_phi_label.clone()), &mut Vec::new());
          let (alt_body, mut alt_bindings) = effect_star(vec![*alt], mk_fp_call(new_phi_label.clone()), &mut Vec::new());

          bindings.append(&mut pred_bindings);
          bindings.push(FPLetrec::Entry(new_con_label, make_begin(con_body)));
          bindings.append(&mut con_bindings);
          bindings.push(FPLetrec::Entry(new_alt_label, make_begin(alt_body)));
          bindings.append(&mut alt_bindings);
          bindings.push(FPLetrec::Entry(new_phi_label, make_begin(tail)));

          tail = pred_body;
        }
      , Effect::Begin(mut effs, eff) => 
        { 
          effects.append(&mut effs);
          effects.push(*eff);
        }
      }
    }
  }

  return (make_begin(tail), bindings);
}

fn loc(input : Location) -> FPLoc {
  return match input 
  { Location::Reg(s)                => FPLoc::Reg(s)
  , Location::DisplaceOperand(s, n) => FPLoc::DisplaceOperand(s,n)
  , Location::IndexOperand(s1, s2)  => FPLoc::IndexOperand(s1,s2)
  }
}

fn triv(input : Triv) -> FPTriv {
  return match input
  { Triv::Loc(l)   => FPTriv::Loc(loc(l))
  , Triv::Num(n)   => FPTriv::Num(n)
  , Triv::Label(l) => FPTriv::Label(l)
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
           vec![ Letrec::Entry(mk_lbl("X1")
                                   , Exp::If(Pred::Op(Relop::LT ,mk_loc_triv(mk_reg("r9")), mk_loc_triv(mk_reg("r8"))),
                                             Box::new(
                                               Exp::Begin(
                                                 vec![mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_triv(mk_reg("rax")), mk_num_lit(10))]
                                                , Box::new(mk_call("void"))))
                                            , Box::new(
                                                Exp::Begin(
                                                  vec![mk_set_op(mk_reg("rax"), Binop::Plus, mk_loc_triv(mk_reg("rax")), mk_num_lit(10))]
                                                 , Box::new(mk_call("void"))))))
               ]
         , Exp::Begin(
            vec![ mk_set(mk_reg("r9"), mk_num_lit(0))
                , mk_set(mk_reg("r8"), mk_num_lit(1))]
            , Box::new(mk_call("X1"))));
}
