/* PASS    | generate_x86_64
 * -------------------------------------------------------------
 * USAGE   | Turns an X86Lang program into x86-64 assembly
 * -------------------------------------------------------------
 * RETURNS | A string of the x86-64 code.
 */

use util::Binop;
use util::Relop;
use util::Ident;
use util::FRAME_PTR_REG;
use util::ALLOC_PTR_REG;
use util::RETURN_ADDR_REG;

// ---------------------------------------------------------------------------
// INPUT LANGUAGE
// ---------------------------------------------------------------------------
#[derive(PartialEq,Eq,Debug)]
pub enum X86Exp 
  { ExpLabel(Ident)
  , ExpReg(Ident)
  , ExpDisplace(Ident, i64) // base register and offset value
  , ExpIndex(Ident, Ident) // base register and offset register
  , ExpNum(i64)
  }

#[derive(Debug)]
pub enum X86LangStmt 
  { Lbl(Ident)
  , SetOp(X86Exp, (Binop, X86Exp, X86Exp))
  , SetLoad(X86Exp, X86Exp)
  , IfNot(Relop, X86Exp, X86Exp, X86Exp)
  , If(Relop, X86Exp, X86Exp, X86Exp)
  , Jump(X86Exp) 
  }

// This is where we'd add extra sections for emitting, too,
// like String sections and whatnot.
#[derive(Debug)]
pub enum Program { Program(Vec<X86LangStmt>) }

// ---------------------------------------------------------------------------
// IMPLEMENTATION 
// ---------------------------------------------------------------------------
fn lookup_binop(op : Binop) -> String {
  return match op 
  { Binop::Plus   => String::from("addq")
  , Binop::Minus  => String::from("subq")
  , Binop::Mult   => String::from("imulq")
  , Binop::LogAnd => String::from("andq")
  , Binop::LogOr  => String::from("orq")
  }
}

fn lookup_relop(op : Relop, negated : bool) -> String {
  if negated {
    return match op  
    { Relop::LT    => String::from("jge")
    , Relop::LTEq  => String::from("jg")
    , Relop::Equal => String::from("jne")
    , Relop::GtEq  => String::from("jl")
    , Relop::GT    => String::from("jle")
    };
  } else {
    return match op  
    { Relop::LT    => String::from("jl")
    , Relop::LTEq  => String::from("jle")
    , Relop::Equal => String::from("je")
    , Relop::GtEq  => String::from("jge")
    , Relop::GT    => String::from("jg")
    };
  }
}

fn emit_exp (input: X86Exp) -> String {
  return match input  
  { X86Exp::ExpLabel(s) => format!("{}(%rip)", s) 
  , X86Exp::ExpReg(s) => format!("%{}", s)
  , X86Exp::ExpDisplace(reg, offset) => format!("{}(%{})",offset.to_string(),reg) 
  , X86Exp::ExpIndex(reg, index) => format!("(%{}, %{})", reg, index)
  , X86Exp::ExpNum(n) => n.to_string()
  }
}

fn emit_label(output: &mut String, label: &String) {
  output.push_str(".align 8\n");
  output.push_str(&format!("{}:\n",label));
}

fn emit_op(output: &mut String, op : &String) {
  output.push_str(&format!("    {}\n", op));
}

fn emit_unop(output: &mut String, op : &String, arg : &String) {
  output.push_str(&format!("    {} {}\n",op,arg));
}

fn emit_binop(output: &mut String, op : &String, arg1 : &String, arg2 : &String) {
  output.push_str(&format!("    {} {}, {}\n",op,arg1,arg2));
}

fn emit_jump(output: &mut String, op : &String, arg : X86Exp) {
  output.push_str("    "); 
  output.push_str(op);
  output.push_str(" ");
  match arg
  { X86Exp::ExpLabel(lbl) => { output.push_str(&lbl.to_string()); }
  , _ => { output.push('*'); 
           output.push_str(&emit_exp(arg));
         }
  }
  output.push('\n');
}

fn emit_program(input: Vec<String>) -> String {
  let pushq : String = String::from("pushq");
  let popq : String  = String::from("popq");
  let movq : String  = String::from("movq");
  let leaq : String  = String::from("leaq");

  let mut output = String::new();
  output.push_str(&".globl _scheme_entry\n".to_string());
  emit_label(&mut output, &"_scheme_entry".to_string());
  // At this point,  we set up the registers to return cleanly
  // to our runtime
  emit_unop(&mut output, &pushq, &"%rbx".to_string());
  emit_unop(&mut output, &pushq, &"%rbp".to_string());
  emit_unop(&mut output, &pushq, &"%r12".to_string());
  emit_unop(&mut output, &pushq, &"%r13".to_string());
  emit_unop(&mut output, &pushq, &"%r14".to_string());
  emit_unop(&mut output, &pushq, &"%r15".to_string());
  emit_binop(&mut output, &movq, &"%rdi".to_string(),  &FRAME_PTR_REG.to_string());
  emit_binop(&mut output, &movq, &"%rsi".to_string(),  &ALLOC_PTR_REG.to_string());
  emit_binop(&mut output, &leaq, &"_scheme_exit(%rip)".to_string(),  &RETURN_ADDR_REG.to_string());
  // Now emit the compiled program
  for x in input {
    output.push_str(&x);
  }
  // Now,  emit the code to exit back to our runtime
  emit_label(&mut output, &"_scheme_exit".to_string());
  emit_unop(&mut output, &popq, &"%r15".to_string());
  emit_unop(&mut output, &popq, &"%r14".to_string());
  emit_unop(&mut output, &popq, &"%r13".to_string());
  emit_unop(&mut output, &popq, &"%r12".to_string());
  emit_unop(&mut output, &popq, &"%rbp".to_string());
  emit_unop(&mut output, &popq, &"%rbx".to_string());
  emit_op(&mut output, &"ret".to_string());
 
  return output;
}

fn statement(input : X86LangStmt) -> String {
  let movq : String  = String::from("movq");
  let cmpq : String  = String::from("cmpq");
  let jmp : String  = String::from("jmp");

  let mut output = String::new();
  match input 
  { X86LangStmt::Lbl(s) => { emit_label(&mut output, &s.to_string()); }
  , X86LangStmt::SetOp(dest, (binop, _dest2, source)) =>
      // should probably ensure dest == dest2
      { emit_binop(&mut output, &lookup_binop(binop), &emit_exp(dest), &emit_exp(source)); }
  , X86LangStmt::SetLoad(dest, source) => 
      { emit_binop(&mut output, &movq, &emit_exp(dest), &emit_exp(source)); }
  , X86LangStmt::IfNot(op, t1, t2, dest) =>
      { emit_binop(&mut output, &cmpq, &emit_exp(t2), &emit_exp(t1));
        emit_jump(&mut output, &lookup_relop(op, true), dest);
      }
  , X86LangStmt::If(op, t1, t2, dest) =>
      { emit_binop(&mut output, &cmpq, &emit_exp(t2), &emit_exp(t1));
        emit_jump(&mut output, &lookup_relop(op, false), dest);
      }
  , X86LangStmt::Jump(dest)  =>
      { emit_jump(&mut output, &jmp, dest); }
  }   
  return output;
}

pub fn generate_x86_64 (input: Program) -> String {
  match input {
    Program::Program(stmts) =>
      emit_program(stmts.into_iter().map(|x| statement(x)).collect())
  }
}

// ---------------------------------------------------------------------------
// TESTING
// ---------------------------------------------------------------------------
fn mk_num_lit(n: i64) -> X86Exp {
  return X86Exp::ExpNum(n);
}
fn mk_reg(s: &str) -> X86Exp {
  return X86Exp::ExpReg(Ident::from_str(s));
}
fn mk_exp_lbl(s: &str) -> X86Exp {
  return X86Exp::ExpLabel(Ident::from_str(s));
}
fn mk_lbl(s : &str) -> X86LangStmt {
  return X86LangStmt::Lbl(Ident::from_str(s));
}

pub fn test1() -> Program {

  let rax = Ident::from_str("rax");
  let r8 = Ident::from_str("r8");
  let r9 = Ident::from_str("r9");
  let X2 = Ident::from_str("X2");
  let X3 = Ident::from_str("X3");

  return Program::Program(
     vec![ X86LangStmt::SetLoad(mk_reg("r9"), mk_num_lit(0))    
         , X86LangStmt::SetLoad(mk_reg("r8"), mk_num_lit(1))    
         , X86LangStmt::Jump(mk_exp_lbl("X1"))
         , mk_lbl("X2")
         , X86LangStmt::SetOp(X86Exp::ExpReg(rax),(Binop::Plus,X86Exp::ExpReg(rax),X86Exp::ExpNum(10)))
         , X86LangStmt::Jump(X86Exp::ExpLabel(X3))
         , mk_lbl("X1")
         , X86LangStmt::If(Relop::LT,X86Exp::ExpReg(r9),X86Exp::ExpReg(r8),X86Exp::ExpLabel(X2))
         , X86LangStmt::Jump(X86Exp::ExpLabel(X3))
         , mk_lbl("X3")
         , X86LangStmt::SetOp(X86Exp::ExpReg(rax),(Binop::Plus,X86Exp::ExpReg(rax),X86Exp::ExpNum(10)))
         ]);
}
