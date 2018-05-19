
pub use interner::Ident;
use std::hash::{Hash, Hasher};

#[derive(Debug)]
pub enum Binop 
  { Plus
  , Minus
  , Mult
  , LogAnd
  , LogOr
  }

#[derive(Debug)]
pub enum Relop 
  { LT
  , LTEq
  , Equal
  , GtEq
  , GT
  }

#[derive(Debug,Clone, Copy)]
pub struct Label {
  label : Ident  
}

impl Label {
  pub fn new(id : Ident) -> Label {
    Label { label : id }
  }
  
  pub fn to_id(&self) -> Ident {
    self.label 
  }
}

pub const FRAME_PTR_REG   : Ident = Ident::from_str("rbp");
pub const ALLOC_PTR_REG   : Ident = Ident::from_str("r12");
pub const RETURN_ADDR_REG : Ident = Ident::from_str("r15");
pub const RETURN_VAL_REG  : Ident = Ident::from_str("rax");

// We're addressing each word, and using 64-bit values,
// so we need to shift by 8
pub const WORD_SIZE       : i64  = 3; 

static mut LABEL_COUNTER : i64 = 0;

pub fn next_lbl_cnt () -> String {
  unsafe {
    let output : String = LABEL_COUNTER.to_string();
    LABEL_COUNTER += 1;
    return output;
  }
}

pub fn unique_label(label: &str) -> Label {
    let mut label_str = label.to_string();
    label_str.push_str(&next_lbl_cnt());
    return Label::new(Ident::from_str(&label_str));
}

// A variable is a string and number, so that we can number them easily for
// uniqueness. The ids _must_ be unique: it's a large part of how we hash 'em.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct UniqueVar
{ pub name : Ident
, pub id : i64
}

impl UniqueVar {
  pub fn new(new_name : &str, new_id : i64) -> UniqueVar {
    UniqueVar { name : Ident::from_str(new_name), id : new_id }
  }
}

pub fn mk_uvar(new_name : &str, new_id : i64) -> UniqueVar {
  UniqueVar::new(new_name, new_id)
}

impl Hash for UniqueVar {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
    self.id.hash(state);
  }
}

// A location is a register or a frame variable. That's all they will ever be.
// Abstracting this allows us to use the same map through multiple passes
// without converting the locations from language to language.
#[derive(Debug, Clone)]
pub enum Location
  { Reg(Ident)
  , FrameVar(i64) // offset value
  }

// An x86_64 location is one of:
// - a register
// -a displacement operand (a register and offset value)
// - an index operand (a pair of registers)
#[derive(Debug, Clone)]
pub enum X86Loc 
  { Reg(Ident)
  , DisplaceOperand(Ident, i64) // base register and offset value
  , IndexOperand(Ident, Ident) // base register and offset register
  }
