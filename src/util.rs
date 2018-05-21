pub use interner::Ident;

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

pub static FRAME_PTR_REG   : &str = "rbp";
pub static ALLOC_PTR_REG   : &str = "r12";
pub static RETURN_ADDR_REG : &str = "r15";
pub static RETURN_VAL_REG  : &str = "rax";

// We're addressing each word, and using 64-bit values,
// so we need to shift by 8
pub const WORD_SIZE       : i64  = 3; 


// We need a way to make new, unique labels. We do this with a static, mutable
// counter.
static mut LABEL_COUNTER : i64 = 0;

fn next_lbl_cnt () -> String {
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


// We also need a way to make new, unique indentifiers. We also do this with a
// static, mutable counter.
static mut UVAR_COUNTER : i64 = 0;

fn next_uvar_cnt () -> String {
  unsafe {
    let output : String = LABEL_COUNTER.to_string();
    LABEL_COUNTER += 1;
    return output;
  }
}

pub fn mk_uvar(var: &str) -> Ident {
    let mut var_str = var.to_string();
    var_str.push_str(&next_uvar_cnt());
    return Ident::from_str(&var_str);
}

// A location is a register or a frame variable. That's all they will ever be.
// Abstracting this allows us to use the same map through multiple passes
// without converting the locations from language to language.
#[derive(Debug, Clone, Copy)]
pub enum Location
  { Reg(Ident)
  , FrameVar(i64) // offset value
  }

// Returns the frame index of frame variable locations
// (and -1 for registers).
pub fn frame_index(l: Location) -> i64 {
  match l 
  { Location::Reg(_)      => -1
  , Location::FrameVar(n) => n
  }  
}

pub fn index_fvar(n : i64) -> Location {
  Location::FrameVar(n)
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
