
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

#[derive(Debug,Clone)]
pub enum Label { Label(String) }

pub const FRAME_PTR_REG   : &str = "rbp";
pub const ALLOC_PTR_REG   : &str = "r12";
pub const RETURN_ADDR_REG : &str = "r15";
pub const RETURN_VAL_REG  : &str = "rax";

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
    return Label::Label(label_str);
}

// A variable is a string and number, so that we can number them easily for
// uniqueness. The ids _must_ be unique: it's a large part of how we hash 'em.
#[derive(Debug, PartialEq, Eq)]
pub struct UniqueVar 
{ pub name : String
, pub id : i64
}

pub fn mk_uvar(new_name : &str, new_id : i64) -> UniqueVar {
  return UniqueVar { name : new_name.to_string(), id : new_id };
}

impl Hash for UniqueVar {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.name.hash(state);
    self.id.hash(state);
  }
}


