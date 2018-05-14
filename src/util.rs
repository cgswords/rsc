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

pub const FRAME_PTR_REG   : &str = "%rbp";
pub const ALLOC_PTR_REG   : &str = "%r12";
pub const RETURN_ADDR_REG : &str = "%r15";
pub const RETURN_VAL_REG  : &str = "%rax";
