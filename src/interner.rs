
use string_interner::DefaultStringInterner;
use string_interner::StringInterner;

use std::fmt;
use std::sync::Mutex;

// use std::hash::{Hash, Hasher};

lazy_static! {
  static ref INTERNER : Mutex<StringInterner<usize>> = Mutex::new(DefaultStringInterner::default());
}

#[derive(PartialEq, Eq, Clone, Copy, Hash)]
pub struct Ident { intern_ref : usize }

impl Ident {
  pub fn from_str(input : &str) -> Ident {
    let new_ref = INTERNER.lock().unwrap().get_or_intern(input);
    return Ident { intern_ref : new_ref };
  }

  pub fn to_string(&self) -> String {
    if let Some(s) = INTERNER.lock().unwrap().resolve(self.intern_ref) {
      return s.to_string();
    } else {
      panic!("Tried to look up an uninterned ident. HOW?!");
    }
  }

  pub fn lookup<'a>(&self) -> Option<String> {
    if let Some(s) = INTERNER.lock().unwrap().resolve(self.intern_ref) {
      Some(s.to_owned())
    } else {
      panic!("Tried to look up an uninterned ident. HOW?!");
    }
  }
}

impl fmt::Debug for Ident {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if let Some(s) = self.lookup() {
      write!(f, "{}", s)
    } else {
      write!(f, "uninterned_var")
    }
  }  
}

impl fmt::Display for Ident {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    if let Some(s) = self.lookup() {
      write!(f, "{}", s)
    } else {
      write!(f, "uninterned_var")
    }
  }  
}
