use std::hash::{Hash, Hasher};

static mut INTERNER : DefaultStringInterner::new();

pub Ident { intern_ref : u64 }

pub Ident {
  pub fn from_str(input : &str) -> Ident {
    unsafe {
      let new_ref = INTERNER.get_or_intern(input);
      return Ident { intern_ref : new_ref };
    }
  }

  pub fn lookup(&self) -> String {
    if let Some(s) = INTERNER.resolve(&self.intern_ref) {
      return s.to_string();
    } else {
      panic!("Tried to look up an uninterned ident. HOW?!"):
    }
  }
}
