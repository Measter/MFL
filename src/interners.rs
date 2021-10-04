use lasso::{Iter, Rodeo, Spur};

pub struct Interners {
    literals: Rodeo,
    lexemes: Rodeo,
}

impl Interners {
    pub fn new() -> Self {
        Interners {
            lexemes: Rodeo::default(),
            literals: Rodeo::default(),
        }
    }

    pub fn intern_literal(&mut self, literal: &str) -> Spur {
        self.literals.get_or_intern(literal)
    }

    pub fn intern_lexeme(&mut self, lexeme: &str) -> Spur {
        self.lexemes.get_or_intern(lexeme)
    }

    pub fn resolve_literal(&self, id: Spur) -> &str {
        self.literals.resolve(&id)
    }

    pub fn iter_literals(&self) -> Iter<'_, Spur> {
        self.literals.iter()
    }
}
