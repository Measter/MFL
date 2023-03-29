use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::program::{ItemId, Program};

pub struct Interners {
    lexemes: Rodeo,

    symbols: HashMap<ItemId, Spur>,
}

impl Interners {
    pub fn new() -> Self {
        Interners {
            lexemes: Rodeo::default(),
            symbols: HashMap::new(),
        }
    }

    pub fn intern_literal(&mut self, literal: &str) -> Spur {
        self.lexemes.get_or_intern(literal)
    }

    pub fn intern_lexeme(&mut self, lexeme: &str) -> Spur {
        self.lexemes.get_or_intern(lexeme)
    }

    pub fn resolve_literal(&self, id: Spur) -> &str {
        self.lexemes.resolve(&id)
    }

    pub fn resolve_lexeme(&self, id: Spur) -> &str {
        self.lexemes.resolve(&id)
    }

    pub fn get_symbol_name(&mut self, program: &Program, id: ItemId) -> &str {
        if let Some(name) = self.symbols.get(&id) {
            return self.lexemes.resolve(name);
        }

        let mut parts = Vec::new();

        let item = program.get_item_header(id);
        parts.push(self.lexemes.resolve(&item.name().lexeme));

        let mut parent = item.parent();
        while let Some(parent_id) = parent {
            let item = program.get_item_header(parent_id);
            parts.push(self.lexemes.resolve(&item.name().lexeme));
            parent = item.parent();
        }

        // There'll be at least one.
        let mut name = parts.pop().unwrap().to_owned();

        while let Some(part) = parts.pop() {
            name.push('$');
            name.push_str(part);
        }

        let spur = self.intern_lexeme(&name);
        self.symbols.insert(id, spur);

        self.resolve_lexeme(spur)
    }
}
