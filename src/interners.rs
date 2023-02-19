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

        let item = program.get_item_header(id);
        let module = program.get_module(item.module());
        let item_name = self.lexemes.resolve(&item.name().lexeme);
        let module_name = self.lexemes.resolve(&module.name());

        let name = format!("{module_name}${item_name}");
        let spur = self.intern_lexeme(&name);

        self.resolve_lexeme(spur)
    }
}
