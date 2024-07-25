use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::context::{Context, ItemId};

pub struct StringStore {
    lexemes: Rodeo,

    symbols: HashMap<ItemId, Spur>,
}

impl StringStore {
    pub fn new() -> Self {
        StringStore {
            lexemes: Rodeo::default(),
            symbols: HashMap::new(),
        }
    }

    #[inline]
    pub fn intern(&mut self, lexeme: &str) -> Spur {
        self.lexemes.get_or_intern(lexeme)
    }

    #[inline]
    pub fn get(&self, lexeme: &str) -> Spur {
        self.lexemes.get(lexeme).unwrap()
    }

    #[inline]
    pub fn resolve(&self, id: Spur) -> &str {
        self.lexemes.resolve(&id)
    }

    pub fn get_symbol_name(&mut self, ctx: &Context, id: ItemId) -> &str {
        if let Some(name) = self.symbols.get(&id) {
            return self.lexemes.resolve(name);
        }

        let mut parts = Vec::new();

        let item = ctx.get_item_header(id);
        parts.push(self.lexemes.resolve(&item.name.inner));

        let mut parent = item.parent;
        while let Some(parent_id) = parent {
            let item = ctx.get_item_header(parent_id);
            parts.push(self.lexemes.resolve(&item.name.inner));
            parent = item.parent;
        }

        // There'll be at least one.
        let mut name = parts.pop().unwrap().to_owned();

        while let Some(part) = parts.pop() {
            name.push('$');
            name.push_str(part);
        }

        let spur = self.intern(&name);
        self.symbols.insert(id, spur);

        self.resolve(spur)
    }
}
