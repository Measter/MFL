use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::{
    item_store::{ItemId, ItemStore},
    option::OptionExt,
    stores::FRENDLY_PATH_SEP,
};

pub struct StringStore {
    lexemes: Rodeo,
    friendly_names: HashMap<ItemId, Spur>,
    mangled_names: HashMap<ItemId, Spur>,
    // Only used in the log traces, if the friendly name doesn't exist.
    fallback_symbol_names: HashMap<ItemId, Spur>,
}

impl StringStore {
    pub fn new() -> Self {
        StringStore {
            lexemes: Rodeo::default(),
            friendly_names: HashMap::new(),
            mangled_names: HashMap::new(),
            fallback_symbol_names: HashMap::new(),
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

    #[inline]
    #[track_caller]
    pub(crate) fn get_friendly_name(&self, item_id: ItemId) -> &str {
        let spur = self.friendly_names[&item_id];
        self.resolve(spur)
    }

    #[inline]
    #[track_caller]
    pub(crate) fn set_friendly_name(&mut self, item_id: ItemId, name: &str) -> Spur {
        let spur = self.lexemes.get_or_intern(name);
        self.friendly_names
            .insert(item_id, spur)
            .expect_none("ICE: Tried to set friendly name twice");
        spur
    }

    #[inline]
    #[track_caller]
    pub(crate) fn get_mangled_name(&self, item_id: ItemId) -> &str {
        let spur = self.mangled_names[&item_id];
        self.resolve(spur)
    }

    #[inline]
    #[track_caller]
    pub(crate) fn set_mangled_name(&mut self, item_id: ItemId, name: &str) -> Spur {
        let spur = self.lexemes.get_or_intern(name);
        self.mangled_names
            .insert(item_id, spur)
            .expect_none("ICE: Tried to set mangled name twice");
        spur
    }

    #[inline]
    #[track_caller]
    pub(crate) fn get_symbol_name(&mut self, item_store: &ItemStore, item_id: ItemId) -> &str {
        if let Some(&name) = self.friendly_names.get(&item_id) {
            return self.resolve(name);
        } else if let Some(&name) = self.fallback_symbol_names.get(&item_id) {
            return self.resolve(name);
        }

        let mut parts = Vec::new();

        let item = item_store.get_item_header(item_id);
        parts.push(self.resolve(item.name.inner));

        let mut parent = item.parent;
        while let Some(parent_id) = parent {
            let item = item_store.get_item_header(parent_id);
            parts.push(self.resolve(item.name.inner));
            parent = item.parent;
        }

        // There'll be at least one part.o
        let mut name = parts.pop().unwrap().to_owned();
        while let Some(part) = parts.pop() {
            name.push_str(FRENDLY_PATH_SEP);
            name.push_str(part);
        }

        let spur = self.intern(&name);
        self.fallback_symbol_names.insert(item_id, spur);

        self.resolve(spur)
    }
}
