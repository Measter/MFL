use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::option::OptionExt;

use super::item::ItemId;

pub struct StringStore {
    lexemes: Rodeo,
    pub(super) friendly_names: HashMap<ItemId, Spur>,
    pub(super) mangled_names: HashMap<ItemId, Spur>,
    // Only used in the log traces, if the friendly name doesn't exist.
    pub(super) fallback_symbol_names: HashMap<ItemId, Spur>,
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
}
