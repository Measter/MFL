use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::items::ItemId;

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
    pub fn get_friendly_name(&self, item_id: ItemId) -> &str {
        let spur = self.friendly_names[&item_id];
        self.resolve(spur)
    }

    #[inline]
    #[track_caller]
    pub fn try_get_friendly_name(&self, item_id: ItemId) -> Option<Spur> {
        self.friendly_names.get(&item_id).copied()
    }

    #[inline]
    #[track_caller]
    pub fn set_friendly_name(&mut self, item_id: ItemId, name: &str) -> Spur {
        let spur = self.lexemes.get_or_intern(name);
        let prev = self.friendly_names.insert(item_id, spur);

        if prev.is_some() {
            panic!("ICE: Tried to set friendly name twice");
        }
        spur
    }

    #[inline]
    #[track_caller]
    pub fn get_mangled_name(&self, item_id: ItemId) -> &str {
        let spur = self.mangled_names[&item_id];
        self.resolve(spur)
    }

    #[inline]
    #[track_caller]
    pub fn try_get_mangled_name(&self, item_id: ItemId) -> Option<Spur> {
        self.mangled_names.get(&item_id).copied()
    }

    #[inline]
    #[track_caller]
    pub fn set_mangled_name(&mut self, item_id: ItemId, name: &str) -> Spur {
        let spur = self.lexemes.get_or_intern(name);
        let prev = self.mangled_names.insert(item_id, spur);

        if prev.is_some() {
            panic!("ICE: Tried to set mangled name twice");
        }
        spur
    }

    #[inline]
    #[track_caller]
    pub fn get_fallback_name(&self, item_id: ItemId) -> &str {
        let spur = self.fallback_symbol_names[&item_id];
        self.resolve(spur)
    }

    #[inline]
    #[track_caller]
    pub fn try_get_fallback_name(&self, item_id: ItemId) -> Option<Spur> {
        self.fallback_symbol_names.get(&item_id).copied()
    }

    #[inline]
    #[track_caller]
    pub fn set_fallback_name(&mut self, item_id: ItemId, name: Spur) -> Spur {
        let prev = self.fallback_symbol_names.insert(item_id, name);

        if prev.is_some() {
            panic!("ICE: Tried to set fallback name twice");
        }
        name
    }
}

impl Default for StringStore {
    fn default() -> Self {
        Self::new()
    }
}
