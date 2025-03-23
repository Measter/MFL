use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::items::ItemId;

pub struct StringStore {
    lexemes: Rodeo,
    escaped_strings: HashMap<Spur, String>,
    friendly_names: HashMap<ItemId, Spur>,
    mangled_names: HashMap<ItemId, Spur>,
    // Only used in the log traces, if the friendly name doesn't exist.
    fallback_symbol_names: HashMap<ItemId, Spur>,
}

impl StringStore {
    pub fn new() -> Self {
        StringStore {
            lexemes: Rodeo::default(),
            escaped_strings: HashMap::new(),
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
    pub fn is_escaped(&self, id: Spur) -> bool {
        self.escaped_strings.contains_key(&id)
    }

    #[inline]
    pub fn set_escaped_string(&mut self, id: Spur, string: String) {
        let prev = self.escaped_strings.insert(id, string);
        if prev.is_some() {
            panic!("ICE: Tried to set escaped string twice");
        }
    }

    #[inline]
    pub fn get_escaped_string(&self, id: Spur) -> &str {
        self.escaped_strings.get(&id).unwrap()
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

pub fn escape_string_or_char_literal(string: &str, is_string: bool) -> String {
    let mut escaped = String::with_capacity(string.len());
    let mut chars = string.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            escaped.push(ch);
            continue;
        }
        let next_ch = chars.next().unwrap();
        let real = match next_ch {
            '\'' if !is_string => '\'',
            '\"' if is_string => '\"',
            '\\' => '\\',
            'r' => '\r',
            'n' => '\n',
            't' => '\t',
            '0' => '\0',
            _ => unreachable!(),
        };
        escaped.push(real);
    }

    escaped
}
