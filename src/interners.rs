use std::collections::HashMap;

use lasso::{Rodeo, Spur};

use crate::program::{ProcedureId, Program};

pub struct Interners {
    lexemes: Rodeo,

    symbols: HashMap<ProcedureId, Spur>,
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

    pub fn get_symbol_name(&mut self, program: &Program, id: ProcedureId) -> &str {
        if let Some(name) = self.symbols.get(&id) {
            return self.lexemes.resolve(name);
        }

        let proc = program.get_proc_header(id);
        let module = program.get_module(proc.module());
        let proc_name = self.lexemes.resolve(&proc.name().lexeme);
        let module_name = self.lexemes.resolve(&module.name());

        let name = format!("{module_name}${proc_name}");
        let spur = self.intern_lexeme(&name);

        self.resolve_lexeme(spur)
    }
}
