use lasso::Spur;
use type_store::{TypeId, TypeStore};

use crate::{interners::Interner, source_file::SourceStorage};

pub mod type_store;

pub struct Stores {
    pub source: SourceStorage,
    pub strings: Interner,
    pub types: TypeStore,
}

impl Stores {
    pub fn build_mangled_name(&mut self, inner: lasso::Spur, generic_params: &[TypeId]) -> Spur {
        let mut name = self.strings.resolve(inner).to_owned();
        name.push_str("$GO$");
        let [first, rest @ ..] = generic_params else {
            unreachable!()
        };

        let first_ti = self.types.get_type_info(*first);
        name.push_str(self.strings.resolve(first_ti.name));

        for tn in rest {
            name.push('_');
            let tn_ti = self.types.get_type_info(*tn);
            name.push_str(self.strings.resolve(tn_ti.name));
        }

        name.push_str("$GC$");
        self.strings.intern(&name)
    }
}
