use interner::Interner;
use lasso::Spur;
use ops::OpStore;
use source::SourceStore;
use types::{TypeId, TypeStore};

pub mod interner;
pub mod ops;
pub mod source;
pub mod types;

pub struct Stores {
    pub source: SourceStore,
    pub strings: Interner,
    pub types: TypeStore,
    pub ops: OpStore,
}

impl Stores {
    pub fn new() -> Stores {
        let source_storage = SourceStore::new();
        let mut interner = Interner::new();
        let type_store = TypeStore::new(&mut interner);
        let op_store = OpStore::new();

        Stores {
            source: source_storage,
            strings: interner,
            types: type_store,
            ops: op_store,
        }
    }

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
