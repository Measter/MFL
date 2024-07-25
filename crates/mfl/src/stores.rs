use analyzer::ValueStore;
use block::BlockStore;
use lasso::Spur;
use ops::OpStore;
use source::SourceStore;
use strings::StringStore;
use types::{TypeId, TypeStore};

pub mod analyzer;
pub mod block;
pub mod ops;
pub mod source;
pub mod strings;
pub mod types;

pub struct Stores {
    pub source: SourceStore,
    pub strings: StringStore,
    pub types: TypeStore,
    pub ops: OpStore,
    pub blocks: BlockStore,
    pub values: ValueStore,
}

impl Stores {
    pub fn new() -> Stores {
        let source_storage = SourceStore::new();
        let mut string_store = StringStore::new();
        let type_store = TypeStore::new(&mut string_store);
        let op_store = OpStore::new();
        let block_store = BlockStore::new();
        let value_store = ValueStore::new();

        Stores {
            source: source_storage,
            strings: string_store,
            types: type_store,
            ops: op_store,
            blocks: block_store,
            values: value_store,
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
