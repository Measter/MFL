use analyzer::ValueStore;
use block::BlockStore;
use lasso::Spur;
use ops::OpStore;
use source::SourceStore;
use strings::StringStore;
use types::TypeStore;

use crate::{
    context::{Context, ItemAttribute, ItemId, ItemKind},
    pass_manager::PassManager,
};

pub mod analyzer;
pub mod block;
pub mod ops;
pub mod source;
pub mod strings;
pub mod types;

pub const MANGLED_PATH_SEP: &str = "$";
pub const MANGLED_GENERIC_OPEN: &str = "$GO$";
pub const MANGLED_GENERIC_CLOSE: &str = "$GC$";
pub const MANGLED_GENERIC_SEP: &str = "_";
pub const MANGLED_ARRAY_OPEN: &str = "$BO$";
pub const MANGLED_ARRAY_CLOSE: &str = "$BC$";
pub const MANGLED_PTR_MULTI: &str = "$PTR$";
pub const MANGLED_PTR_SINGLE: &str = "$SPTR$";

pub const FRENDLY_PATH_SEP: &str = "::";
pub const FRENDLY_GENERIC_OPEN: &str = "(";
pub const FRENDLY_GENERIC_CLOSE: &str = ")";
pub const FRENDLY_GENERIC_SEP: &str = ", ";
pub const FRENDLY_ARRAY_OPEN: &str = "[";
pub const FRENDLY_ARRAY_CLOSE: &str = "]";
pub const FRENDLY_PTR_MULTI: &str = "*";
pub const FRENDLY_PTR_SINGLE: &str = "&";

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

    pub fn build_mangled_name(
        &mut self,
        ctx: &mut Context,
        pass_manager: &mut PassManager,
        item_id: ItemId,
    ) -> Spur {
        let item_header = ctx.get_item_header(item_id);

        if matches!(
            item_header.kind,
            ItemKind::Function | ItemKind::FunctionDecl
        ) && item_header.attributes.contains(ItemAttribute::Extern)
        {
            // No mangling here, just use the bare name.
            let name = self.strings.resolve(item_header.name.inner).to_owned();
            self.strings.set_mangled_name(item_id, &name);

            return item_header.name.inner;
        }

        let mut mangled_name = String::new();
        if let Some(parent_id) = item_header.parent {
            let _ = pass_manager.ensure_build_names(ctx, self, parent_id);

            mangled_name.push_str(self.strings.get_mangled_name(parent_id));
            mangled_name.push_str(MANGLED_PATH_SEP);
        }

        mangled_name.push_str(self.strings.resolve(item_header.name.inner));

        if matches!(item_header.kind, ItemKind::Function)
            && pass_manager
                .ensure_type_resolved_signature(ctx, self, item_id)
                .is_ok()
        {
            let signature = ctx.trir().get_item_signature(item_id);
            if let [first, rest @ ..] = signature.generic_params.as_slice() {
                mangled_name.push_str(MANGLED_GENERIC_OPEN);

                let type_info = self.types.get_type_info(*first);
                let name = self.strings.resolve(type_info.mangled_name);
                mangled_name.push_str(name);

                for &r in rest {
                    let type_info = self.types.get_type_info(r);
                    let name = self.strings.resolve(type_info.mangled_name);
                    mangled_name.push_str(MANGLED_GENERIC_SEP);
                    mangled_name.push_str(name);
                }

                mangled_name.push_str(MANGLED_GENERIC_CLOSE);
            }
        }

        self.strings.set_mangled_name(item_id, &mangled_name)
    }

    // Creates the user-friendly name displayed in the compiler diagnostics.
    pub fn build_friendly_name(
        &mut self,
        ctx: &mut Context,
        pass_manager: &mut PassManager,
        item_id: ItemId,
    ) -> Spur {
        let item_header = ctx.get_item_header(item_id);

        let mut friendly_name = String::new();
        if let Some(parent_id) = item_header.parent {
            let _ = pass_manager.ensure_build_names(ctx, self, parent_id);

            friendly_name.push_str(self.strings.get_friendly_name(parent_id));
            friendly_name.push_str(FRENDLY_PATH_SEP);
        }

        friendly_name.push_str(self.strings.resolve(item_header.name.inner));

        if matches!(item_header.kind, ItemKind::Function { .. })
            && pass_manager
                .ensure_type_resolved_signature(ctx, self, item_id)
                .is_ok()
        {
            let signature = ctx.trir().get_item_signature(item_id);
            if let [first, rest @ ..] = signature.generic_params.as_slice() {
                friendly_name.push_str(FRENDLY_GENERIC_OPEN);

                let type_info = self.types.get_type_info(*first);
                let name = self.strings.resolve(type_info.friendly_name);
                friendly_name.push_str(name);

                for &r in rest {
                    let type_info = self.types.get_type_info(r);
                    let name = self.strings.resolve(type_info.friendly_name);
                    friendly_name.push_str(FRENDLY_GENERIC_SEP);
                    friendly_name.push_str(name);
                }

                friendly_name.push_str(FRENDLY_GENERIC_CLOSE);
            }
        }

        self.strings.set_friendly_name(item_id, &friendly_name)
    }
}
