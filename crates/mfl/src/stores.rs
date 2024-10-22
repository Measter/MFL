use block::BlockStore;
use diagnostics::DiagnosticStore;
use item::{ItemAttribute, ItemKind, ItemStore};
use lasso::Spur;
use ops::OpStore;
use signatures::SigStore;
use stores::{items::ItemId, source::SourceStore, strings::StringStore};
use types::TypeStore;
use values::ValueStore;

use crate::{pass_manager::PassManager, timer::Timer};

pub mod block;
pub mod diagnostics;
mod generics;
pub mod item;
pub mod ops;
pub mod signatures;
pub mod types;
pub mod values;

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

pub struct Stores<'source, 'strings, 'types, 'ops, 'blocks, 'values, 'items, 'sigs, 'diags, 'timer>
{
    pub source: &'source mut SourceStore,
    pub strings: &'strings mut StringStore,
    pub types: &'types mut TypeStore,
    pub ops: &'ops mut OpStore,
    pub blocks: &'blocks mut BlockStore,
    pub values: &'values mut ValueStore,
    pub items: &'items mut ItemStore,
    pub sigs: &'sigs mut SigStore,
    pub diags: &'diags mut DiagnosticStore,
    pub timer: &'timer Timer,
}

impl Stores<'_, '_, '_, '_, '_, '_, '_, '_, '_, '_> {
    pub fn build_mangled_name(&mut self, pass_manager: &mut PassManager, item_id: ItemId) -> Spur {
        let item_header = self.items.get_item_header(item_id);

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
            let _ = pass_manager.ensure_build_names(self, parent_id);

            mangled_name.push_str(self.strings.get_mangled_name(parent_id));
            mangled_name.push_str(MANGLED_PATH_SEP);
        }

        mangled_name.push_str(self.strings.resolve(item_header.name.inner));

        if matches!(item_header.kind, ItemKind::Function)
            && pass_manager
                .ensure_type_resolved_signature(self, item_id)
                .is_ok()
        {
            let signature = self.sigs.trir.get_item_signature(item_id);
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
    pub fn build_friendly_name(&mut self, pass_manager: &mut PassManager, item_id: ItemId) -> Spur {
        let item_header = self.items.get_item_header(item_id);

        let mut friendly_name = String::new();
        if let Some(parent_id) = item_header.parent {
            let _ = pass_manager.ensure_build_names(self, parent_id);

            friendly_name.push_str(self.strings.get_friendly_name(parent_id));
            friendly_name.push_str(FRENDLY_PATH_SEP);
        }

        friendly_name.push_str(self.strings.resolve(item_header.name.inner));

        if matches!(item_header.kind, ItemKind::Function { .. })
            && pass_manager
                .ensure_type_resolved_signature(self, item_id)
                .is_ok()
        {
            let signature = self.sigs.trir.get_item_signature(item_id);
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

    #[inline]
    #[track_caller]
    pub fn get_symbol_name(&mut self, item_id: ItemId) -> &str {
        if let Some(name) = self.strings.try_get_friendly_name(item_id) {
            return self.strings.resolve(name);
        } else if let Some(name) = self.strings.try_get_fallback_name(item_id) {
            return self.strings.resolve(name);
        }

        let mut parts = Vec::new();

        let item = self.items.get_item_header(item_id);
        parts.push(self.strings.resolve(item.name.inner));

        let mut parent = item.parent;
        while let Some(parent_id) = parent {
            let item = self.items.get_item_header(parent_id);
            parts.push(self.strings.resolve(item.name.inner));
            parent = item.parent;
        }

        // There'll be at least one part.o
        let mut name = parts.pop().unwrap().to_owned();
        while let Some(part) = parts.pop() {
            name.push_str(FRENDLY_PATH_SEP);
            name.push_str(part);
        }

        let spur = self.strings.intern(&name);
        self.strings.set_fallback_name(item_id, spur);

        self.strings.resolve(spur)
    }
}
