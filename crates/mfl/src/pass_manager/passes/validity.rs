use hashbrown::HashMap;
use stores::items::ItemId;

use crate::{
    error_signal::ErrorSignal,
    pass_manager::PassManager,
    simulate::SimulatorValue,
    stores::{
        diagnostics::Diagnostic,
        item::{ItemAttribute, ItemKind, LangItem},
        Stores,
    },
};

mod cycles;

pub(crate) fn validity_check(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let cur_item_header = stores.items.get_item_header(cur_id);

    match cur_item_header.kind {
        ItemKind::Assert | ItemKind::Const => {
            if pass_manager
                .ensure_ident_resolved_body(stores, cur_id)
                .is_ok()
            {
                cycles::check_invalid_cycles(stores, pass_manager, had_error, cur_id);
            }
            validate_attributes(stores, had_error, cur_id);
        }
        ItemKind::Variable
        | ItemKind::Function
        | ItemKind::FunctionDecl
        | ItemKind::GenericFunction
        | ItemKind::Module => {
            validate_attributes(stores, had_error, cur_id);
        }
        ItemKind::StructDef => {
            if pass_manager
                .ensure_ident_resolved_signature(stores, cur_id)
                .is_ok()
            {
                cycles::check_invalid_cycles(stores, pass_manager, had_error, cur_id);
            }

            validate_attributes(stores, had_error, cur_id);
        }
        ItemKind::Enum => {
            validate_enum_variants(stores, pass_manager, had_error, cur_id);
            validate_attributes(stores, had_error, cur_id);
        }
    }
}
