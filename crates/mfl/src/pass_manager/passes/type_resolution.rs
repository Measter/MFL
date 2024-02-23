use tracing::debug_span;

use crate::{
    context::{Context, ItemId, ItemKind},
    pass_manager::{PassContext, PassResult, PassState},
    type_store::emit_type_error_diag,
    Stores,
};

pub fn resolve_signature(
    ctx: &mut Context,
    stores: &mut Stores,
    _: &mut PassContext,
    had_error: &mut bool,
    cur_id: ItemId,
) -> PassResult {
    let _span = debug_span!("Defining struct", ?cur_id);

    let cur_item_header = ctx.get_item_header(cur_id);
    match cur_item_header.kind {
        ItemKind::GenericFunction | ItemKind::Module | ItemKind::StructDef => {
            panic!(
                "ICE: Tried to resolve_signature on a {:?}",
                cur_item_header.kind
            )
        }

        ItemKind::Assert => todo!(),
        ItemKind::Const => todo!(),
        ItemKind::Function => todo!(),
        ItemKind::Memory => {
            if cur_item_header
                .parent
                .is_some_and(|ph| ctx.get_item_header(ph).kind == ItemKind::GenericFunction)
            {
                // These shouldn't be processed at all until instantiation.
                return PassResult::Progress(PassState::Done);
            }

            let memory_type_unresolved = ctx.nrir().get_memory_type(cur_id);
            let info = match stores
                .types
                .resolve_type(&mut stores.strings, memory_type_unresolved)
            {
                Ok(info) => info,
                Err(tk) => {
                    *had_error = true;
                    emit_type_error_diag(stores, tk);
                    return PassResult::Error;
                }
            };

            ctx.trir_mut().set_memory_type(cur_id, info.id);
        }
    }
    todo!()
}
