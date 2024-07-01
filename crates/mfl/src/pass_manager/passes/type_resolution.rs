use smallvec::SmallVec;
use tracing::debug_span;

use crate::{
    context::{Context, ItemId, ItemKind, TypeResolvedItemSignature},
    ir::{If, NameResolvedOp, Op, OpCode, TerminalBlock, TypeResolvedOp, While},
    pass_manager::{PassContext, PassState},
    type_store::{emit_type_error_diag, TypeId, UnresolvedTypeIds},
    Stores,
};

pub fn resolve_signature(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
) {
    let _span = debug_span!("Type Resolve Signature", ?cur_id);

    let cur_item_header = ctx.get_item_header(cur_id);
    match cur_item_header.kind {
        ItemKind::GenericFunction | ItemKind::Module | ItemKind::StructDef => {
            panic!(
                "ICE: Tried to resolve_signature on a {:?}",
                cur_item_header.kind
            )
        }

        ItemKind::Assert | ItemKind::Const | ItemKind::Function => {
            let unresolved_sig = ctx.nrir().get_item_signature(cur_id);
            let mut resolved_sig = TypeResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),
            };

            let mut local_had_error = false;

            let mut process_sig = |unresolved: &[UnresolvedTypeIds], resolved: &mut Vec<TypeId>| {
                for kind in unresolved {
                    let info = match stores.types.resolve_type(&mut stores.strings, kind) {
                        Ok(info) => info,
                        Err(tk) => {
                            local_had_error = true;
                            emit_type_error_diag(stores, tk);
                            continue;
                        }
                    };

                    resolved.push(info.id);
                }
            };

            process_sig(&unresolved_sig.entry, &mut resolved_sig.entry);
            process_sig(&unresolved_sig.exit, &mut resolved_sig.exit);

            *had_error |= local_had_error;
            if local_had_error {
                return;
            }

            ctx.trir_mut().set_item_signature(cur_id, resolved_sig);
        }
        ItemKind::Memory => {
            if cur_item_header
                .parent
                .is_some_and(|ph| ctx.get_item_header(ph).kind == ItemKind::GenericFunction)
            {
                // These shouldn't be processed at all until instantiation.
                return;
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
                    return;
                }
            };

            ctx.trir_mut().set_memory_type(cur_id, info.id);
        }
    }
}
