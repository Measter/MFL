use std::ops::ControlFlow;

use ariadne::{Color, Label};
use lasso::Spur;
use tracing::debug_span;

use crate::{
    context::{make_symbol_redef_error, Context, ItemId, ItemKind, NameResolvedItemSignature},
    diagnostics,
    ir::UnresolvedIdent,
    pass_manager::PassResult,
    source_file::{Spanned, WithSpan},
    type_store::{
        BuiltinTypes, UnresolvedField, UnresolvedStruct, UnresolvedType, UnresolvedTypeIds,
        UnresolvedTypeTokens,
    },
    Stores,
};

fn resolved_single_ident(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    ident: &UnresolvedIdent,
) -> Result<ItemId, ()> {
    let [first_ident, rest @ ..] = ident.path.as_slice() else {
        unreachable!()
    };

    let mut current_item = if ident.is_from_root {
        let Some(tlm) = ctx.get_top_level_module(first_ident.inner) else {
            let item_name = stores.strings.resolve(first_ident.inner);
            diagnostics::emit_error(
                stores,
                first_ident.location,
                format!("symbol `{item_name}` not found"),
                [Label::new(first_ident.location).with_color(Color::Red)],
                None,
            );
            *had_error = true;
            return Err(());
        };
        tlm
    } else {
        let header = ctx.get_item_header(cur_id);
        let Some(start_item) = ctx.get_visible_symbol(header, first_ident.inner) else {
            // TODO: Handle naming builtins here
            let item_name = stores.strings.resolve(first_ident.inner);
            diagnostics::emit_error(
                stores,
                first_ident.location,
                format!("symbol `{item_name}` not found"),
                [Label::new(first_ident.location).with_color(Color::Red)],
                None,
            );

            *had_error = true;
            return Err(());
        };
        start_item
    };

    let mut last_ident = *first_ident;
    for sub_ident in rest {
        let current_item_header = ctx.get_item_header(current_item);
        if current_item_header.kind != ItemKind::Module {
            diagnostics::emit_error(
                stores,
                sub_ident.location,
                "cannot path into non-module item",
                [
                    Label::new(sub_ident.location).with_color(Color::Red),
                    Label::new(last_ident.location)
                        .with_color(Color::Cyan)
                        .with_message("not a module"),
                ],
                None,
            );
            *had_error = true;
            return Err(());
        }

        let scope = ctx.nrir().get_scope(current_item_header.id);
        let Some(sub_item) = scope.get_symbol(sub_ident.inner) else {
            diagnostics::emit_error(
                stores,
                sub_ident.location,
                "symbol not found",
                [Label::new(sub_ident.location).with_color(Color::Red)],
                None,
            );
            *had_error = true;
            return Err(());
        };

        last_ident = *sub_ident;
        current_item = sub_item;
    }

    Ok(current_item)
}

fn resolve_idents_in_type(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    unresolved_type: &UnresolvedTypeTokens,
    generic_params: Option<&[Spanned<Spur>]>,
) -> Result<UnresolvedTypeIds, ()> {
    let res = match unresolved_type {
        UnresolvedTypeTokens::Simple(unresolved_ident) => {
            let item_name = unresolved_ident
                .path
                .last()
                .expect("ICE: empty unresolved ident");

            let name = stores.strings.resolve(item_name.inner);
            let builtin_name = BuiltinTypes::from_name(name);

            if (unresolved_ident.path.len() > 1
                || unresolved_ident.is_from_root
                || unresolved_ident.generic_params.is_some())
                && builtin_name.is_some()
            {
                // Emit error
                diagnostics::emit_error(
                    stores,
                    unresolved_ident.span,
                    "cannot name builtin with a path",
                    [Label::new(unresolved_ident.span).with_color(Color::Red)],
                    None,
                );
                *had_error = true;
                return Err(());
            }

            if let Some(builtin) = builtin_name {
                UnresolvedTypeIds::SimpleBuiltin(builtin)
            } else if unresolved_ident.path.len() == 1
                && !unresolved_ident.is_from_root
                && unresolved_ident.generic_params.is_none()
                && generic_params
                    .and_then(|t| t.iter().find(|tp| tp.inner == item_name.inner))
                    .is_some()
            {
                UnresolvedTypeIds::SimpleGenericParam(*item_name)
            } else {
                let ident =
                    resolved_single_ident(ctx, stores, had_error, cur_id, unresolved_ident)?;

                match &unresolved_ident.generic_params {
                    Some(params) => {
                        let params: Vec<_> = params
                            .iter()
                            .map(|p| {
                                resolve_idents_in_type(
                                    ctx,
                                    stores,
                                    had_error,
                                    cur_id,
                                    p,
                                    generic_params,
                                )
                            })
                            .collect::<Result<_, _>>()?;

                        UnresolvedTypeIds::GenericInstance {
                            id: ident,
                            id_token: item_name.inner.with_span(unresolved_ident.span),
                            params,
                        }
                    }
                    None => UnresolvedTypeIds::SimpleCustom {
                        id: ident,
                        token: item_name.inner.with_span(unresolved_ident.span),
                    },
                }
            }
        }
        UnresolvedTypeTokens::Array(sub_type, length) => {
            let sub_type =
                resolve_idents_in_type(ctx, stores, had_error, cur_id, sub_type, generic_params)?;
            UnresolvedTypeIds::Array(Box::new(sub_type), *length)
        }
        UnresolvedTypeTokens::Pointer(sub_type) => {
            let sub_type =
                resolve_idents_in_type(ctx, stores, had_error, cur_id, sub_type, generic_params)?;
            UnresolvedTypeIds::Pointer(Box::new(sub_type))
        }
    };

    Ok(res)
}

fn resolve_idents_in_struct_def(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
    def: &UnresolvedStruct,
) -> UnresolvedStruct {
    let mut resolved = UnresolvedStruct {
        name: def.name,
        fields: Vec::new(),
        generic_params: def.generic_params.clone(),
        is_union: def.is_union,
    };

    for field in &def.fields {
        let UnresolvedType::Tokens(field_kind) = &field.kind else {
            unreachable!()
        };

        let Ok(new_kind) = resolve_idents_in_type(
            ctx,
            stores,
            had_error,
            cur_id,
            field_kind,
            def.generic_params.as_deref(),
        ) else {
            *had_error = true;
            continue;
        };

        resolved.fields.push(UnresolvedField {
            name: field.name,
            kind: UnresolvedType::Id(new_kind),
        });
    }

    resolved
}

fn resolve_idents_in_module_imports(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
) {
    let unresolved_imports = ctx.urir().get_scope(cur_id).imports().to_owned();

    for import in unresolved_imports {
        let Ok(resolved_item_id) = resolved_single_ident(ctx, stores, had_error, cur_id, &import)
        else {
            *had_error = true;
            continue;
        };

        let item_name = ctx.get_item_header(resolved_item_id).name;
        let resolved_scope = ctx.nrir_mut().get_scope_mut(cur_id);
        match resolved_scope
            .add_visible_symbol(item_name.inner.with_span(import.span), resolved_item_id)
        {
            Ok(_) => {}
            Err(prev_loc) => {
                *had_error = true;
                make_symbol_redef_error(stores, import.span, prev_loc);
            }
        }
    }
}

pub fn resolve_signature(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut bool,
    cur_id: ItemId,
) -> ControlFlow<(), PassResult> {
    let _span = debug_span!("Ident Resolve Signature", ?cur_id);

    let header = ctx.get_item_header(cur_id);
    match header.kind {
        ItemKind::StructDef => {
            let def = ctx.urir().get_struct(cur_id);
            let resolved = resolve_idents_in_struct_def(ctx, stores, had_error, cur_id, def);
            ctx.nrir_mut().set_struct(cur_id, resolved);
        }
        ItemKind::Memory => {
            let generic_params = match header.parent {
                Some(parent_id)
                    if ctx.get_item_header(parent_id).kind == ItemKind::GenericFunction =>
                {
                    Some(ctx.get_function_template_paramaters(parent_id))
                }
                _ => None,
            };

            let unresolved_memory_type = ctx.urir().get_memory_type(cur_id);

            let Ok(new_kind) = resolve_idents_in_type(
                ctx,
                stores,
                had_error,
                cur_id,
                unresolved_memory_type.inner,
                generic_params,
            ) else {
                *had_error = true;
                return ControlFlow::Break(());
            };

            ctx.nrir_mut().set_memory_type(cur_id, new_kind);
        }
        ItemKind::Module => resolve_idents_in_module_imports(ctx, stores, had_error, cur_id),
        // These are all treated the same.
        ItemKind::Assert | ItemKind::Const | ItemKind::Function | ItemKind::GenericFunction => {
            let unresolved_sig = ctx.urir().get_item_signature(cur_id);

            let generic_params = match header.parent {
                Some(parent_id)
                    if ctx.get_item_header(parent_id).kind == ItemKind::GenericFunction =>
                {
                    Some(ctx.get_function_template_paramaters(parent_id))
                }
                _ => None,
            };

            let mut resolved_sig = NameResolvedItemSignature {
                exit: Vec::new(),
                entry: Vec::new(),
            };

            let mut local_had_error = false;

            for kind in &unresolved_sig.entry.inner {
                let Ok(new_kind) = resolve_idents_in_type(
                    ctx,
                    stores,
                    had_error,
                    cur_id,
                    &kind.inner,
                    generic_params,
                ) else {
                    local_had_error = true;
                    continue;
                };
                resolved_sig.entry.push(new_kind);
            }

            for kind in &unresolved_sig.exit.inner {
                let Ok(new_kind) = resolve_idents_in_type(
                    ctx,
                    stores,
                    had_error,
                    cur_id,
                    &kind.inner,
                    generic_params,
                ) else {
                    local_had_error = true;
                    continue;
                };
                resolved_sig.exit.push(new_kind);
            }

            *had_error |= local_had_error;
            if local_had_error {
                return ControlFlow::Break(());
            }
        }
    }

    ControlFlow::Continue(PassResult::Progress)
}
