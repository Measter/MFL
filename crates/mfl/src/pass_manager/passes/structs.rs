use ariadne::{Color, Label};
use tracing::debug_span;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    pass_manager::{PassContext, PassResult, PassState},
    type_store::{TypeKind, UnresolvedTypeIds},
    Stores,
};

pub fn declare_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    pass_ctx: &mut PassContext,
    had_error: &mut bool,
    cur_id: ItemId,
) -> PassResult {
    let _span = debug_span!("Declaring struct", ?cur_id);

    let def = ctx.nrir().get_struct(cur_id);
    // We check if the name already exists by trying to resolve it.
    if let Ok(existing_info) = stores.types.resolve_type(
        &mut stores.strings,
        &UnresolvedTypeIds::SimpleCustom {
            id: cur_id,
            token: def.name,
        },
    ) {
        if let Some(loc) = existing_info.location {
            // The user defined the type.
            diagnostics::emit_error(
                stores,
                def.name.location,
                "type with this name already exists",
                [
                    Label::new(def.name.location).with_color(Color::Red),
                    Label::new(loc)
                        .with_color(Color::Cyan)
                        .with_message("already defined here"),
                ],
                None,
            );
        } else {
            // It's a builtin type
            diagnostics::emit_error(
                stores,
                def.name.location,
                "cannot define struct with the name of a primitive",
                [Label::new(def.name.location).with_color(Color::Red)],
                None,
            );
        }

        *had_error = true;
    }

    if def.generic_params.is_some() {
        stores.types.add_type(
            def.name.inner,
            def.name.location,
            TypeKind::GenericStructBase(cur_id),
        );
    } else {
        // Non-generic structs need to wait until the generic structs are defined
        for gen_struct in ctx.get_generic_structs() {
            pass_ctx.add_dependency(
                cur_id,
                PassState::DefineStructs,
                *gen_struct,
                PassState::DefineStructs,
            );
        }

        stores
            .types
            .add_type(def.name.inner, def.name.location, TypeKind::Struct(cur_id));
    }

    PassResult::Progress(PassState::DefineStructs)
}

pub fn define_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    _: &mut PassContext,
    had_error: &mut bool,
    cur_id: ItemId,
) -> PassResult {
    let _span = debug_span!("Defining struct", ?cur_id);

    let def = ctx.nrir().get_struct(cur_id);
    if def.generic_params.is_some() {
        stores
            .types
            .partially_resolve_generic_struct(&mut stores.strings, cur_id, def);
    } else if let Err(missing_token) =
        stores
            .types
            .define_fixed_struct(&mut stores.strings, cur_id, def)
    {
        // The type that failed to resolve is us.
        diagnostics::emit_error(
            stores,
            missing_token.location,
            "undefined field type",
            [
                Label::new(missing_token.location).with_color(Color::Red),
                Label::new(def.name.location)
                    .with_color(Color::Cyan)
                    .with_message("In this struct"),
            ],
            None,
        );
        *had_error = true;
        return PassResult::Error;
    }
    PassResult::Progress(PassState::Done)
}
