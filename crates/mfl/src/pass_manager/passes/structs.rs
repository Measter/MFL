use ariadne::{Color, Label};

use crate::{
    context::{Context, ItemId},
    diagnostics,
    error_signal::ErrorSignal,
    type_store::{TypeKind, UnresolvedTypeIds},
    Stores,
};

pub fn declare_struct(
    ctx: &mut Context,
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
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

        had_error.set();
    }

    if def.generic_params.is_some() {
        stores.types.add_type(
            def.name.inner,
            def.name.location,
            TypeKind::GenericStructBase(cur_id),
        );
    } else {
        stores
            .types
            .add_type(def.name.inner, def.name.location, TypeKind::Struct(cur_id));
    }
}

pub fn define_struct(
    ctx: &Context,
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
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
        had_error.set();
        return;
    }
}
