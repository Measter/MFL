use ariadne::{Color, Label};
use stores::items::ItemId;

use crate::{
    diagnostics,
    error_signal::ErrorSignal,
    ir::NameResolvedType,
    pass_manager::{static_analysis::ensure_structs_declared_in_type, PassManager},
    stores::types::TypeKind,
    Stores,
};

pub fn declare_struct(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let def = stores.sigs.nrir.get_struct(cur_id);
    // We check if the name already exists by trying to resolve it.
    if let Ok(existing_info) = stores.types.resolve_type(
        stores.strings,
        &NameResolvedType::SimpleCustom {
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

    let has_generics = !def.generic_params.is_empty();
    let def_name = def.name;

    let friendly_name = stores.build_friendly_name(pass_manager, cur_id);
    let mangled_name = stores.build_mangled_name(pass_manager, cur_id);

    if has_generics {
        stores.types.add_type(
            friendly_name,
            mangled_name,
            def_name.location,
            TypeKind::GenericStructBase(cur_id),
        );
    } else {
        stores.types.add_type(
            friendly_name,
            mangled_name,
            def_name.location,
            TypeKind::Struct(cur_id),
        );
    }
}

pub fn define_struct(
    stores: &mut Stores,
    pass_manager: &mut PassManager,
    had_error: &mut ErrorSignal,
    cur_id: ItemId,
) {
    let def = stores.sigs.nrir.get_struct(cur_id).clone();
    for field in &def.fields {
        // Failure here can be handled by the type resolver.
        ensure_structs_declared_in_type(stores, pass_manager, had_error, &field.kind.inner);
    }

    if !def.generic_params.is_empty() {
        stores
            .types
            .partially_resolve_generic_struct(stores.strings, cur_id, &def);
    } else if let Err(missing_token) =
        stores
            .types
            .define_fixed_struct(stores.strings, cur_id, &def)
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
