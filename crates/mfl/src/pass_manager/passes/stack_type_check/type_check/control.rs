use ariadne::{Color, Label};
use intcast::IntCast;

use crate::{
    context::{Context, ItemId},
    diagnostics,
    ir::{Op, TypeResolvedOp},
    pass_manager::static_analysis::{
        can_promote_int_unidirectional, failed_compare_stack_types, Analyzer,
    },
    type_store::TypeKind,
    Stores,
};

pub(crate) fn epilogue_return(
    ctx: &mut Context,
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
    item_id: ItemId,
) {
    let item_urir_sig = ctx.urir().get_item_signature(item_id);
    let item_trir_sig = ctx.trir().get_item_signature(item_id);
    let op_data = analyzer.get_op_io(op.id);

    for (&expected_type_id, &actual_value_id) in item_trir_sig.exit.iter().zip(&op_data.inputs) {
        let Some([actual_type_id]) = analyzer.value_types([actual_value_id]) else {
            continue;
        };

        if actual_type_id != expected_type_id {
            let actual_type_info = stores.types.get_type_info(actual_type_id);
            let expected_type_info = stores.types.get_type_info(expected_type_id);

            if !matches!((actual_type_info.kind, expected_type_info.kind),
                (TypeKind::Integer(actual), TypeKind::Integer(expected))
                if can_promote_int_unidirectional(actual, expected))
            {
                failed_compare_stack_types(
                    stores,
                    analyzer,
                    &op_data.inputs,
                    &item_trir_sig.exit,
                    item_urir_sig.exit.location,
                    op.token.location,
                    "item return stack mismatch",
                );
                *had_error = true;
                break;
            }
        }
    }
    todo!()
}

pub(crate) fn prologue(
    ctx: &mut Context,
    analyzer: &mut Analyzer,
    op: &Op<TypeResolvedOp>,
    item_id: ItemId,
) {
    let op_data = analyzer.get_op_io(op.id);
    let sigs = ctx.trir().get_item_signature(item_id);
    let outputs = op_data.outputs.clone();

    for (output_id, &output_type) in outputs.into_iter().zip(&sigs.entry) {
        analyzer.set_value_type(output_id, output_type);
    }
}

pub(crate) fn syscall(
    stores: &mut Stores,
    analyzer: &mut Analyzer,
    had_error: &mut bool,
    op: &Op<TypeResolvedOp>,
) {
    let op_data = analyzer.get_op_io(op.id);

    for (idx, &input_value_id) in op_data.inputs.iter().enumerate() {
        let Some([input_type_id]) = analyzer.value_types([input_value_id]) else {
            continue;
        };

        let input_type_info = stores.types.get_type_info(input_type_id);
        if matches!(
            input_type_info.kind,
            TypeKind::Integer(_) | TypeKind::Pointer(_) | TypeKind::Bool
        ) {
            continue;
        }

        let type_name = stores.strings.resolve(input_type_info.name);
        let mut labels = diagnostics::build_creator_label_chain(
            analyzer,
            [(input_value_id, idx.to_u64(), type_name)],
            Color::Yellow,
            Color::Cyan,
        );

        labels.push(Label::new(op.token.location).with_color(Color::Red));

        diagnostics::emit_error(
            stores,
            op.token.location,
            "invalid syscall parameter",
            labels,
            None,
        );
        *had_error = true;
    }
}
