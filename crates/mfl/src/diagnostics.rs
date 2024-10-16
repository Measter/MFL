use stores::{items::ItemId, source::SourceLocation};

use crate::{error_signal::ErrorSignal, stores::diagnostics::Diagnostic, Stores};

pub struct NameCollision {
    pub prev: SourceLocation,
    pub new: SourceLocation,
}

pub fn handle_symbol_redef_error(
    stores: &mut Stores,
    had_error: &mut ErrorSignal,
    item_id: impl Into<Option<ItemId>>,
    prev_def: Option<NameCollision>,
) {
    let Some(coll) = prev_def else {
        return;
    };

    had_error.set();

    let diag = Diagnostic::error(coll.new, "item of that name already exists")
        .with_help_label(coll.prev, "previously defined here");

    if let Some(item) = item_id.into() {
        diag.attached(stores.diags, item);
    } else {
        diag.detached(stores.diags);
    }
}
