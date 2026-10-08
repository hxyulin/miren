//! Keep the compiler's actual exported symbol index in metadata-only analysis builds.
use rustc_interface::interface;
use rustc_middle::middle::exported_symbols::{ExportedSymbol, SymbolExportInfo};
use rustc_middle::query::LocalCrate;
use rustc_middle::ty::TyCtxt;

pub(super) fn retain(config: &mut interface::Config) {
    config.override_queries = Some(|_, providers| {
        providers.queries.reachable_non_generics =
            |tcx, _| rustc_codegen_ssa::back::symbol_export::reachable_non_generics_helper(tcx);
        providers.queries.exported_non_generic_symbols = exported_symbols;
    });
}

fn exported_symbols<'tcx>(
    tcx: TyCtxt<'tcx>,
    _: LocalCrate,
) -> &'tcx [(ExportedSymbol<'tcx>, SymbolExportInfo)] {
    rustc_codegen_ssa::back::symbol_export::exported_non_generic_symbols_helper(tcx)
}
