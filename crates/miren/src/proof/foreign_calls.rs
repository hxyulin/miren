//! Resolve narrow Rust foreign declarations to actual compiler-exported Rust bodies.
use super::*;
use rustc_attr_ir::Linkage;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::middle::exported_symbols::{ExportedSymbol, SymbolExportKind};

fn strong_linkage(linkage: Option<Linkage>) -> bool {
    match linkage {
        None | Some(Linkage::External) => true,
        Some(
            Linkage::AvailableExternally
            | Linkage::Common
            | Linkage::ExternalWeak
            | Linkage::Internal
            | Linkage::LinkOnceAny
            | Linkage::LinkOnceODR
            | Linkage::WeakAny
            | Linkage::WeakODR,
        ) => false,
    }
}

fn unique_body(candidates: &[Option<DefId>]) -> Result<DefId, &'static str> {
    match candidates {
        [Some(id)] => Ok(*id),
        [] => Err("no compiler-exported Rust definition matches the foreign symbol"),
        [None] => Err("foreign symbol export has no ordinary Rust function body"),
        _ => Err("multiple compiler exports match the foreign symbol"),
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn foreign_rust_target(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<Option<ty::Instance<'tcx>>, String> {
        let declaration = instance.def_id();
        if !self.tcx.is_foreign_item(declaration) {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        if signature.abi() != rustc_abi::ExternAbi::Rust {
            return Err("foreign symbol resolution supports only the Rust ABI".to_owned());
        }
        if !instance.args.is_empty() || signature.c_variadic() {
            return Err("foreign symbol resolution requires a non-generic fixed signature".into());
        }
        if !self.configured_contracts(instance)?.is_empty() {
            return Err(
                "foreign declaration contracts require an explicit declaration model".into(),
            );
        }
        let attrs = self.tcx.codegen_fn_attrs(declaration);
        if !strong_linkage(attrs.import_linkage) || attrs.link_ordinal.is_some() {
            return Err("foreign symbol import is not an ordinary strong Rust binding".into());
        }
        if self.tcx.native_library(declaration).is_some() {
            return Err("foreign symbol belongs to a native library boundary".into());
        }
        let symbol = self.tcx.symbol_name(instance);
        let mut candidates = Vec::new();
        let mut visited = std::collections::HashSet::new();
        let mut exports = 0usize;
        for krate in std::iter::once(LOCAL_CRATE).chain(self.tcx.crates(()).iter().copied()) {
            for (export, info) in self.tcx.exported_non_generic_symbols(krate) {
                exports += 1;
                if exports > 65_536 {
                    return Err("foreign symbol index exceeds the 65536-export budget".into());
                }
                if export.symbol_name_for_local_instance(self.tcx) != symbol {
                    continue;
                }
                let candidate = match *export {
                    ExportedSymbol::NonGeneric(id)
                        if info.kind == SymbolExportKind::Text
                            && self.tcx.def_kind(id) == DefKind::Fn
                            && !self.tcx.is_foreign_item(id) =>
                    {
                        Some(id)
                    }
                    ExportedSymbol::NonGeneric(_)
                    | ExportedSymbol::Generic(_, _)
                    | ExportedSymbol::DropGlue(_)
                    | ExportedSymbol::AsyncDropGlueCtorShim(_)
                    | ExportedSymbol::AsyncDropGlue(_, _)
                    | ExportedSymbol::ThreadLocalShim(_)
                    | ExportedSymbol::NoDefId(_) => None,
                };
                // Reexporting the same definition does not create a second implementation.
                if candidate.is_none() || visited.insert(candidate) {
                    candidates.push(candidate);
                }
            }
        }
        let target = unique_body(&candidates).map_err(|reason| {
            self.categorized_error(UnknownCategory::MissingCompilerEvidence, reason.into())
        })?;
        let attrs = self.tcx.codegen_fn_attrs(target);
        if !strong_linkage(attrs.linkage)
            || !(attrs.flags.contains(CodegenFnAttrFlags::NO_MANGLE) || attrs.symbol_name.is_some())
            || !attrs.foreign_item_symbol_aliases.is_empty()
            || !attrs.target_features.is_empty()
        {
            return Err("foreign symbol target lacks an ordinary strong explicit export".into());
        }
        if !target.is_local() && self.tcx.used_crate_source(target.krate).dylib.is_some() {
            return Err("foreign symbol target has a dynamic Rust library source".into());
        }
        if self.tcx.generics_of(target).count() != 0 || !self.tcx.is_mir_available(target) {
            return Err("foreign symbol target lacks retained non-generic Rust MIR".into());
        }
        let target = ty::Instance::mono(self.tcx, target);
        if !call_metadata::callable_signature_compatible(
            self.call_poly_signature(target)?,
            self.call_poly_signature(instance)?,
        ) {
            return Err(
                "foreign symbol target Rust signature does not match the declaration".into(),
            );
        }
        self.record_model(
            declaration,
            &format!(
                "compiler-exported strong Rust symbol {}; executes retained {} MIR",
                symbol,
                self.tcx.def_path_str(target.def_id())
            ),
        );
        Ok(Some(target))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_hir::def_id::CRATE_DEF_ID;

    #[test]
    fn foreign_symbols_need_one_actual_rust_definition() {
        let id = CRATE_DEF_ID.to_def_id();
        assert_eq!(unique_body(&[Some(id)]), Ok(id));
        assert!(unique_body(&[]).is_err());
        assert!(unique_body(&[None]).is_err());
        assert!(unique_body(&[Some(id), None]).is_err());
        assert!(unique_body(&[Some(id), Some(id)]).is_err());
    }

    #[test]
    fn weak_or_nondefining_linkage_cannot_supply_a_foreign_body() {
        assert!(strong_linkage(None));
        assert!(strong_linkage(Some(Linkage::External)));
        for linkage in [
            Linkage::AvailableExternally,
            Linkage::Common,
            Linkage::ExternalWeak,
            Linkage::Internal,
            Linkage::LinkOnceAny,
            Linkage::LinkOnceODR,
            Linkage::WeakAny,
            Linkage::WeakODR,
        ] {
            assert!(!strong_linkage(Some(linkage)), "{linkage:?}");
        }
    }
}
