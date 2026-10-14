//! Bound raw and selectable pretty-printer paths before owned names are materialized.
use super::*;
use rustc_hir::definitions::{DefKey, DefPathData, DefPathDataName};
use rustc_span::def_id::ModId;
use rustc_span::{Symbol, kw};

pub(super) struct Names<'tcx> {
    original: Ty<'tcx>,
    outer: Ty<'tcx>,
    inner: Ty<'tcx>,
    symbols: [Symbol; 5],
}

fn bounded(bytes: usize) -> Result<usize, String> {
    if bytes > 128 {
        Err("niche codec original display/name exceeds128 bytes".into())
    } else {
        Ok(bytes)
    }
}

fn digits(mut value: u32) -> usize {
    let mut digits = 1;
    while value >= 10 {
        value /= 10;
        digits += 1
    }
    digits
}

fn component(key: &DefKey) -> Result<usize, String> {
    match key.disambiguated_data.data {
        DefPathData::Impl => {
            return Err("niche codec impl display requires separate type formatting plan".into());
        }
        DefPathData::ForeignMod | DefPathData::Ctor => return Ok(0),
        _ => {}
    }
    let disambiguator = key.disambiguated_data.disambiguator;
    bounded(match key.disambiguated_data.data.name() {
        // Include optional raw-identifier prefix and verbose disambiguation, even if omitted.
        DefPathDataName::Named(name) => {
            name.as_str().len()
                + 2
                + if disambiguator == 0 {
                    0
                } else {
                    1 + digits(disambiguator)
                }
        }
        DefPathDataName::Anon { namespace } => {
            namespace.as_str().len()
                + 3
                + digits(disambiguator)
                + match key.disambiguated_data.data {
                    DefPathData::AnonAssocTy(method) => method.as_str().len() + 2,
                    _ => 0,
                }
        }
    })
}

fn raw(engine: &mut Engine<'_>, mut id: DefId) -> Result<usize, String> {
    let mut bytes = 0usize;
    for _ in 0..16 {
        pay(engine, 8)?;
        let key = engine.tcx.def_key(id);
        let Some(parent) = key.parent else {
            pay(engine, 4)?;
            return bounded(bytes + engine.tcx.crate_name(id.krate).as_str().len().max(5));
        };
        let count = component(&key)?;
        if count != 0 {
            bytes = bounded(bytes + count + 2)?
        }
        id.index = parent;
    }
    Err(engine.categorized_error(
        UnknownCategory::ResourceLimit,
        "niche codec display path exceeds16 parents".into(),
    ))
}

fn prefix(engine: &mut Engine<'_>, id: DefId) -> Result<usize, String> {
    pay(engine, 8)?;
    let ordinary = engine.tcx.crate_name(id.krate).as_str().len().max(5);
    let explicit = engine.tcx.extern_crate(id.krate).copied();
    if let Some(external) = explicit
        && external.is_direct()
        && !external.span.is_dummy()
        && let rustc_crate_store::ExternCrateSource::Extern(alias) = external.src
    {
        return Ok(ordinary.max(raw(engine, alias)?));
    }
    bounded(ordinary)
}

fn visible(engine: &mut Engine<'_>, mut id: DefId) -> Result<Option<usize>, String> {
    let mut bytes = 0usize;
    let mut visited = [None; 16];
    for depth in 0..16 {
        if visited[..depth].contains(&Some(id)) {
            return Ok(None);
        }
        visited[depth] = Some(id);
        pay(engine, 16)?;
        if id.as_crate_root().is_some() {
            return Ok(Some(bounded(bytes + prefix(engine, id)?)?));
        }
        // Local paths fall back to their actual definition path in the pinned printer.
        if id.is_local() {
            return Ok(Some(bounded(bytes + raw(engine, id)?)?));
        }
        let key = engine.tcx.def_key(id);
        let parents = engine.tcx.visible_parent_map(());
        let Some(parent) = parents.get(&id).copied() else {
            return Ok(None);
        };
        let mut count = component(&key)?;
        if matches!(key.disambiguated_data.data, DefPathData::TypeNs(_))
            && engine.tcx.opt_parent(id) != Some(parent)
        {
            pay(engine, 8)?;
            let children = engine.tcx.module_children(ModId::new_unchecked(parent));
            if children.len() > 512 {
                return Err("niche codec visible reexport catalogue exceeds512".into());
            }
            pay(engine, children.len() + 4)?;
            let Some(name) = children
                .iter()
                .find(|child| {
                    child.res.opt_def_id() == Some(id)
                        && child.vis.is_public()
                        && child.ident.name != kw::Underscore
                })
                .map(|child| child.ident.name)
            else {
                return Ok(None);
            };
            count = bounded(name.as_str().len() + 2)?;
        }
        if count != 0 {
            bytes = bounded(bytes + count + 2)?
        }
        id = parent;
    }
    Err(engine.categorized_error(
        UnknownCategory::ResourceLimit,
        "niche codec visible display path exceeds16 parents".into(),
    ))
}

pub(super) fn path(engine: &mut Engine<'_>, id: DefId) -> Result<(), String> {
    let actual = raw(engine, id)?;
    let selected = visible(engine, id)?.unwrap_or(actual);
    bounded(actual.max(selected))?;
    Ok(())
}

fn symbols<'tcx>(raw: &RawCertificate<'tcx>) -> Result<[Symbol; 5], String> {
    let (ty::Adt(parent, _), ty::Adt(outer, _), ty::Adt(inner, _)) =
        (raw.original.kind(), raw.nonzero.kind(), raw.inner.kind())
    else {
        return Err("niche codec raw name identities absent".into());
    };
    let field = FieldIdx::from_usize(0);
    Ok([
        parent.variants()[rustc_abi::VariantIdx::from_usize(0)].name,
        parent.variants()[rustc_abi::VariantIdx::from_usize(1)].name,
        parent
            .variant(rustc_abi::VariantIdx::from_usize(raw.payload_variant))
            .fields[field]
            .name,
        outer.non_enum_variant().fields[field].name,
        inner.non_enum_variant().fields[field].name,
    ])
}

pub(super) fn prepare<'tcx>(
    engine: &mut Engine<'tcx>,
    raw: &RawCertificate<'tcx>,
) -> Result<Names<'tcx>, String> {
    pay(engine, 32)?;
    let symbols = symbols(raw)?;
    for name in symbols {
        pay(engine, 4)?;
        bounded(name.as_str().len())?;
    }
    for original in [raw.original, raw.nonzero, raw.inner] {
        let ty::Adt(def, _) = original.kind() else {
            return Err("niche codec raw ADT absent".into());
        };
        path(engine, def.did())?;
    }
    // Independent prepayment for future owned strings, wrapper/header inspection and comparison.
    pay(engine, 3 * 2 * 129 + 5 * 129 + 96)?;
    Ok(Names {
        original: raw.original,
        outer: raw.nonzero,
        inner: raw.inner,
        symbols,
    })
}

impl<'tcx> Names<'tcx> {
    pub(super) fn check(&self, raw: &RawCertificate<'tcx>) -> Result<(), String> {
        if self.original != raw.original
            || self.outer != raw.nonzero
            || self.inner != raw.inner
            || self.symbols != symbols(raw)?
        {
            return Err("niche codec preplanned original display/name association differs".into());
        }
        Ok(())
    }
}
