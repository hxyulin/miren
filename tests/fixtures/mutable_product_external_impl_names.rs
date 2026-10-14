#![no_std]
#![forbid(unsafe_code)]

extern crate d as actual_external_alias_for_printer;

use actual_external_alias_for_printer::{
    ExternalArgumentWithVisibleAliasName, ExternalSelfWithSelectableReexportName,
    ExternalTraitWithSelectableAliasName,
};

pub trait LocalTrait {
    fn external_self_product(&self) -> u16;
}
impl LocalTrait for ExternalSelfWithSelectableReexportName<ExternalArgumentWithVisibleAliasName> {
    fn external_self_product(&self) -> u16 {
        #[derive(Clone, Copy)]
        struct ExternalSelfProduct {
            value: u16,
        }
        ExternalSelfProduct { value: 7 }.value
    }
}

pub struct LocalSelf;
impl ExternalTraitWithSelectableAliasName<ExternalArgumentWithVisibleAliasName> for LocalSelf {
    fn external_trait_product(&self) -> u16 {
        #[derive(Clone, Copy)]
        struct ExternalTraitProduct {
            value: u16,
        }
        ExternalTraitProduct { value: 7 }.value
    }
}
