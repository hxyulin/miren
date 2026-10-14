#![no_std]
#![forbid(unsafe_code)]

mod r {
    pub struct S<T>(pub T);
    pub struct A;
    pub trait T<V> {
        fn external_trait_product(&self) -> u16;
    }
}

pub use r::A as ExternalArgumentWithVisibleAliasName;
pub use r::S as ExternalSelfWithSelectableReexportName;
pub use r::T as ExternalTraitWithSelectableAliasName;
