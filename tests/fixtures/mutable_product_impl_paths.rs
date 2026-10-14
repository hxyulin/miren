#![no_std]

pub mod compiler_impl_product_name_printer_module {
    pub struct ContainerWithAnActualLongNameForCompilerPathAccounting<T>(pub T);
    pub trait CompilerPathAccountingTrait<T> {
        fn product_path(&self) -> u16;
    }
    impl<GenericParameterWithAnActualLongNameForCompilerPathAccounting>
        ContainerWithAnActualLongNameForCompilerPathAccounting<
            GenericParameterWithAnActualLongNameForCompilerPathAccounting,
        >
    {
        pub fn inherent_product(&self) -> u16 {
            #[derive(Clone, Copy)]
            struct InherentProductWithActualCompilerQualifiedName {
                left: u16,
                right: u16,
            }
            let product = InherentProductWithActualCompilerQualifiedName { left: 3, right: 7 };
            product.left + product.right
        }
    }
    impl<T> CompilerPathAccountingTrait<T>
        for ContainerWithAnActualLongNameForCompilerPathAccounting<T>
    {
        fn product_path(&self) -> u16 {
            #[derive(Clone, Copy)]
            struct TraitProductWithActualCompilerQualifiedName {
                left: u16,
                right: u16,
            }
            let product = TraitProductWithActualCompilerQualifiedName { left: 3, right: 7 };
            product.left + product.right
        }
    }
}

pub struct ConstContainer<const COUNT: usize>;
impl<const ACTUAL_CONST_PARAMETER_NAME_FOR_THE_COMPILER_PATH: usize>
    ConstContainer<ACTUAL_CONST_PARAMETER_NAME_FOR_THE_COMPILER_PATH>
{
    pub fn constant_product(&self) -> u16 {
        #[derive(Clone, Copy)]
        struct ConstProduct {
            value: u16,
        }
        ConstProduct { value: 7 }.value
    }
}

pub trait FunctionTypeTrait {
    fn function_product(&self) -> u16;
}
impl FunctionTypeTrait for fn(u16) -> u16 {
    fn function_product(&self) -> u16 {
        #[derive(Clone, Copy)]
        struct UnsupportedFunctionPrinterProduct {
            value: u16,
        }
        UnsupportedFunctionPrinterProduct { value: 7 }.value
    }
}

pub struct OversizedNameContainer<A, B, C, D, E, F, G, H>(
    pub core::marker::PhantomData<(A, B, C, D, E, F, G, H)>,
);
impl<
    ActualLongCompilerGenericParameterForOversizedPathAccounting0,
    ActualLongCompilerGenericParameterForOversizedPathAccounting1,
    ActualLongCompilerGenericParameterForOversizedPathAccounting2,
    ActualLongCompilerGenericParameterForOversizedPathAccounting3,
    ActualLongCompilerGenericParameterForOversizedPathAccounting4,
    ActualLongCompilerGenericParameterForOversizedPathAccounting5,
    ActualLongCompilerGenericParameterForOversizedPathAccounting6,
    ActualLongCompilerGenericParameterForOversizedPathAccounting7,
>
    OversizedNameContainer<
        ActualLongCompilerGenericParameterForOversizedPathAccounting0,
        ActualLongCompilerGenericParameterForOversizedPathAccounting1,
        ActualLongCompilerGenericParameterForOversizedPathAccounting2,
        ActualLongCompilerGenericParameterForOversizedPathAccounting3,
        ActualLongCompilerGenericParameterForOversizedPathAccounting4,
        ActualLongCompilerGenericParameterForOversizedPathAccounting5,
        ActualLongCompilerGenericParameterForOversizedPathAccounting6,
        ActualLongCompilerGenericParameterForOversizedPathAccounting7,
    >
{
    pub fn oversized_product(&self) -> u16 {
        #[derive(Clone, Copy)]
        struct OversizedPrinterProduct {
            value: u16,
        }
        OversizedPrinterProduct { value: 7 }.value
    }
}
