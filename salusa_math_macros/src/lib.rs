// use proc_macro2::TokenStream;
use quote::quote;
// use syn::spanned::Spanned;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(GroupOps)]
pub fn derive_group_ops(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = quote! {
        impl #impl_generics std::ops::Add<#name #ty_generics> for #name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn add(self, rhs: #name #ty_generics) -> Self::Output {
                self.gop(&rhs)
            }
        }

        impl #impl_generics std::ops::Add<#name #ty_generics> for &#name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn add(self, rhs: #name #ty_generics) -> Self::Output {
                self.gop(&rhs)
            }
        }

        impl #impl_generics std::ops::Add<&#name #ty_generics> for #name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn add(self, rhs: &#name #ty_generics) -> Self::Output {
                self.gop(rhs)
            }
        }

        impl #impl_generics std::ops::Add<&#name #ty_generics> for &#name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn add(self, rhs: &#name #ty_generics) -> Self::Output {
                self.gop(rhs)
            }
        }

        impl #impl_generics std::ops::Sub<#name #ty_generics> for #name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn sub(self, rhs: #name #ty_generics) -> Self::Output {
                self.gop(&rhs.neg())
            }
        }

        impl #impl_generics std::ops::Sub<#name #ty_generics> for &#name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn sub(self, rhs: #name #ty_generics) -> Self::Output {
                self.gop(&rhs.neg())
            }
        }

        impl #impl_generics std::ops::Sub<&#name #ty_generics> for #name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn sub(self, rhs: &#name #ty_generics) -> Self::Output {
                self.gop(&-rhs)
            }
        }

        impl #impl_generics std::ops::Sub<&#name #ty_generics> for &#name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn sub(self, rhs: &#name #ty_generics) -> Self::Output {
                self.gop(&-rhs)
            }
        }

        impl #impl_generics std::ops::Neg for &#name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn neg(self) -> Self::Output {
                self.gneg()
            }
        }

        impl #impl_generics std::ops::Neg for #name #ty_generics #where_clause
        {
            type Output = #name #ty_generics;

            fn neg(self) -> Self::Output {
                self.gneg()
            }
        }

        impl #impl_generics std::ops::Mul<#name #ty_generics> for num::BigInt #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: #name #ty_generics) -> Self::Output {
                rhs.scalar_mult(&self)
            }
        }

        impl #impl_generics std::ops::Mul<#name #ty_generics> for &num::BigInt #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: #name #ty_generics) -> Self::Output {
                rhs.scalar_mult(self)
            }
        }

        impl #impl_generics std::ops::Mul<&#name #ty_generics> for num::BigInt #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: &#name #ty_generics) -> Self::Output {
                rhs.scalar_mult(&self)
            }
        }

        impl #impl_generics std::ops::Mul<&#name #ty_generics> for &num::BigInt #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: &#name #ty_generics) -> Self::Output {
                rhs.scalar_mult(self)
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}

#[proc_macro_derive(FieldOps)]
pub fn derive_field_ops(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = quote! {
        impl #impl_generics std::ops::Mul<#name #ty_generics> for #name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: #name #ty_generics) -> Self::Output {
                self.mop(&rhs)
            }
        }

        impl #impl_generics std::ops::Mul<&#name #ty_generics> for #name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: &#name #ty_generics) -> Self::Output {
                self.mop(rhs)
            }
        }

        impl #impl_generics std::ops::Mul<#name #ty_generics> for &#name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: #name #ty_generics) -> Self::Output {
                self.mop(&rhs)
            }
        }

        impl #impl_generics std::ops::Mul<&#name #ty_generics> for &#name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn mul(self, rhs: &#name #ty_generics) -> Self::Output {
                self.mop(rhs)
            }
        }

        impl #impl_generics std::ops::Div<#name #ty_generics> for #name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn div(self, rhs: #name #ty_generics) -> Self::Output {
                self.mop(&rhs.m_inv().unwrap())
            }
        }

        impl #impl_generics std::ops::Div<&#name #ty_generics> for #name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn div(self, rhs: &#name #ty_generics) -> Self::Output {
                self.mop(&rhs.m_inv().unwrap())
            }
        }

        impl #impl_generics std::ops::Div<#name #ty_generics> for &#name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn div(self, rhs: #name #ty_generics) -> Self::Output {
                self.mop(&rhs.m_inv().unwrap())
            }
        }

        impl #impl_generics std::ops::Div<&#name #ty_generics> for &#name #ty_generics #where_clause {
            type Output = #name #ty_generics;

            fn div(self, rhs: &#name #ty_generics) -> Self::Output {
                self.mop(&rhs.m_inv().unwrap())
            }
        }
    };

    proc_macro::TokenStream::from(expanded)
}