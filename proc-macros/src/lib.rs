#[macro_use]
extern crate quote;

use ::convert_case::{Case, Casing};
use ::darling::FromMeta;
use ::derive_more::Display;
use ::itertools::interleave;
use ::proc_macro::TokenStream;
use ::proc_macro2::{Span, TokenStream as TokenStream2};
use ::std::str::FromStr;
use ::syn::{parse2, spanned::Spanned, Error};

const ATTRIBUTE_PATH: &str = "dataloader";

#[derive(Clone, Copy, Debug, Default, Display, FromMeta)]
enum TraceLevel {
    #[display("debug")]
    Debug,
    #[display("error")]
    Error,
    #[default]
    #[display("info")]
    Info,
    #[display("trace")]
    Trace,
    #[display("warn")]
    Warn,
}

impl FromStr for TraceLevel {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match &*s {
            "debug" => Self::Debug,
            "error" => Self::Error,
            "info" => Self::Info,
            "trace" => Self::Trace,
            "warn" => Self::Warn,
            _ => {
                return Err(Error::new_spanned(
                    &s,
                    r#"invalid `trace_level`: must use one of "debug", "error", "info", "trace", "warn" "#,
                ))
            }
        })
    }
}

#[derive(Clone, Debug, Default, FromMeta)]
struct DataloaderAttr {
    #[allow(unused)]
    trace_level: Option<TraceLevel>,
    value: Option<syn::Type>,
}

#[proc_macro_attribute]
pub fn dataloader(attr: TokenStream, item: TokenStream) -> TokenStream {
    match dataloader2(attr.into(), item.into()) {
        Ok(tokens) => tokens.into(),
        Err(err) => err.into_compile_error().into(),
    }
}

fn dataloader2(attr: TokenStream2, item: TokenStream2) -> Result<TokenStream2, Error> {
    let item_fn = parse2::<syn::ItemFn>(item)?;
    let meta = parse2::<syn::Meta>(attr)?;

    if !meta.path().is_ident(ATTRIBUTE_PATH) {
        return Err(Error::new_spanned(meta.path(), "expected `#[dataloader]`"));
    }

    let attr = DataloaderAttr::from_meta(&meta)?;

    let fn_name = &item_fn.sig.ident;

    let ctx_ident = format_ident!("ctx");

    let (keys_ident, key_index, key_ty) = get_key_ty_and_index(&item_fn.sig.inputs)?;

    if item_fn.sig.asyncness.is_none() {
        return Err(Error::new_spanned(fn_name, "dataloader function must be async"));
    }

    let fn_call_args = get_fn_call_args(&item_fn.sig.inputs, keys_ident, &ctx_ident)?;

    let (ok_ty, err_ty) = get_fn_return_ok_and_err_types(&item_fn.sig.ident, &item_fn.sig.output)?;

    let struct_vis = &item_fn.vis;
    let key_wrapper_struct_name = format_ident!("{}", format!("{fn_name}").to_case(Case::Pascal));

    let value_ty = get_value_ty(ok_ty, &attr.value)?;

    let loader_key_tys =
        item_fn.sig.inputs
            .iter()
            .enumerate()
            .filter_map(|(i, fn_arg)| {
                if i == key_index {
                    None
                } else {
                    Some(Ok(match fn_arg {
                        syn::FnArg::Typed(pat_type) => match &*pat_type.ty {
                            syn::Type::Reference(type_reference) => &type_reference.elem,
                            _ => return Some(Err(Error::new_spanned(&pat_type.ty, "dataloader function can only accept references to static types (excluding the `keys` argument which is a reference of a slice of references)"))),
                        },
                        _ => unreachable!(),
                    }))
                }
            })
            .collect::<Result<Vec<_>, Error>>()?;

    let lifetime = |i: usize| format!("'dataloader{i}");

    let ctx_ty = quote! { ( #(#loader_key_tys,)* ) }.to_string();
    let ctx_ty = ctx_ty.split("'_").collect::<Vec<_>>();
    let num_anonymous_lifetimes = ctx_ty.len() - 1;

    let mut new_item_fn = item_fn.clone();
    for i in 0..num_anonymous_lifetimes {
        new_item_fn
            .sig
            .generics
            .params
            .push(syn::parse_str::<syn::GenericParam>(&lifetime(i))?);
    }

    let ctx_ty = interleave(ctx_ty.into_iter().map(String::from), (0..num_anonymous_lifetimes).map(lifetime))
        .collect::<Vec<_>>()
        .join("");
    let ctx_ty = TokenStream2::from_str(&ctx_ty).unwrap();

    let (impl_generics, _, _) = new_item_fn.sig.generics.split_for_impl();

    let derefed_keys_ident = format_ident!("{keys_ident}_derefed");

    // define the field tokenstreams conditionally in order to avoid adding unnecessary fields to
    // key wrapper struct
    // define the fn call separately because the traced function call requires pre and post work
    // specific to handling tracing properly across await boundaries
    #[allow(unused)]
    let (default_context_field_defn, default_context_field_init, default_impl_as_ref_context_for_wrapper, default_fn_call) = (
        quote!(),
        quote!(),
        quote!(),
        quote!(
            let #keys_ident = #derefed_keys_ident;
            Ok(#fn_name(#(#fn_call_args),*)
                .await?
                .into_iter()
                .map(|(k, v)| (#key_wrapper_struct_name::from(k), v))
                .collect())
        ),
    );

    #[allow(unused)]
    let span_macro = Option::<syn::Ident>::None;

    #[cfg(feature = "tracing")]
    let trace_level = attr.trace_level.unwrap_or_default();

    #[cfg(feature = "tracing")]
    let span_macro = Some(format_ident!("{trace_level}_span"));

    #[allow(unused_variables)]
    let span_macro = match span_macro {
        Some(span_macro) => span_macro,
        None => return Err(Error::new(Span::call_site(), "dataloader-util requires a tracing level to be specified using one of the following features: tracing-debug, tracing-error, tracing-info, tracing-trace, tracing-warn. Make sure this matches your application's tracing level otherwise dataloader spans may not be properly reconciled with their parent spans.")),
    };

    #[cfg(not(feature = "tracing"))]
    let (context_field_defn, context_field_init, impl_as_ref_context_for_wrapper, fn_call) = (
        default_context_field_defn,
        default_context_field_init,
        default_impl_as_ref_context_for_wrapper,
        default_fn_call,
    );

    #[cfg(feature = "tracing")]
    let context_field_name = format_ident!("context");

    #[cfg(feature = "tracing")]
    let (context_field_defn, context_field_init, impl_as_ref_context_for_wrapper, fn_call) = (
        quote!(
            #[derivative(Hash = "ignore", Ord = "ignore", PartialEq = "ignore", PartialOrd = "ignore")]
            #context_field_name: Option<dataloader_util::opentelemetry::Context>,
        ),
        quote!(#context_field_name: {
            use dataloader_util::tracing_opentelemetry::OpenTelemetrySpanExt;
            use dataloader_util::opentelemetry::trace::TraceContextExt;
            let context = dataloader_util::tracing::Span::current().context();
            let span_ref = context.span();
            let span_context = span_ref.span_context();
            Some(context.clone())
        },),
        quote!(
            impl AsRef<Option<dataloader_util::opentelemetry::Context>> for #key_wrapper_struct_name {
                fn as_ref(&self) -> &Option<dataloader_util::opentelemetry::Context> {
                    &self.#context_field_name
                }
            }
        ),
        quote!(
            if dataloader_util::should_use_span_context(#keys_ident) {
                use dataloader_util::tracing::Instrument;
                use dataloader_util::tracing_opentelemetry::OpenTelemetrySpanExt;
                let #context_field_name = #keys_ident[0].#context_field_name.clone().unwrap();

                let span = dataloader_util::tracing::#span_macro!("dataloader");
                span.set_parent(#context_field_name.clone());

                let #keys_ident = #derefed_keys_ident;

                Ok(#fn_name(#(#fn_call_args),*)
                    .instrument(span)
                    .await?
                    .into_iter()
                    .map(|(key, value)| (#key_wrapper_struct_name { #context_field_name: Some(#context_field_name.clone()), key }, value))
                    .collect())
            } else {
                #default_fn_call
            }
        ),
    );

    let tokens = quote! {
        #item_fn
        #struct_vis use #fn_name::#key_wrapper_struct_name;
        #struct_vis mod #fn_name {
            use super::*;

            #[derive(Clone, Debug, dataloader_util::DataloaderUtilDerivative)]
            #[derivative(Eq, Hash, Ord, PartialEq, PartialOrd)]
            #struct_vis struct #key_wrapper_struct_name {
                #context_field_defn
                #struct_vis key: #key_ty,
            }

            impl #key_wrapper_struct_name {
                pub fn new(key: #key_ty) -> #key_wrapper_struct_name {
                   #key_wrapper_struct_name {
                        #context_field_init
                        key,
                    }
                }
            }

            pub fn new(key: #key_ty) -> #key_wrapper_struct_name {
                #key_wrapper_struct_name {
                    #context_field_init
                    key,
                }
            }

            impl From<#key_ty> for #key_wrapper_struct_name {
                fn from(key: #key_ty) -> Self {
                    #key_wrapper_struct_name {
                        #context_field_init
                        key,
                    }
                }
            }

            impl From<#key_wrapper_struct_name> for #key_ty {
                fn from(key_wrapper: #key_wrapper_struct_name) -> Self {
                    key_wrapper.key
                }
            }

            impl std::ops::Deref for #key_wrapper_struct_name {
                type Target = #key_ty;
                fn deref(&self) -> &Self::Target {
                    &self.key
                }
            }

            impl std::ops::DerefMut for #key_wrapper_struct_name {
                fn deref_mut(&mut self) -> &mut Self::Target {
                    &mut self.key
                }
            }

            #impl_as_ref_context_for_wrapper

            #[dataloader_util::async_trait::async_trait]
            impl #impl_generics async_graphql::dataloader::Loader<#key_wrapper_struct_name> for dataloader_util::BaseLoader<#ctx_ty> {
                type Value = #value_ty;
                type Error = #err_ty;

                #[dataloader_util::async_backtrace::framed]
                async fn load(&self, #keys_ident: &[#key_wrapper_struct_name]) -> Result<std::collections::HashMap<#key_wrapper_struct_name, Self::Value>, Self::Error> {
                    let #ctx_ident = self.ctx();

                    let #derefed_keys_ident = #keys_ident.iter().map(std::ops::Deref::deref).collect::<Vec<_>>();
                    let #derefed_keys_ident: &[&#key_ty] = #derefed_keys_ident.as_slice();

                    #fn_call
                }
            }
        }
    };

    Ok(tokens.into())
}

fn get_key_ty_and_index(
    inputs: &syn::punctuated::Punctuated<syn::FnArg, syn::token::Comma>,
) -> Result<(&syn::Ident, usize, &syn::Type), Error> {
    if inputs.len() != 2 {
        return Err(Error::new_spanned(inputs, "expected 2 inputs"));
    }

    let fn_arg = &inputs[1];
    match fn_arg {
        syn::FnArg::Typed(pat_type) => {
            if let syn::Pat::Ident(ident) = &*pat_type.pat {
                let ident = &ident.ident;
                if let syn::Type::Reference(type_reference) = &*pat_type.ty {
                    if let syn::Type::Slice(type_slice) = &*type_reference.elem {
                        if let syn::Type::Reference(type_reference) = &*type_slice.elem {
                            Ok((ident, 1, &*type_reference.elem))
                        } else {
                            return Err(Error::new_spanned(
                                fn_arg,
                                format!("`{ident}` must be a reference to a slice of references"),
                            ));
                        }
                    } else {
                        return Err(Error::new_spanned(
                            fn_arg,
                            format!("`{ident}` must be a reference to a slice of references"),
                        ));
                    }
                } else {
                    return Err(Error::new_spanned(
                        fn_arg,
                        format!("`{ident}` must be a reference to a slice of references"),
                    ));
                }
            } else {
                Err(Error::new_spanned(pat_type, "unexpected argument pattern, must be an ident"))
            }
        }
        syn::FnArg::Receiver(receiver) => Err(Error::new_spanned(
            receiver.self_token,
            "dataloader function cannot accept a receiver arg",
        )),
    }
}

fn get_value_ty<'a>(ok_ty: &'a syn::Type, value_ty: &'a Option<syn::Type>) -> Result<syn::Type, Error> {
    static ERR_MSG: &str = "unable to parse async_graphql::dataloader::Loader::Value from your dataloader function's return type (automatically parsed include Vec<(K, V)>, Vec<(K, Vec<V>)>, HashMap<K, V>, HashMap<K, Vec<V>>, LoadedOne<K, V> and LoadedMany<K, V> where LoadedOne and LoadedMany are exported from dataloader_util. Note that using LoadedOne and LoadedMany will prevent any confusion of using a Vec type as your V value), please use one of these return types or specify the Value type in the attribute, such as #[dataloader(Value = DbRecord)]";

    if let Some(value_ty) = value_ty.as_ref() {
        return Ok(value_ty.clone());
    }

    let err = || Err(Error::new_spanned(ok_ty, ERR_MSG));

    match ok_ty {
        syn::Type::Path(type_path) => {
            let path = &type_path.path;
            if path.segments.len() != 1 {
                return err();
            }

            let path_segment = path.segments.first().unwrap();

            if path_segment.ident == "Vec" {
                let inner_ty = get_inner_vec_ty(ok_ty)?;
                let second_field_tuple_ty = match inner_ty {
                    syn::Type::Tuple(type_tuple) => {
                        if type_tuple.elems.len() != 2 {
                            return err();
                        }
                        type_tuple.elems.last().unwrap()
                    }
                    _ => return err(),
                };
                if is_vec_type(second_field_tuple_ty) {
                    let inner_vec_ty = get_inner_vec_ty(second_field_tuple_ty)?;
                    Ok(parse2(quote!(Vec<#inner_vec_ty>))?)
                } else {
                    Ok(second_field_tuple_ty.clone())
                }
            } else if path_segment.ident == "HashMap" {
                let inner_ty = match &path_segment.arguments {
                    syn::PathArguments::AngleBracketed(angle_bracketed_generic_arguments) => {
                        if angle_bracketed_generic_arguments.args.len() != 2 {
                            return err();
                        }
                        let tys: Vec<_> = angle_bracketed_generic_arguments.args.iter().collect();
                        match tys[1] {
                            syn::GenericArgument::Type(inner_ty) => inner_ty,
                            _ => return err(),
                        }
                    }
                    _ => return err(),
                };
                let second_field_tuple_ty = match inner_ty {
                    syn::Type::Tuple(type_tuple) => {
                        if type_tuple.elems.len() != 2 {
                            return err();
                        }
                        type_tuple.elems.last().unwrap()
                    }
                    _ => return err(),
                };
                if is_vec_type(second_field_tuple_ty) {
                    let inner_vec_ty = get_inner_vec_ty(second_field_tuple_ty)?;
                    Ok(parse2(quote!(Vec<#inner_vec_ty>))?)
                } else {
                    Ok(second_field_tuple_ty.clone())
                }
            } else if path_segment.ident == "LoadedOne" {
                match &path_segment.arguments {
                    syn::PathArguments::AngleBracketed(angle_bracketed_generic_arguments) => {
                        if angle_bracketed_generic_arguments.args.len() != 2 {
                            return err();
                        }
                        let tys: Vec<_> = angle_bracketed_generic_arguments.args.iter().collect();
                        match tys[1] {
                            syn::GenericArgument::Type(inner_ty) => Ok(inner_ty.clone()),
                            _ => return err(),
                        }
                    }
                    _ => return err(),
                }
            } else if path_segment.ident == "LoadedMany" {
                match &path_segment.arguments {
                    syn::PathArguments::AngleBracketed(angle_bracketed_generic_arguments) => {
                        if angle_bracketed_generic_arguments.args.len() != 2 {
                            return err();
                        }
                        let tys: Vec<_> = angle_bracketed_generic_arguments.args.iter().collect();
                        match tys[1] {
                            syn::GenericArgument::Type(inner_ty) => Ok(parse2(quote!(Vec<#inner_ty>))?),
                            _ => return err(),
                        }
                    }
                    _ => return err(),
                }
            } else {
                err()
            }
        }
        _ => err(),
    }
}

fn is_vec_type(ty: &syn::Type) -> bool {
    if let syn::Type::Path(type_path) = ty {
        type_path.path.is_ident("Vec")
    } else {
        false
    }
}

fn get_fn_return_ok_and_err_types<'a>(
    sig_ident: &syn::Ident,
    sig_output: &'a syn::ReturnType,
) -> Result<(&'a syn::Type, &'a syn::Type), Error> {
    static ERR_MSG: &str = "dataloader function return type must have be a Result";

    match sig_output {
        syn::ReturnType::Type(_, ty) => match &**ty {
            syn::Type::Path(type_path) => {
                let err = Error::new(type_path.span(), ERR_MSG);

                if type_path.path.segments.len() != 1 || type_path.path.segments.first().unwrap().ident != "Result" {
                    return Err(err);
                }
                match &type_path.path.segments.first().unwrap().arguments {
                    syn::PathArguments::AngleBracketed(angle_bracketed_generic_arguments) => {
                        let num_gen_args = angle_bracketed_generic_arguments.args.len();
                        if num_gen_args == 1 {
                            return Err(Error::new_spanned(
                                ty,
                                "must specify error variant (required to implement async_grahpql::dataloader::Loader and cannot be inferred)",
                            ));
                        }
                        if num_gen_args != 2 {
                            return Err(err);
                        }
                        let tys: Vec<_> = angle_bracketed_generic_arguments.args.iter().collect();
                        match tys[0] {
                            syn::GenericArgument::Type(ok_ty) => match tys[1] {
                                syn::GenericArgument::Type(err_ty) => Ok((ok_ty, err_ty)),
                                _ => Err(err),
                            },
                            _ => Err(err),
                        }
                    }
                    _ => Err(err),
                }
            }
            _ => Err(Error::new(sig_ident.span(), ERR_MSG)),
        },
        _ => Err(Error::new(sig_ident.span(), ERR_MSG)),
    }
}

fn get_inner_vec_ty(ty: &syn::Type) -> Result<&syn::Type, Error> {
    static ERR_MSG: &str = "expected a Vec type";

    match ty {
        syn::Type::Path(type_path) => {
            let err = || Err(Error::new_spanned(type_path, ERR_MSG));

            if type_path.path.segments.len() != 1 || type_path.path.segments.first().unwrap().ident != "Vec" {
                return err();
            }
            match &type_path.path.segments.first().unwrap().arguments {
                syn::PathArguments::AngleBracketed(angle_bracketed_generic_arguments) => {
                    if angle_bracketed_generic_arguments.args.len() != 1 {
                        return err();
                    }
                    let tys: Vec<_> = angle_bracketed_generic_arguments.args.iter().collect();
                    match tys[0] {
                        syn::GenericArgument::Type(inner_ty) => Ok(inner_ty),
                        _ => err(),
                    }
                }
                _ => err(),
            }
        }
        _ => Err(Error::new(Span::call_site(), ERR_MSG)),
    }
}

fn is_keys_ident(pat_type: &syn::PatType, keys_ident: &syn::Ident) -> bool {
    if let syn::Pat::Ident(ident) = &*pat_type.pat {
        ident.ident == *keys_ident
    } else {
        false
    }
}

fn get_fn_call_args(
    inputs: &syn::punctuated::Punctuated<syn::FnArg, syn::token::Comma>,
    keys_ident: &syn::Ident,
    ctx_ident: &syn::Ident,
) -> Result<Vec<TokenStream2>, Error> {
    let mut fn_call_args = Vec::with_capacity(inputs.len());

    let mut index = 0;
    for fn_arg in inputs.iter() {
        match fn_arg {
            syn::FnArg::Receiver(receiver) => {
                return Err(Error::new_spanned(
                    receiver.self_token,
                    "dataloader function cannot accept a receiver arg",
                ));
            }
            syn::FnArg::Typed(pat_type) => {
                if is_keys_ident(pat_type, keys_ident) {
                    fn_call_args.push(quote! { #keys_ident });
                } else {
                    match &*pat_type.ty {
                        syn::Type::Reference(_) => {},
                        _ => return Err(Error::new_spanned(&pat_type.ty, "dataloader function can only accept references to static types (excluding the `keys` argument which is a reference of a slice of references)")),
                    }
                    let index_token = TokenStream2::from_str(&index.to_string()).unwrap();
                    fn_call_args.push(quote! { &#ctx_ident.#index_token });
                    index += 1;
                }
            }
        };
        index += 1;
    }

    Ok(fn_call_args)
}
