extern crate proc_macro;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_error::abort;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    spanned::Spanned,
    Expr, Ident, LitStr, Pat, PatIdent, Result, Token,
};

struct MacroInput {
    in_value: Expr,
    pat: Pat,
    guard: Option<(Token![if], Box<Expr>)>,
}

impl Parse for MacroInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let in_value = input.parse()?;
        input.parse::<Token![,]>()?;
        let pat = input.call(multi_pat_with_leading_vert)?;
        let guard = if input.peek(Token![if]) {
            let if_token: Token![if] = input.parse()?;
            let guard: Expr = input.parse()?;
            Some((if_token, Box::new(guard)))
        } else {
            None
        };

        Ok(Self {
            pat,
            in_value,
            guard,
        })
    }
}

fn multi_pat_with_leading_vert(input: ParseStream) -> Result<Pat> {
    let leading_vert: Option<Token![|]> = input.parse()?;
    let mut pat: Pat = input.parse()?;
    if leading_vert.is_some()
        || input.peek(Token![|]) && !input.peek(Token![||]) && !input.peek(Token![|=])
    {
        let mut cases = syn::punctuated::Punctuated::new();
        cases.push_value(pat);
        while input.peek(Token![|]) && !input.peek(Token![||]) && !input.peek(Token![|=]) {
            let punct = input.parse()?;
            cases.push_punct(punct);
            let pat: Pat = input.parse()?;
            cases.push_value(pat);
        }
        pat = Pat::Or(syn::PatOr {
            attrs: Vec::new(),
            leading_vert,
            cases,
        });
    }
    Ok(pat)
}

#[proc_macro]
#[proc_macro_error::proc_macro_error]
pub fn implicit_try_match_inner(input: TokenStream) -> TokenStream {
    let MacroInput {
        pat,
        in_value,
        guard,
    } = parse_macro_input!(input);

    let mut idents = Vec::new();
    collect_pat_ident(&pat, &mut idents);

    idents.sort_by_key(|i| &i.ident);
    idents.dedup_by_key(|i| &i.ident);

    let success_output =
        // Check if bound variables are all like `_0`, `_1`, in which case
        // collect them in a tuple
        if let Some(tokens) = check_tuple_captures(&idents) {
            tokens
        } else {
            // Decide what to do based on the number of bound variables
            match &idents[..] {
                [] => {
                    quote! {()}
                }
                [single] => {
                    quote! {#single}
                }
                multi => {
                    // `var1`, `var2`, ...
                    let idents: Vec<_> = multi.iter().map(|p| p.ident.clone()).collect();

                    // `_M_0`, `_M_1`, ...
                    let ty_params: Vec<_> = (0..idents.len())
                        .map(|i| Ident::new(&format!("_M_{}", i), Span::call_site()))
                        .collect();

                    // `"var1"`, `"var2"`, ...
                    let ident_strs: Vec<_> = idents
                        .iter()
                        .map(|i| LitStr::new(&format!("{}", i), i.span()))
                        .collect();

                    let ty_name = Ident::new("__Match", Span::call_site());

                    let debug_impl = {
                        let fmt = quote! { ::core::fmt };
                        quote! {
                            impl<#(#ty_params),*> #fmt::Debug for #ty_name<#(#ty_params),*>
                            where
                                #(#ty_params: #fmt::Debug),*
                            {
                                fn fmt(&self, f: &mut #fmt::Formatter<'_>) -> #fmt::Result {
                                    f.debug_struct("<anonymous>")
                                        #(.field(#ident_strs, &self.#idents))*
                                        .finish()
                                }
                            }
                        }
                    };

                    quote! {{
                        #[derive(Clone, Copy)]
                        struct #ty_name<#(#ty_params),*> {
                            #(
                                #idents: #ty_params
                            ),*
                        }

                        #debug_impl

                        #ty_name { #(#idents),* }
                    }}
                }
            }
        };

    let guard = guard.map(|(t0, t1)| quote! { #t0 #t1 });

    let output = quote! {
        match #in_value {
            #pat #guard => ::core::result::Result::Ok(#success_output),
            in_value => ::core::result::Result::Err(in_value),
        }
    };

    TokenStream::from(output)
}

/// Check if `idents` contains a tuple binding (e.g., `_4`). If it does, returns
/// a `TokenStream` that collects the bound variables (e.g., `(_0, _1)`).
#[allow(clippy::manual_strip)] // `strip_prefix` is only available in Rust ≥ 1.45
fn check_tuple_captures(idents: &[&PatIdent]) -> Option<proc_macro2::TokenStream> {
    let mut some_tuple_cap = None;
    let mut some_non_tuple_cap = None;

    let mut indices: Vec<(u128, &Ident)> = idents
        .iter()
        .map(|i| {
            let index = {
                let text = i.ident.to_string();
                if text.starts_with("_") {
                    // assuming the index fits in `u128`...
                    text[1..].parse().ok()
                } else {
                    None
                }
            };

            if let Some(index) = index {
                some_tuple_cap = Some(*i);
                (index, &i.ident)
            } else {
                some_non_tuple_cap = Some(*i);
                (0 /* dummy */, &i.ident)
            }
        })
        .collect();

    if let (Some(i1), Some(i2)) = (some_tuple_cap, some_non_tuple_cap) {
        abort!(
            i1.span(),
            "can't have both of a tuple binding `{}` and a non-tuple binding \
             `{}` at the same time",
            i1.ident,
            i2.ident
        );
    }

    if some_tuple_cap.is_some() {
        // Create a reverse map from tuple fields to bound variables
        indices.sort_unstable_by_key(|e| e.0);

        for (&(ind, ref ident), i) in indices.iter().zip(0u128..) {
            if ind > i {
                if ind - 1 == i {
                    abort!(
                        ident.span(),
                        "non-contiguous tuple binding: `_{}` is missing",
                        ind - 1
                    );
                } else {
                    abort!(
                        ident.span(),
                        "non-contiguous tuple binding: `_{}` .. `_{}` are missing",
                        i,
                        ind - 1
                    );
                }
            } else if ind < i {
                assert_eq!(i - 1, ind);
                abort!(
                    ident.span(),
                    "duplicate tuple binding: `_{}` is defined for multiple times",
                    ind
                );
            }
        }

        // `var1`, `var2`, ...
        let idents: Vec<_> = indices.into_iter().map(|p| p.1).collect();

        Some(quote! { ( #(#idents),* ) })
    } else {
        None
    }
}

fn collect_pat_ident<'a>(pat: &'a Pat, out: &mut Vec<&'a PatIdent>) {
    match pat {
        Pat::Box(pat) => collect_pat_ident(&pat.pat, out),
        Pat::Ident(pat) => {
            out.push(pat);
            if let Some((_, subpat)) = &pat.subpat {
                collect_pat_ident(subpat, out);
            }
        }
        Pat::Lit(_) => {}
        Pat::Macro(_) => {}
        Pat::Or(pat) => {
            for case in pat.cases.iter() {
                collect_pat_ident(case, out);
            }
        }
        Pat::Path(_) => {}
        Pat::Range(_) => {}
        Pat::Reference(pat) => collect_pat_ident(&pat.pat, out),
        Pat::Rest(_) => {}
        Pat::Slice(pat) => {
            for elem in pat.elems.iter() {
                collect_pat_ident(elem, out);
            }
        }
        Pat::Struct(pat) => {
            for field in pat.fields.iter() {
                collect_pat_ident(&field.pat, out);
            }
        }
        Pat::Tuple(pat) => {
            for elem in pat.elems.iter() {
                collect_pat_ident(elem, out);
            }
        }
        Pat::TupleStruct(pat) => {
            for elem in pat.pat.elems.iter() {
                collect_pat_ident(elem, out);
            }
        }
        Pat::Type(pat) => collect_pat_ident(&pat.pat, out),
        Pat::Wild(_) => {}
        // `Pat` can't be covered exhaustively
        _ => abort!(pat.span(), "unsupported pattern"),
    }
}
