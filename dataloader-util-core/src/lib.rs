#![cfg_attr(feature = "unstable", feature(type_alias_impl_trait))]

#[macro_use]
extern crate derive_more;

pub use async_backtrace;
pub use async_trait;
pub use derivative::Derivative as DataloaderUtilDerivative;

use cfg_if::cfg_if;
use futures::future::try_join_all;
use itertools::Itertools;
use scoped_futures::*;
use std::collections::HashMap;
use std::hash::Hash;

#[cfg(feature = "unstable")]
use std::fmt::Debug;

/// `'static` lifetime imposed by [async_graphql::dataloader::Loader](https://docs.rs/async-graphql/latest/async_graphql/dataloader/trait.Loader.html)
pub struct BaseLoader<Ctx: 'static> {
    ctx: Ctx,
}

impl<Ctx: 'static> BaseLoader<Ctx> {
    pub fn new(ctx: Ctx) -> Self {
        Self { ctx }
    }
    pub fn ctx(&self) -> &Ctx {
        &self.ctx
    }
}

pub trait LoadedMap {
    type Value;
    type Iterator<'a, T>
    where
        Self: 'a;
    fn map_loaded<'a, T, F>(&'a self) -> Self::Iterator<'a, T>
    where
        F: FnOnce(&Self::Value) -> T;
}

#[derive(
    AsRef, AsMut, Clone, Debug, Default, Deref, DerefMut, Eq, From, Into, Ord, PartialEq, PartialOrd,
)]
pub struct LoadedMany<K, V>(pub Vec<(K, Vec<V>)>);

#[derive(
    AsRef, AsMut, Clone, Debug, Default, Deref, DerefMut, Eq, From, Into, Ord, PartialEq, PartialOrd,
)]
pub struct LoadedOne<K, V>(pub Vec<(K, V)>);

impl<K, V> FromIterator<(K, Vec<V>)> for LoadedMany<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, Vec<V>)>>(iter: T) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl<K, V> FromIterator<(K, V)> for LoadedOne<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        Self(Vec::from_iter(iter))
    }
}

impl<K, V> IntoIterator for LoadedMany<K, V> {
    type Item = (K, Vec<V>);
    type IntoIter = <Vec<(K, Vec<V>)> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<K, V> IntoIterator for LoadedOne<K, V> {
    type Item = (K, V);
    type IntoIter = <Vec<(K, V)> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[cfg(feature = "unstable")]
impl<'a, K: Debug + 'a, V: Debug + 'a> IntoIterator for &'a LoadedMany<K, V> {
    type Item = &'a V;
    type IntoIter = impl Debug + Iterator<Item = &'a V>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().flat_map(|x| x.1.iter())
    }
}
#[cfg(feature = "unstable")]
impl<'a, K: Debug + 'a, V: Debug + 'a> IntoIterator for &'a LoadedOne<K, V> {
    type Item = &'a V;
    type IntoIter = impl Debug + Iterator<Item = &'a V>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|x| &x.1)
    }
}

#[cfg(not(feature = "unstable"))]
impl<'a, K: 'a, V: 'a> IntoIterator for &'a LoadedMany<K, V> {
    type Item = &'a V;
    type IntoIter = std::iter::FlatMap<
        std::slice::Iter<'a, (K, Vec<V>)>,
        std::slice::Iter<'a, V>,
        Box<dyn FnMut(&'a (K, Vec<V>)) -> std::slice::Iter<'a, V> + Send + Sync>,
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().flat_map(Box::new(|x| x.1.iter()))
    }
}
#[cfg(not(feature = "unstable"))]
impl<'a, K: 'a, V: 'a> IntoIterator for &'a LoadedOne<K, V> {
    type Item = &'a V;
    type IntoIter = std::iter::Map<
        std::slice::Iter<'a, (K, V)>,
        Box<dyn FnMut(&'a (K, V)) -> &'a V + Send + Sync>,
    >;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(Box::new(|x| &x.1))
    }
}

pub trait LoadedIterator {
    type Item<'a>
    where
        Self: 'a;
    type Iter<'a>
    where
        Self: 'a;
    fn iter(&self) -> Self::Iter<'_>;
}

impl<K, V> LoadedIterator for LoadedMany<K, V>
where
    for<'a> &'a LoadedMany<K, V>: IntoIterator,
{
    type Item<'a> = &'a V where Self: 'a;
    type Iter<'a> = <&'a Self as IntoIterator>::IntoIter where Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        (self).into_iter()
    }
}
impl<K, V> LoadedIterator for LoadedOne<K, V>
where
    for<'a> &'a LoadedOne<K, V>: IntoIterator,
{
    type Item<'a> = &'a V where Self: 'a;
    type Iter<'a> = <&'a Self as IntoIterator>::IntoIter where Self: 'a;
    fn iter(&self) -> Self::Iter<'_> {
        (self).into_iter()
    }
}

/// Manages grouping keys, fetching their values and unloading key-value pairs fetched into
/// an acceptable output format for the dataloader utility provided by async-graphql.
///
/// keys: a slice of references to a generic `K`. Note that the slice may contain keys from more than
/// one concurrent request (the whole point of dataloading). No extra work needs to be done at the
/// end to dissect which key belongs to which "request" because that splitting off is managed by the
/// dataloader functionality of this crate / the async-graphql crate
///
/// group_by: a function which takes a key &K returns any type `G` where `G` implements for [PartialEq]
/// for grouping purposes. The produced group `G` and all the keys which map to it are passed on as
/// arguments to the fetch function.
///
/// fetch: a function which takes a group &G and a set of keys `&[&K]` corresponding to the provided
/// group which should return a scoped and boxed future (as simple as calling `.scope_boxed()` on an
/// async block provided the trait scoped_futures::ScopedFutureExt is in scope) whose Output is a
/// `Vec<KV>` (where `KV` is determined by the fetch function). `KV` is a generic of this function which
/// which represents a pairing of a fetched value and the key corresponding to it. This could be a
/// tuple of `(Uuid, Value)` or a single Value which has its key embedded in it. `KV` is very flexibly
/// defined because of the next and final argument.
///
/// unload: a function which takes a group `&G` and a fetched `KV` and produces a tuple of the original
/// key type `K` and the final output `V`. The group `G` is provided in case any information (such as a
/// page) isn't included in the `KV` type but is included in the `K` type. Because `G` is passed in by
/// reference, typically values will need to be cloned out of it but that burden is placed on the
/// caller so that this function isn't just spreadshot cloning every group for every key.
///
#[async_backtrace::framed]
pub async fn dataload_many<'a, K, V, KV, E, G, GB, F, U>(
    keys: &[&'a K],
    group_by: GB,
    fetch: F,
    unload: U,
) -> Result<LoadedMany<K, V>, E>
where
    K: Eq + Hash + 'a,
    G: PartialEq,
    GB: Fn(&'a K) -> G,
    for<'r> F: Copy + Fn(&'r G, &'r [&'a K]) -> ScopedBoxFuture<'a, 'r, Result<Vec<KV>, E>>,
    U: Fn(&G, KV) -> (K, V),
{
    let grouped_keys = keys
        .iter()
        .group_by(|x| group_by(**x))
        .into_iter()
        .map(|(group, keys)| (group, keys.copied().collect()))
        .collect::<Vec<(G, Vec<&'a K>)>>();

    Ok(
        try_join_all(grouped_keys.iter().map(|(group, keys)| async move {
            fetch(group, keys)
                .await
                .map(|key_values| (group, key_values))
        }))
        .await?
        .into_iter()
        .flat_map(|(group, key_values)| {
            let mut grouped_values = HashMap::<K, Vec<V>>::default();
            for key_value in key_values {
                let (key, value) = unload(group, key_value);

                #[allow(clippy::map_entry)]
                if !grouped_values.contains_key(&key) {
                    grouped_values.insert(key, vec![value]);
                } else {
                    grouped_values.get_mut(&key).unwrap().push(value);
                }
            }
            grouped_values.into_iter()
        })
        .collect(),
    )
}

#[async_backtrace::framed]
pub async fn dataload_many_group_none<'a, K, V, E, F>(
    keys: &[&'a K],
    fetch: F,
) -> Result<LoadedMany<K, V>, E>
where
    K: Clone + Eq + Hash + 'a,
    for<'r> F: Copy + Fn(&'r &'a K) -> ScopedBoxFuture<'a, 'r, Result<Vec<V>, E>>,
{
    Ok(try_join_all(
        keys.iter()
            .map(|key| async move { fetch(key).await.map(|values| (key, values)) }),
    )
    .await?
    .into_iter()
    .flat_map(|(key, values)| {
        let mut grouped_values = HashMap::<K, Vec<V>>::default();
        for value in values {
            #[allow(clippy::map_entry)]
            if !grouped_values.contains_key(key) {
                grouped_values.insert((**key).clone(), vec![value]);
            } else {
                grouped_values.get_mut(key).unwrap().push(value);
            }
        }
        grouped_values.into_iter()
    })
    .collect())
}

#[async_backtrace::framed]
pub async fn dataload_one<'a, K, V, KV, E, G, GB, F, U>(
    keys: &[&'a K],
    group_by: GB,
    fetch: F,
    unload: U,
) -> Result<LoadedOne<K, V>, E>
where
    K: Eq + Hash + 'a,
    G: PartialEq,
    GB: Fn(&'a K) -> G,
    for<'r> F: Copy + Fn(&'r G, &'r [&'a K]) -> ScopedBoxFuture<'a, 'r, Result<Vec<KV>, E>>,
    U: Fn(&G, KV) -> (K, V),
{
    let grouped_keys = keys
        .iter()
        .group_by(|x| group_by(**x))
        .into_iter()
        .map(|(group, keys)| (group, keys.copied().collect()))
        .collect::<Vec<(G, Vec<&'a K>)>>();

    Ok(
        try_join_all(grouped_keys.iter().map(|(group, keys)| async move {
            fetch(group, keys)
                .await
                .map(|key_values| (group, key_values))
        }))
        .await?
        .into_iter()
        .flat_map(|(group, key_values)| {
            key_values
                .into_iter()
                .map(|key_value| unload(group, key_value))
        })
        .collect(),
    )
}

#[async_backtrace::framed]
pub async fn dataload_many_basic<'a, K, V, E, F>(
    keys: &[&'a K],
    fetch: F,
) -> Result<LoadedMany<K, V>, E>
where
    K: Eq + Hash + 'a,
    for<'r> F: Copy + Fn(&'r [&'a K]) -> ScopedBoxFuture<'a, 'r, Result<Vec<(K, V)>, E>>,
{
    dataload_many(
        keys,
        |key| key,
        |_, keys| fetch(keys),
        |_, key_value| key_value,
    )
    .await
}

#[async_backtrace::framed]
pub async fn dataload_one_basic<'a, K, V, E, F>(
    keys: &[&'a K],
    fetch: F,
) -> Result<LoadedOne<K, V>, E>
where
    K: Clone + Eq + Hash + Send + Sync + 'a,
    for<'r> F: Copy + Send + Sync + Fn(&'r K) -> ScopedBoxFuture<'a, 'r, Result<V, E>>,
{
    dataload_one(
        keys,
        |key| key,
        |key, _| async { fetch(key).await.map(|x| vec![x]) }.scope_boxed(),
        |key, value| ((**key).clone(), value),
    )
    .await
}

cfg_if! {
    if #[cfg(feature = "tracing")] {
        pub use opentelemetry;
        pub use tracing;
        pub use tracing_opentelemetry;

        use opentelemetry::{Context, trace::TraceContextExt};
        use tracing::Span;
        use tracing_opentelemetry::OpenTelemetrySpanExt;

        pub fn current_trace_context() -> Option<Context> {
            let context = Span::current().context();
            let span_ref = context.span();
            let span_context = span_ref.span_context();
            if !span_context.is_valid() {
                return None;
            }
            Some(context)
        }

        pub fn should_use_span_context(contexts: impl IntoIterator<Item = impl AsRef<Option<Context>>>) -> bool {
            let mut contexts = contexts.into_iter();

            let first = match contexts.next() {
                Some(first) => first,
                None => return false,
            };

            if first.as_ref().is_some() {
                let first_context = first.as_ref().as_ref().unwrap();
                let first_span_ref = first_context.span();
                let first_span_context = first_span_ref.span_context();
                if !first_span_context.is_valid() {
                    return false;
                }

                for key in contexts {
                    let context = match key.as_ref().as_ref() {
                        Some(context) => context,
                        None => return false,
                    };
                    let span_ref = context.span();
                    let span_context = span_ref.span_context();
                    if !span_context.is_valid() {
                        return false;
                    }
                    if span_context != first_span_context {
                        return false;
                    }
                }
            }

            true
        }
    }
}
