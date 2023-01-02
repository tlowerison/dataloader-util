use futures::future::try_join_all;
use itertools::Itertools;
use scoped_futures::*;
use std::collections::HashMap;
use std::hash::Hash;

pub use async_backtrace;
pub use async_trait;

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

pub type LoadedMany<K, V> = Vec<(K, Vec<V>)>;
pub type LoadedOne<K, V> = Vec<(K, V)>;

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
        .map(|(group, keys)| (group, keys.map(|x| *x).collect()))
        .collect::<Vec<(G, Vec<&'a K>)>>();

    Ok(try_join_all(
        grouped_keys
            .iter()
            .map(|(group, keys)| async move { fetch(group, keys).await.map(|key_values| (group, key_values)) })
    )
        .await?
        .into_iter()
        .flat_map(|(group, key_values)| {
            let mut grouped_values = HashMap::<K, Vec<V>>::default();
            for key_value in key_values {
                let (key, value) = unload(&group, key_value);
                if !grouped_values.contains_key(&key) {
                    grouped_values.insert(key, vec![value]);
                } else {
                    grouped_values.get_mut(&key).unwrap().push(value);
                }
            }
            grouped_values.into_iter()
        })
        .collect())
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
        keys
            .iter()
            .map(|key| async move { fetch(key).await.map(|values| (key, values)) })
    )
        .await?
        .into_iter()
        .flat_map(|(key, values)| {
            let mut grouped_values = HashMap::<K, Vec<V>>::default();
            for value in values {
                if !grouped_values.contains_key(&key) {
                    grouped_values.insert((**key).clone(), vec![value]);
                } else {
                    grouped_values.get_mut(&key).unwrap().push(value);
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
        .map(|(group, keys)| (group, keys.map(|x| *x).collect()))
        .collect::<Vec<(G, Vec<&'a K>)>>();

    Ok(try_join_all(
        grouped_keys
            .iter()
            .map(|(group, keys)| async move { fetch(group, keys).await.map(|key_values| (group, key_values)) })
    )
        .await?
        .into_iter()
        .flat_map(|(group, key_values)| key_values.into_iter().map(|key_value| unload(group, key_value)))
        .collect())
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
    ).await
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

