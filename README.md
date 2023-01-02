# dataloader-util

Turn any function into a dataloader! Integrates with the [async-graphql](https://github.com/async-graphql/async-graphql) feature `dataloader`.

## Example

```rust
// service / db layers
use async_graphql::{DataLoader, InputObject};
use dataloader_util::{BaseLoader, dataloader, dataload_many, LoadedMany};
use uuid::Uuid;

#[dataloader]
pub async fn get_accounts(ctx: &Ctx, pages: &[&Page]) -> Result<LoadedMany<Page, DbAccount>, Error> {
    Ok(dataload_many(
        pages, // keys
        |page| page, // group_by
        |page, _| DbAccount::get_page(ctx, page).scope_boxed(), // fetch
        |page, db_account| (**page, db_account), // unload
    ).await?)
}

#[dataloader]
pub async fn get_accounts_by_role_ids(
    ctx: &Ctx,
    keys: &[&(Page, Uuid)],
) -> Result<LoadedMany<(Page, Uuid), DbAccount>, Error> {
    Ok(dataload_many(
        keys, // keys
        |key| &key.0, // group_by
        // fetch
        |page, keys| async {
            let ids = keys.iter().map(|key| &key.1).collect_vec();
            DbAccount::get_by_role_ids(
                &ctx.db,
                DbAccountByRoleFilter {
                    page: Some(page),
                    role_ids: Some(&ids),
                },
            ).await
        }.scope_boxed(),
        |page, (role_id, db_account)| ((**page, role_id), db_account), // unload
    )
    .await?)
}


#[derive(Clone, Debug, InputObject)]
pub struct Page {
    #[graphql(validator(minimum = 1))]
    pub count: i64,
    #[graphql(validator(minimum = 0))]
    pub index: i64,
}

#[derive(Clone, Debug)]
pub struct DbAccount {
  pub id: Uuid,
  pub username: String,
}

#[derive(Clone, Debug)]
pub struct DbRole {
  pub id: Uuid,
  pub title: String,
}

#[derive(Clone, Debug)]
pub struct DbAccountRole {
  pub id: Uuid,
  pub account_id: Uuid,
  pub role_id: Uuid,
}

#[derive(Clone, Debug)]
pub struct DbAccountByRoleFilter<'a> {
    pub page: Option<&'a Page>,
    pub role_ids: Option<&'a [&'a Uuid]>,
}

impl DbAccount {
    pub async fn get_page<D: Db>(db: &D, page: &Page) -> Result<Vec<Self>> {
      todo!()
    }

    pub async fn get_by_role_ids<D: Db>(db: &D, filter: DbAccountByRoleFilter<'_>) -> Result<Vec<(Uuid, Self)>> {
      todo!()
    }
}

#[derive(Clone, Debug)]
pub struct Ctx;

pub type CtxLoader = DataLoader<BaseLoader<(Ctx,)>>;
```

```rust
// api layer
use async_graphql::Context;
use derive_more::{From, Into};
use service::{Ctx, CtxLoader, DbAccount, DbRole, Page};

#[derive(Clone, Debug, From, Into)]
pub struct ApiAccount(pub DbAccount);

#[derive(Clone, Debug, From, Into)]
pub struct ApiRole(pub DbRole);

#[Query]
impl Query {
    async fn accounts(&self, ctx: &Context<'_>, page: Page) -> Result<Vec<ApiAccount>> {
        Ok(ctx
            .data::<CtxLoader>()?
            .load_one(service::GetAccounts(page)) // GetAccounts is the output of the #[dataloader] attribute on service::get_accounts
            .await?
            .ok_or_else(|| todo!())?
            .into_iter()
            .map(Into::into)
            .collect())
    }

    async fn roles(&self, ctx: &Context<'_>, page: Page) -> Result<Vec<ApiRole>> {
        Ok(service::get_roles(ctx.try_into()?, page).await?.into_iter().map(Into::into).collect())
    }
}

#[Object]
impl ApiAccount {
    pub async fn id(&self) -> Uuid {
        self.0.id    
    }
    pub async username(&self) -> String {
        self.0.username.clone()
    }
}

#[Object]
impl ApiRole {
    pub async fn id(&self) -> Uuid {
        self.0.id
    }
    pub async fn title(&self) -> String {
        self.0.title.clone()
    }

    #[graphql(complexity = "page.count * child_complexity")]
    pub async fn accounts(&self, ctx: &Context<'_>, page: Page) -> Result<Vec<ApiAccount>> {
        Ok(ctx
            .data::<CtxLoader>()?
            .load_one(service::GetAccountsByRoleIds((page, self.0.id))) // GetRolesByAccountIds is the output of the #[dataloader] attribute on service::get_accounts_by_role_ids
            .await?
            .unwrap_or_default()
            .into_iter()
            .map(Into::into)
            .collect())
    }
}
```
