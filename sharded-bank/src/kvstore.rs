use builtin::*;
use vstd::prelude::*;
use crate::frac::*;
use crate::logatom::*;

verus! {

/// get operation
pub struct KVStoreGetOperation<Key, Value> {
    pub id: int,
    pub k: Key,
    pub v: Option::<Value> // needed in order to provide Value as a type argument
}

impl<Key, Value> ReadOperation for KVStoreGetOperation<Key, Value> {
    type Resource = Tracked<FractionalResource<Map::<Key, Value>, 2>>;
    type ExecResult = Option::<Value>;

    open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r@.valid(self.id, 1)
        &&& r@.val().contains_key(self.k) ==> e.is_some() && r@.val()[self.k] == e.unwrap()
        &&& !r@.val().contains_key(self.k) ==> e.is_none()
    }
}

/// put operation
pub struct KVStorePutOperation<Key, Value> {
    pub id: int,
    pub k: Key,
    pub v: Value
}

impl<Key, Value> MutOperation for KVStorePutOperation<Key, Value> {
    type Resource = FractionalResource<Map::<Key, Value>, 2>;
    type ExecResult = ();
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.valid(self.id, 1)
    }

    open spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& post.valid(self.id, 1)
        &&& post.val() == pre.val().insert(self.k, self.v)
    }
}

pub open spec fn get_op<Key, Value>(id: int, k: Key) -> KVStoreGetOperation<Key, Value> {
    KVStoreGetOperation{ id: id, k: k, v: None }
}

pub open spec fn put_op<Key, Value>(id: int, k: Key, v: Value) -> KVStorePutOperation<Key, Value> {
    KVStorePutOperation{ id: id, k: k, v: v }
}

/// KVStore interface
pub trait KVStore<Key, Value> : Sized {
    spec fn id(&self) -> int;

    spec fn inv(&self) -> bool;

    spec fn new_pre() -> bool;

    /// On initialization, this store creates one fractional resource for every possible key in the map.
    /// Each key begins with an "uninitialized" value of None to represent that it is not present in the store.
    fn new() 
        -> (out: (Self, Tracked<FractionalResource<Map::<Key, Value>, 2>>))
    requires
        Self::new_pre()
    ensures 
        out.0.inv(),
        out.1@.valid(out.0.id(), 1),
        out.1@.val() == Map::<Key, Value>::empty()
    ; 

    /// Returns Some if this key is in the store, returns None otherwise.
    fn get<Lin: ReadLinearizer<KVStoreGetOperation<Key, Value>>>(&self, k: Key, lin: Tracked<Lin>) 
        -> (out: (Option::<Value>, Tracked<Lin::ApplyResult>))
    requires
        self.inv(),
        lin@.pre(get_op(self.id(), k))
    ensures 
        lin@.post(get_op(self.id(), k), out.0, out.1@)
    ;

    /// Inserts the given key-value pair into the store, overwriting the old value.
    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, Value>>>(&self, k: Key, v: Value, lin: Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    requires
        self.inv(),
        lin@.pre(put_op(self.id(), k, v))
    ensures
        lin@.post(put_op(self.id(), k, v), (), out@)
    ;
}
}