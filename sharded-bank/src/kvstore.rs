use builtin::*;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
//use vstd::invariant::*;
use vstd::rwlock::*;
use std::collections::hash_map::*;
use std::hash::*;
use crate::frac::*;
use crate::logatom::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

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

/// KVStore implementation with single lock and hash table
#[verifier::reject_recursive_types(Key)]
struct HashKVState<Key, Value> {
    phy: HashMap<Key, Value>,
    rsrc: Tracked<FractionalResource<Map::<Key, Value>, 2>>,
}

struct KVPred {
    id: int
}

impl<Key, Value> RwLockPredicate<HashKVState<Key, Value>> for KVPred {
    closed spec fn inv(self, v: HashKVState<Key, Value>) -> bool {
        &&& v.rsrc@.valid(self.id, 1)
        &&& v.rsrc@.val() == v.phy@
    }
}

#[verifier::reject_recursive_types(Key)]
struct HashKVStore<Key, Value> {
    locked_state: RwLock<HashKVState<Key, Value>, KVPred>,
}

impl<Key: Eq + Hash> KVStore<Key, usize> for HashKVStore<Key, usize> {
    closed spec fn id(&self) -> int
    {
        self.locked_state.pred().id
    }

    open spec fn inv(&self) -> bool {
        &&& obeys_key_model::<Key>()
    }

    open spec fn new_pre() -> bool {
        obeys_key_model::<Key>()
    }

    fn new() 
        -> (out: (Self, Tracked<FractionalResource<Map::<Key, usize>, 2>>))
    // ensures
    //     out.0.inv(),
    //     out.1@.valid(out.0.id(), 1),
    //     forall |k: Key| #![trigger out.1@.val().contains_key(k)]
    //     {
    //         &&& !out.1@.val().contains_key(k)
    //     };
    {
        let mut phy = HashMap::new();
        let tracked(my_frac, client_frac) = FractionalResource::new(phy@).split(1);

        let state = HashKVState{ phy, rsrc: Tracked(my_frac) };

        let ghost pred = KVPred { id: my_frac.id() };
        let locked_state = RwLock::new(state, Ghost(pred));

        (HashKVStore{locked_state}, Tracked(client_frac))
    }

    fn get<Lin: ReadLinearizer<KVStoreGetOperation<Key, usize>>>(&self, k: Key, Tracked(lin): Tracked<Lin>) 
        -> (out: (Option::<usize>, Tracked<Lin::ApplyResult>))
    // requires
    //     self.inv(),
    //     lin@.pre(self.get_op(k))
    // ensures 
    //     lin@.post(self.get_op(k), out.0, out.1@)
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let phy_result_ref = state.phy.get(&k);
        let phy_result = if phy_result_ref.is_some() { Some(*phy_result_ref.unwrap()) } else { None };  // could use clone + extra assumption about equality
        
        let tracked ar = lin.apply(get_op(self.id(), k), &state.rsrc, &phy_result);

        read_handle.release_read();
        (phy_result, Tracked(ar))
    }

    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, usize>>>(&self, k: Key, v: usize, Tracked(lin): Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    // requires
    //     old(self).inv(),
    //     lin@.pre(old(self).put_op(k, v))
    // ensures
    //     self.inv(),
    //     self.id() == old(self).id(),
    //     lin@.post(old(self).put_op(k, v), (), out@)
    {   
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost op = put_op(self.id(), k, v);
        let ghost old_phy = state.phy@;

        state.phy.insert(k, v);

        let tracked ar = lin.apply(op, (), state.rsrc.borrow_mut(), &());

        lock_handle.release_write(state);
        Tracked(ar)
    }

}
}