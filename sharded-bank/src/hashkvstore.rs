use builtin::*;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::rwlock::*;
use std::collections::hash_map::*;
use std::hash::*;
use crate::frac::*;
use crate::logatom::*;
use crate::kvstore::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

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

impl<Key: Eq + Hash, Value : Copy> KVStore<Key, Value> for HashKVStore<Key, Value> {
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
        -> (out: (Self, Tracked<FractionalResource<Map::<Key, Value>, 2>>))
    {
        let mut phy = HashMap::new();
        let tracked(my_frac, client_frac) = FractionalResource::new(phy@).split(1);

        let state = HashKVState{ phy, rsrc: Tracked(my_frac) };

        let ghost pred = KVPred { id: my_frac.id() };
        let locked_state = RwLock::new(state, Ghost(pred));

        (HashKVStore{locked_state}, Tracked(client_frac))
    }

    fn get<Lin: ReadLinearizer<KVStoreGetOperation<Key, Value>>>(&self, k: Key, Tracked(lin): Tracked<Lin>) 
        -> (out: (Option::<Value>, Tracked<Lin::ApplyResult>))
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let phy_result_ref = state.phy.get(&k);
        let phy_result = if phy_result_ref.is_some() { Some(*phy_result_ref.unwrap()) } else { None };
        
        let tracked ar = lin.apply(get_op(self.id(), k), &state.rsrc, &phy_result);

        read_handle.release_read();
        (phy_result, Tracked(ar))
    }

    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, Value>>>(&self, k: Key, v: Value, Tracked(lin): Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
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