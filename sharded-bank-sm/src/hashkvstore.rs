use builtin::*;
use vstd::prelude::*;
use vstd::std_specs::hash::*;
use vstd::rwlock::*;
use std::collections::hash_map::*;
use std::hash::*;
use crate::logatom::*;
use crate::kvstore::*;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

/// KVStore implementation with single lock and hash table
#[verifier::reject_recursive_types(Key)]
struct HashKVState<Key, Value> {
    phy: HashMap<Key, Value>,
    inst: Tracked<KVStoreSM::Instance<Key, Value>>,
    inner: Tracked<KVStoreSM::inner<Key, Value>>,
}

struct KVPred {
    id: InstanceId
}

impl<Key, Value> RwLockPredicate<HashKVState<Key, Value>> for KVPred {
    closed spec fn inv(self, v: HashKVState<Key, Value>) -> bool {
        &&& v.inst@.id() == self.id
        &&& v.inner@.instance_id() == self.id
        &&& v.inner@.value() == v.phy@
    }
}

#[verifier::reject_recursive_types(Key)]
struct HashKVStore<Key, Value> {
    locked_state: RwLock<HashKVState<Key, Value>, KVPred>,
}

impl<Key: Eq + Hash, Value : Copy> KVStore<Key, Value> for HashKVStore<Key, Value> {
    closed spec fn id(&self) -> InstanceId
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
        -> (out: (Self, Tracked<KVStoreSM::client<Key, Value>>))
    {
        let mut phy = HashMap::new();

        let tracked (
            Tracked(inst),
            Tracked(inner),
            Tracked(client)
        ) = KVStoreSM::Instance::initialize(Map::<Key, Value>::empty(), Map::<Key, Value>::empty());

        let state = HashKVState { 
            phy: phy,
            inst: Tracked(inst),
            inner: Tracked(inner)
        };

        let ghost pred = KVPred { 
            id: inst.id()
        };

        let locked_state = RwLock::new(state, Ghost(pred));

        (HashKVStore{locked_state}, Tracked(client))
    }

    fn get<Lin: ReadLinearizer<KVStoreGetOperation<Key, Value>>>(&self, k: Key, Tracked(lin): Tracked<Lin>) 
        -> (out: (Option::<Value>, Tracked<Lin::ApplyResult>))
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let phy_result_ref = state.phy.get(&k);
        let phy_result = if phy_result_ref.is_some() { Some(*phy_result_ref.unwrap()) } else { None }; 
        
        let tracked ar = lin.apply(get_op(self.id(), k), state.inst, &state.inner, &phy_result);

        read_handle.release_read();
        (phy_result, Tracked(ar))
    }

    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, Value>>>(&self, k: Key, v: Value, tracked lin: &mut Lin) 
        -> (out: Tracked<Lin::ApplyResult>)
    {   
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost op = put_op(self.id(), k, v);
        let ghost old_phy = state.phy@;

        state.phy.insert(k, v);

        let tracked ar = lin.apply(op, (), state.inst, state.inner.borrow_mut(), &());

        lock_handle.release_write(state);
        Tracked(ar)
    }
}

}