use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use std::collections::hash_map::*;
//use vstd::std_specs::hash::*;
//use vstd::modes::*;
//use vstd::invariant::*;
//use std::sync::Arc;
//use vstd::thread::*;
use state_machines_macros::tokenized_state_machine;

verus! {
broadcast use vstd::std_specs::hash::group_hash_axioms;

pub type Key = u64; // NOTE: usize doesn't implement key model, not reasonable
pub type Value = usize;

tokenized_state_machine! {
    KVStoreSM {
        fields {
            #[sharding(map)]
            pub tok: Map<Key, Option<Value>>,
        }

        init! {
            initialize() {
                init tok = Map::<Key, Option<Value>>::new(|k| true, |k| None::<Value>);
            }
        }

        transition! {
            get(k: Key, v: Value) {
                have tok >= [k => Some(v)];
            }
        }

        transition! {
            set(k: Key, v: Value) {
                remove tok -= [k => let Some(_)];
                add tok += [k => Some(v)];
            }
        }
    }
}

pub struct KVState {
    pub phy: HashMap<Key, Value>,
    pub inst: Tracked<KVStoreSM::Instance>,
    pub tokens: Tracked<Map<Key, KVStoreSM::tok>>
}

struct KVPred {
    pub keys: Set<Key>
}

impl RwLockPredicate<KVState> for KVPred {
    closed spec fn inv(self, kv: KVState) -> bool {
        forall |k| #[trigger] self.keys.contains(k)
        ==> {
            &&& kv.phy@.contains_key(k)
            &&& kv.tokens@.contains_key(k)
            &&& kv.tokens@[k]@.key == k
            &&& kv.tokens@[k]@.instance == kv.inst@
            &&& kv.tokens@[k]@.value.is_some()
            &&& kv.tokens@[k]@.value.unwrap() == kv.phy@[k]
        }

    }
}

struct KVStore {
    locked_state: RwLock<KVState, KVPred>,
}

impl KVStore {
    spec fn keys(&self) -> Set<Key>
    {
        self.locked_state.pred().keys
    }

    fn new() -> Self {
        let mut phy = HashMap::<Key, Value>::new();
        let tracked (
            Tracked(inst),
            Tracked(tokens)
        ) = KVStoreSM::Instance::initialize();

        let state = KVState { 
            phy: phy, 
            inst: Tracked(inst),
            tokens: Tracked(tokens)
        };

        let ghost pred = KVPred{ keys: Set::<Key>::empty() };
        let locked_state = RwLock::new(state, Ghost(pred));

        return KVStore { locked_state };
    }

    fn get(&self, k: Key) -> (v: Value) 
        requires self.keys().contains(k)
        // postcondition: we want some way to relate the return value to either the physical or ghost state of the KVStore?
    {
        let read_handle = self.locked_state.acquire_read();
        let state = read_handle.borrow();

        let phy_result_ref = state.phy.get(&k);
        let phy_result = *phy_result_ref.unwrap();

        let tracked token = state.tokens.borrow().tracked_borrow(k);
        let tracked _ = state.inst.borrow().get(k, phy_result, &token);

        read_handle.release_read();
        return phy_result;
    }

    fn set(&self, k: Key, v: Value) 
        requires self.keys().contains(k)
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();
        let ghost old_phy = state.phy@;

        state.phy.insert(k, v);

        let tracked token = state.tokens.borrow_mut().tracked_remove(k);
        let tracked new_token = state.inst.borrow().set(k, v, token);
        proof { 
            state.tokens.borrow_mut().tracked_insert(k, new_token); 
        }

        assert(old_phy.dom() =~= state.phy@.dom());
        lock_handle.release_write(state);
    }
}

fn main() {

}
}