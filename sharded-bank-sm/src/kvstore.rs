use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;
use std::marker::PhantomData;
use crate::logatom::*;

verus! {

tokenized_state_machine! {
    #[verifier::reject_recursive_types(Key)]
    KVStoreSM<Key, Value> {
        fields {
            #[sharding(variable)]
            pub inner: Map<Key, Value>,

            #[sharding(variable)]
            pub client: Map<Key, Value>
        }

        init! {
            initialize(innr: Map<Key, Value>, cl: Map<Key, Value>) 
            {
                require innr == Map::<Key, Value>::empty();
                require cl == Map::<Key, Value>::empty();

                init inner = innr;
                init client = cl;
            }
        }

        property! {
            get(k: Key, v: Option<Value>) {
                require pre.inner.contains_key(k) ==> v == Some(pre.inner[k]);
                require !pre.inner.contains_key(k) ==> v == None::<Value>;

                assert pre.client == pre.inner by {
                    assert(pre.inv());
                };
            }
        }

        transition! {
            put(k: Key, v: Value, new_inner: Map<Key, Value>) {
                assert pre.client == pre.inner by {
                    assert(pre.inv());
                };

                require new_inner == pre.inner.insert(k, v);
                
                update inner = new_inner;
                update client = new_inner;
            }
        }

        property! {
            agree() {
                assert pre.client == pre.inner by {
                    assert(pre.inv());
                };
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            &&& self.inner == self.client
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, innr: Map<Key, Value>, cl: Map<Key, Value>) { }
              
        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, k: Key, v: Value, new_inner: Map<Key, Value>) { }
    }
}

/// get operation
pub struct KVStoreGetOperation<Key, Value> {
    pub id: InstanceId,
    pub k: Key,
    pub v: PhantomData<Value>
}

impl<Key, Value> ReadOperation for KVStoreGetOperation<Key, Value> {
    type Instance = Tracked<KVStoreSM::Instance<Key, Value>>;
    type Resource = Tracked<KVStoreSM::inner<Key, Value>>;
    type ExecResult = Option::<Value>;

    open spec fn requires(self, inst: Self::Instance, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == r@.instance_id()
        &&& r@.value().contains_key(self.k) ==> e.is_some() && r@.value()[self.k] == e.unwrap()
        &&& !r@.value().contains_key(self.k) ==> e.is_none()
    }
}

/// put operation
pub struct KVStorePutOperation<Key, Value> {
    pub id: InstanceId,
    pub k: Key,
    pub v: Value
}

impl<Key, Value> MutOperation for KVStorePutOperation<Key, Value> {
    type Instance = Tracked<KVStoreSM::Instance<Key, Value>>;
    type Resource = KVStoreSM::inner<Key, Value>;
    type ExecResult = ();
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, inst: Self::Instance, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == r.instance_id()
    }

    open spec fn ensures(self, hint: Self::ApplyHint, inst: Self::Instance, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == post.instance_id()
        &&& post.value() == pre.value().insert(self.k, self.v)
    }
}

pub open spec fn get_op<Key, Value>(id: InstanceId, k: Key) -> KVStoreGetOperation<Key, Value> {
    KVStoreGetOperation{ id: id, k: k, v: PhantomData }
}

pub open spec fn put_op<Key, Value>(id: InstanceId, k: Key, v: Value) -> KVStorePutOperation<Key, Value> {
    KVStorePutOperation{ id: id, k: k, v: v }
}

/// KVStore interface
pub trait KVStore<Key, Value> : Sized {
    spec fn id(&self) -> InstanceId;

    spec fn inv(&self) -> bool;

    spec fn new_pre() -> bool;

    /// On initialization, this store creates one fractional resource for every possible key in the map.
    /// Each key begins with an "uninitialized" value of None to represent that it is not present in the store.
    fn new() 
        -> (out: (Self, Tracked<KVStoreSM::client<Key, Value>>))
    requires
        Self::new_pre()
    ensures 
        out.0.inv(),
        out.0.id() == out.1@.instance_id(),
        out.1@.value() == Map::<Key, Value>::empty()
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
    fn put<Lin: MutLinearizer<KVStorePutOperation<Key, Value>>>(&self, k: Key, v: Value, tracked lin: &mut Lin) 
        -> (out: Tracked<Lin::ApplyResult>)
    requires
        self.inv(),
        old(lin).pre(put_op(self.id(), k, v))
    ensures
        lin.post(*old(lin), put_op(self.id(), k, v), (), out@)
    ;
}
}