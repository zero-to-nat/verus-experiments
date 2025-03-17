use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;
use crate::logatom::*;
use crate::kvstore::*;

verus! {

pub open spec fn val_or_none(m: Map::<u32, u32>, k: u32) -> Option::<u32>
{
    if m.contains_key(k) { Some(m[k]) } else { None::<u32> }
}

pub open spec fn unwrap_or_zero_spec(val: Option::<u32>) -> u32
{
    match val {
        None => 0,
        Some(v) => v
    }
}
    
pub fn unwrap_or_zero(val: Option<u32>) -> (out: u32)
    ensures out == unwrap_or_zero_spec(val)
{
    match val {
        None => 0,
        Some(v) => v
    }
}

pub open spec fn sum_option_spec(v1: Option::<u32>, v2: Option::<u32>, sum: Option<u32>) -> bool
{
    match (v1, v2) {
        (None, None) => sum.is_none(),
        (Some(v), None) => sum.is_some() && sum.unwrap() == v,
        (None, Some(v)) => sum.is_some() && sum.unwrap() == v,
        (Some(v1), Some(v2)) => sum.is_some() && sum.unwrap() == v1 + v2
    }
}

pub fn sum_option(v1: Option::<u32>, v2: Option::<u32>) -> (out: Option::<u32>)
    requires unwrap_or_zero_spec(v1) + unwrap_or_zero_spec(v2) <= u32::MAX
    ensures sum_option_spec(v1, v2, out)
{
    match (v1, v2) {
        (None, None) => None,
        (Some(v), None) => Some(v),
        (None, Some(v)) => Some(v),
        (Some(v1), Some(v2)) => Some(v1 + v2)
    }
}

pub open spec fn diff_option_spec(v1: Option::<u32>, v2: u32, diff: Option<u32>) -> bool
{
    match v1 {
        None => diff.is_none(),
        Some(v) => diff.is_some() && diff.unwrap() == v - v2
    }
}

pub fn diff_option(v1: Option::<u32>, v2: u32) -> (out: Option::<u32>)
    requires v2 <= unwrap_or_zero_spec(v1)
    ensures diff_option_spec(v1, v2, out)
{
    match v1 {
        None => None,
        Some(v) => Some(v - v2),
    }
}

tokenized_state_machine! {
    ShardedBankSM {
        fields {
            #[sharding(variable)]
            pub left_client: KVStoreSM::client<u32, u32>,

            #[sharding(variable)]
            pub right_client: KVStoreSM::client<u32, u32>,

            #[sharding(variable)]
            pub inner: Map<u32, u32>,

            #[sharding(variable)]
            pub client: Map<u32, u32>,
        }

        init! {
            initialize(left_client: KVStoreSM::client<u32, u32>, 
                right_client: KVStoreSM::client<u32, u32>,
                innr: Map<u32, u32>,
                cl: Map<u32, u32>
            ) {
                require left_client.value() == Map::<u32, u32>::empty();
                require right_client.value() == Map::<u32, u32>::empty();
                require innr == Map::<u32, u32>::empty();
                require cl == Map::<u32, u32>::empty();

                init left_client = left_client;
                init right_client = right_client;
                init inner = innr;
                init client = cl;
            }
        }

        transition! {
            deposit(a: u32, v: u32, new_total: u32, new_left: KVStoreSM::client<u32, u32>, new_right: KVStoreSM::client<u32, u32>, new_inner: Map<u32, u32>) {
                require pre.inner.contains_key(a);
                require pre.inner[a] + v <= u32::MAX;
                require new_total == pre.inner[a] + v;

                require new_inner == pre.inner.insert(a, new_total);
                require forall |k: u32| #![trigger new_inner.contains_key(k)] sum_option_spec(val_or_none(new_left.value(), k), val_or_none(new_right.value(), k), val_or_none(new_inner, k));
                require new_left.instance_id() == pre.left_client.instance_id();
                require new_right.instance_id() == pre.right_client.instance_id();
                
                update left_client = new_left;
                update right_client = new_right;
                update inner = new_inner;
                update client = new_inner;
            }
        }

        transition! {
            withdraw(a: u32, v: u32, new_total: u32, new_left: KVStoreSM::client<u32, u32>, new_right: KVStoreSM::client<u32, u32>, new_inner: Map<u32, u32>) {
                require pre.inner.contains_key(a);
                require 0 <= pre.inner[a] - v;
                require new_total == pre.inner[a] - v;

                require new_inner == pre.inner.insert(a, new_total);
                require forall |k: u32| #![trigger new_inner.contains_key(k)] sum_option_spec(val_or_none(new_left.value(), k), val_or_none(new_right.value(), k), val_or_none(new_inner, k));
                require new_left.instance_id() == pre.left_client.instance_id();
                require new_right.instance_id() == pre.right_client.instance_id();
                
                update left_client = new_left;
                update right_client = new_right;
                update inner = new_inner;
                update client = new_inner;
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            &&& self.inner == self.client
            &&& forall |k: u32| #![trigger self.inner.contains_key(k)] {
                sum_option_spec(val_or_none(self.left_client.value(), k), val_or_none(self.right_client.value(), k), val_or_none(self.inner, k))
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, left_client: KVStoreSM::client<u32, u32>, right_client: KVStoreSM::client<u32, u32>, innr: Map<u32, u32>, cl: Map<u32, u32>) { }

        #[inductive(deposit)]
        fn deposit_inductive(pre: Self, post: Self, a: u32, v: u32, new_total: u32, new_left: KVStoreSM::client<u32, u32>, new_right: KVStoreSM::client<u32, u32>, new_inner: Map<u32, u32>) { }

        #[inductive(withdraw)]
        fn withdraw_inductive(pre: Self, post: Self, a: u32, v: u32, new_total: u32, new_left: KVStoreSM::client<u32, u32>, new_right: KVStoreSM::client<u32, u32>, new_inner: Map<u32, u32>) { }
    }
}

struct KVStoreExclusiveGetLinearizer {
    pub client: KVStoreSM::client<u32, u32>,
}

impl ReadLinearizer<KVStoreGetOperation<u32, u32>> for KVStoreExclusiveGetLinearizer {
    type ApplyResult = KVStoreSM::client<u32, u32>;

    open spec fn pre(self, op: KVStoreGetOperation<u32, u32>) -> bool {
        self.client.instance_id() == op.id
    }

    open spec fn post(self, op: KVStoreGetOperation<u32, u32>, r: <KVStoreGetOperation<u32, u32> as ReadOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.instance_id() == op.id
        &&& match r {
            None => !ar.value().contains_key(op.k),
            Some(v) => ar.value().contains_key(op.k) && ar.value()[op.k] == v
        }
        &&& self.client.value() == ar.value()
    }

    proof fn apply(tracked self, 
        op: KVStoreGetOperation<u32, u32>, 
        tracked inst: <KVStoreGetOperation<u32, u32> as ReadOperation>::Instance, 
        tracked r: &<KVStoreGetOperation<u32, u32> as ReadOperation>::Resource, 
        e: &<KVStoreGetOperation<u32, u32> as ReadOperation>::ExecResult) 
    -> (tracked out: Self::ApplyResult) 
    {
        let tracked _ = inst.borrow().get(op.k, *e, r.borrow(), &self.client);
        self.client
    }

    proof fn peek(tracked &self, op: KVStoreGetOperation<u32, u32>, tracked r: &<KVStoreGetOperation<u32, u32> as ReadOperation>::Resource) {}
}

struct KVStoreExclusivePutLinearizer {
    pub client: KVStoreSM::client<u32, u32>,
}

impl MutLinearizer<KVStorePutOperation<u32, u32>> for KVStoreExclusivePutLinearizer {
    type ApplyResult = ();

    open spec fn pre(self, op: KVStorePutOperation<u32, u32>) -> bool {
        self.client.instance_id() == op.id
    }

    open spec fn post(self, old_self: KVStoreExclusivePutLinearizer, op: KVStorePutOperation<u32, u32>, r: <KVStorePutOperation<u32, u32> as MutOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& self.client.instance_id() == op.id
        &&& self.client.value() == old_self.client.value().insert(op.k, op.v)
    }

    proof fn apply(tracked &mut self, 
        op: KVStorePutOperation<u32, u32>, 
        hint: <KVStorePutOperation<u32, u32> as MutOperation>::ApplyHint, 
        tracked inst: <KVStorePutOperation<u32, u32> as MutOperation>::Instance,
        tracked r: &mut <KVStorePutOperation<u32, u32> as MutOperation>::Resource, 
        e: &<KVStorePutOperation<u32, u32> as MutOperation>::ExecResult,) 
    -> (tracked out: Self::ApplyResult) 
    {
        let tracked _ = inst.borrow().put(op.k, op.v, r.value().insert(op.k, op.v), r, &mut self.client);
        ()
    }

    proof fn peek(tracked &self, op: KVStorePutOperation<u32, u32>, tracked r: &<KVStorePutOperation<u32, u32> as MutOperation>::Resource) {}
}

}