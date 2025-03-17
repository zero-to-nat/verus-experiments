use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;
use crate::logatom::*;
use crate::kvstore::*;

verus! {

pub open spec fn val_or_none(m: Map::<u32, usize>, k: u32) -> Option::<usize>
{
    if m.contains_key(k) { Some(m[k]) } else { None::<usize> }
}

pub open spec fn unwrap_or_zero_spec(val: Option::<usize>) -> usize
{
    match val {
        None => 0,
        Some(v) => v
    }
}
    
pub fn unwrap_or_zero(val: Option<usize>) -> (out: usize)
    ensures out == unwrap_or_zero_spec(val)
{
    match val {
        None => 0,
        Some(v) => v
    }
}

pub open spec fn sum_option_spec(v1: Option::<usize>, v2: Option::<usize>, sum: Option<usize>) -> bool
{
    match (v1, v2) {
        (None, None) => sum.is_none(),
        (Some(v), None) => sum.is_some() && sum.unwrap() == v,
        (None, Some(v)) => sum.is_some() && sum.unwrap() == v,
        (Some(v1), Some(v2)) => sum.is_some() && sum.unwrap() == v1 + v2
    }
}

pub fn sum_option(v1: Option::<usize>, v2: Option::<usize>) -> (out: Option::<usize>)
    requires unwrap_or_zero_spec(v1) + unwrap_or_zero_spec(v2) <= usize::MAX
    ensures sum_option_spec(v1, v2, out)
{
    match (v1, v2) {
        (None, None) => None,
        (Some(v), None) => Some(v),
        (None, Some(v)) => Some(v),
        (Some(v1), Some(v2)) => Some(v1 + v2)
    }
}

pub open spec fn diff_option_spec(v1: Option::<usize>, v2: usize, diff: Option<usize>) -> bool
{
    match v1 {
        None => diff.is_none(),
        Some(v) => diff.is_some() && diff.unwrap() == v - v2
    }
}

pub fn diff_option(v1: Option::<usize>, v2: usize) -> (out: Option::<usize>)
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
            pub left_client: KVStoreSM::client<u32, usize>,

            #[sharding(variable)]
            pub right_client: KVStoreSM::client<u32, usize>,

            #[sharding(variable)]
            pub inner: Map<u32, usize>,

            #[sharding(variable)]
            pub client: Map<u32, usize>,
        }

        init! {
            initialize(left_client: KVStoreSM::client<u32, usize>, 
                right_client: KVStoreSM::client<u32, usize>,
                innr: Map<u32, usize>,
                cl: Map<u32, usize>
            ) {
                require left_client.value() == Map::<u32, usize>::empty();
                require right_client.value() == Map::<u32, usize>::empty();
                require innr == Map::<u32, usize>::empty();
                require cl == Map::<u32, usize>::empty();

                init left_client = left_client;
                init right_client = right_client;
                init inner = innr;
                init client = cl;
            }
        }

        transition! {
            deposit(a: u32, v: usize, new_total: usize, new_left: KVStoreSM::client<u32, usize>, new_inner: Map<u32, usize>) {
                require pre.inner.contains_key(a);
                require pre.inner[a] + v <= usize::MAX;
                require new_total == pre.inner[a] + v;

                require pre.left_client.value().contains_key(a);
                require new_left.value() == pre.left_client.value().insert(a, (pre.left_client.value()[a] + v) as usize);
                require new_left.instance_id() == pre.left_client.instance_id();

                require new_inner == pre.inner.insert(a, new_total);
                
                update left_client = new_left;
                update inner = new_inner;
                update client = new_inner;
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            &&& self.inner == self.client
            &&& forall |k: u32| #![trigger val_or_none(self.inner, k)] {
                sum_option_spec(val_or_none(self.left_client.value(), k), val_or_none(self.right_client.value(), k), val_or_none(self.inner, k))
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, left_client: KVStoreSM::client<u32, usize>, right_client: KVStoreSM::client<u32, usize>, innr: Map<u32, usize>, cl: Map<u32, usize>) { }

        #[inductive(deposit)]
        fn deposit_inductive(pre: Self, post: Self, a: u32, v: usize, new_total: usize, new_left: KVStoreSM::client<u32, usize>, new_inner: Map<u32, usize>) {
            assert(post.inv()) by {
                assume(false);
            }
        }
    }
}

struct KVStoreExclusiveGetLinearizer {
    pub client: KVStoreSM::client<u32, usize>,
}

impl ReadLinearizer<KVStoreGetOperation<u32, usize>> for KVStoreExclusiveGetLinearizer {
    type ApplyResult = KVStoreSM::client<u32, usize>;

    open spec fn pre(self, op: KVStoreGetOperation<u32, usize>) -> bool {
        self.client.instance_id() == op.id
    }

    open spec fn post(self, op: KVStoreGetOperation<u32, usize>, r: <KVStoreGetOperation<u32, usize> as ReadOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.instance_id() == op.id
        &&& match r {
            None => !ar.value().contains_key(op.k),
            Some(v) => ar.value().contains_key(op.k) && ar.value()[op.k] == v
        }
        &&& self.client.value() == ar.value()
    }

    proof fn apply(tracked self, 
        op: KVStoreGetOperation<u32, usize>, 
        tracked inst: <KVStoreGetOperation<u32, usize> as ReadOperation>::Instance, 
        tracked r: &<KVStoreGetOperation<u32, usize> as ReadOperation>::Resource, 
        e: &<KVStoreGetOperation<u32, usize> as ReadOperation>::ExecResult) 
    -> (tracked out: Self::ApplyResult) 
    {
        let tracked _ = inst.borrow().get(op.k, *e, r.borrow(), &self.client);
        self.client
    }

    proof fn peek(tracked &self, op: KVStoreGetOperation<u32, usize>, tracked r: &<KVStoreGetOperation<u32, usize> as ReadOperation>::Resource) {}
}

struct KVStoreExclusivePutLinearizer {
    pub client: KVStoreSM::client<u32, usize>,
}

impl MutLinearizer<KVStorePutOperation<u32, usize>> for KVStoreExclusivePutLinearizer {
    type ApplyResult = ();

    open spec fn pre(self, op: KVStorePutOperation<u32, usize>) -> bool {
        self.client.instance_id() == op.id
    }

    open spec fn post(self, old_self: KVStoreExclusivePutLinearizer, op: KVStorePutOperation<u32, usize>, r: <KVStorePutOperation<u32, usize> as MutOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& self.client.instance_id() == op.id
        &&& self.client.value() == old_self.client.value().insert(op.k, op.v)
    }

    proof fn apply(tracked &mut self, 
        op: KVStorePutOperation<u32, usize>, 
        hint: <KVStorePutOperation<u32, usize> as MutOperation>::ApplyHint, 
        tracked inst: <KVStorePutOperation<u32, usize> as MutOperation>::Instance,
        tracked r: &mut <KVStorePutOperation<u32, usize> as MutOperation>::Resource, 
        e: &<KVStorePutOperation<u32, usize> as MutOperation>::ExecResult,) 
    -> (tracked out: Self::ApplyResult) 
    {
        //let tracked _ = inst.borrow().agree(r, &self.client); // needed to show that old(self).client.value() == old(r).value()
        let tracked _ = inst.borrow().put(op.k, op.v, r.value().insert(op.k, op.v), r, &mut self.client);
        ()
    }

    proof fn peek(tracked &self, op: KVStorePutOperation<u32, usize>, tracked r: &<KVStorePutOperation<u32, usize> as MutOperation>::Resource) {}
}

}