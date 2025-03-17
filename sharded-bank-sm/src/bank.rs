use builtin::*;
use vstd::prelude::*;
use state_machines_macros::*;
use crate::logatom::*;

verus! {

tokenized_state_machine! {
    BankSM {
        fields {
            #[sharding(variable)]
            pub inner: Map<u32, u32>,

            #[sharding(option)]
            pub client: Option<Map<u32, u32>>,
        }

        init! {
            initialize() {
                init inner = Map::<u32, u32>::empty();
                init client = Some(Map::<u32, u32>::empty());
            }
        }

        transition! {
            deposit(a: u32, v: u32) {
                remove client -= Some(let old_cl);

                assert pre.inner == old_cl by {
                    assert(pre.inv());
                };
                
                require pre.inner.contains_key(a);
                require pre.inner[a] + v <= u32::MAX;

                update inner = pre.inner.insert(a, (pre.inner[a] + v) as u32);
                add client += Some(pre.inner.insert(a, (pre.inner[a] + v) as u32));
            }
        }

        transition! {
            withdraw(a: u32, v: u32) {
                remove client -= Some(let old_cl);

                assert pre.inner == old_cl by {
                    assert(pre.inv());
                };

                require pre.inner.contains_key(a);
                require 0 <= pre.inner[a] - v;

                update inner = pre.inner.insert(a, (pre.inner[a] - v) as u32);
                add client += Some(pre.inner.insert(a, (pre.inner[a] - v) as u32));
            }
        }

        #[invariant]
        pub spec fn inv(&self) -> bool {
            &&& self.client.is_some()
            &&& self.inner == self.client.unwrap()
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(deposit)]
        fn deposit_inductive(pre: Self, post: Self, a: u32, v: u32) { }

        #[inductive(withdraw)]
        fn withdraw_inductive(pre: Self, post: Self, a: u32, v: u32) { }
    }
}

/// bank deposit
pub struct BankDepositOperation {
    pub id: InstanceId,
    pub a: u32,
    pub v: u32
}

impl MutOperation for BankDepositOperation {
    type Instance = Tracked<BankSM::Instance>;
    type Resource = BankSM::inner;
    type ExecResult = ();
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, inst: Self::Instance, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == r.instance_id()
        &&& r.value().contains_key(self.a)
        &&& r.value()[self.a] + self.v <= u32::MAX
    }

    open spec fn ensures(self, hint: Self::ApplyHint, inst: Self::Instance, pre: Self::Resource, post: Self::Resource) -> bool {
        //&&& inst@.id() == self.id
        &&& inst@.id() == post.instance_id()
        &&& post.value() == pre.value().insert(self.a, (self.v + pre.value()[self.a]) as u32)
    }

    open spec fn peek_requires(self, inst: Self::Instance, r: Self::Resource) -> bool { 
        &&& inst@.id() == self.id
        &&& inst@.id() == r.instance_id()
    }

    open spec fn peek_ensures(self, inst: Self::Instance, r: Self::Resource) -> bool { 
        &&& r.value().contains_key(self.a)
        &&& r.value()[self.a] + self.v <= u32::MAX
    }
}

/// bank withdraw
pub struct BankWithdrawOperation {
    pub id: InstanceId,
    pub a: u32,
    pub v: u32
}

impl MutOperation for BankWithdrawOperation {
    type Instance = Tracked<BankSM::Instance>;
    type Resource = BankSM::inner;
    type ExecResult = ();
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, inst: Self::Instance, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& inst@.id() == self.id
        &&& inst@.id() == r.instance_id()
        &&& r.value().contains_key(self.a)
        &&& 0 <= r.value()[self.a] - self.v
    }

    open spec fn ensures(self, hint: Self::ApplyHint, inst: Self::Instance, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& inst@.id() == post.instance_id()
        &&& post.value() == pre.value().insert(self.a, (pre.value()[self.a] - self.v) as u32)
    }

    open spec fn peek_requires(self, inst: Self::Instance, r: Self::Resource) -> bool { 
        &&& inst@.id() == self.id
        &&& inst@.id() == r.instance_id()
    }

    open spec fn peek_ensures(self, inst: Self::Instance, r: Self::Resource) -> bool { 
        &&& r.value().contains_key(self.a)
        &&& 0 <= r.value()[self.a] - self.v
    }
}

pub open spec fn deposit_op(id: InstanceId, a: u32, v: u32) -> BankDepositOperation {
    BankDepositOperation{ id, a, v }
}

pub open spec fn withdraw_op(id: InstanceId, a: u32, v: u32) -> BankWithdrawOperation {
    BankWithdrawOperation{ id, a, v }
}

/// Bank interface
pub trait Bank : Sized {
    spec fn id(&self) -> InstanceId;

    spec fn inv_namespace(self) -> int;

    spec fn inv(&self) -> bool;

    spec fn new_pre() -> bool;

    fn new() 
        -> (out: (Self, Tracked<BankSM::client>))
    requires
        Self::new_pre()
    ensures 
        out.0.inv(),
        out.1@.instance_id() == out.0.id(),
        out.1@.value() == Map::<u32, u32>::empty()
    ; 

    fn deposit<Lin: MutLinearizer<BankDepositOperation>>(&self, a: u32, v: u32, lin: Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    requires
        self.inv(),
        lin@.pre(deposit_op(self.id(), a, v))
    ensures 
        lin@.post(deposit_op(self.id(), a, v), (), out@)
    ;

    fn withdraw<Lin: MutLinearizer<BankWithdrawOperation>>(&self, a: u32, v: u32, lin: Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    requires
        self.inv(),
        lin@.pre(withdraw_op(self.id(), a, v))
    ensures
        lin@.post(withdraw_op(self.id(), a, v), (), out@)
    ;
}

}