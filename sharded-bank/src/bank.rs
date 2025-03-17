use builtin::*;
use vstd::prelude::*;
use crate::frac::*;
use crate::logatom::*;

verus! {

/// bank deposit
pub struct BankDepositOperation {
    pub id: int,
    pub a: u32,
    pub v: u32
}

impl MutOperation for BankDepositOperation {
    type Resource = FractionalResource<Map::<u32, u32>, 2>;
    type ExecResult = u32;
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.valid(self.id, 1)
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] + self.v <= u32::MAX
        &&& e == r.val()[self.a] + self.v
    }

    open spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& post.valid(self.id, 1)
        &&& post.val() == pre.val().insert(self.a, (self.v + pre.val()[self.a]) as u32)
    }

    open spec fn peek_requires(self, r: Self::Resource) -> bool { 
        &&& r.valid(self.id, 1)
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool { 
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] + self.v <= u32::MAX
    }
}

/// bank withdraw
pub struct BankWithdrawOperation {
    pub id: int,
    pub a: u32,
    pub v: u32
}

impl MutOperation for BankWithdrawOperation {
    type Resource = FractionalResource<Map::<u32, u32>, 2>;
    type ExecResult = u32;
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.valid(self.id, 1)
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] - self.v >= 0
        &&& e == r.val()[self.a] - self.v
    }

    open spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& post.valid(self.id, 1)
        &&& post.val() == pre.val().insert(self.a, (pre.val()[self.a] - self.v) as u32)
    }

    open spec fn peek_requires(self, r: Self::Resource) -> bool { 
        &&& r.valid(self.id, 1)
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool { 
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] - self.v >= 0
    }
}

pub open spec fn deposit_op(id: int, a: u32, v: u32) -> BankDepositOperation {
    BankDepositOperation{ id, a, v }
}

pub open spec fn withdraw_op(id: int, a: u32, v: u32) -> BankWithdrawOperation {
    BankWithdrawOperation{ id, a, v }
}

/// Bank interface
pub trait Bank : Sized {
    spec fn id(&self) -> int;

    spec fn inv_namespace(self) -> int;

    spec fn inv(&self) -> bool;

    spec fn new_pre() -> bool;

    fn new() 
        -> (out: (Self, Tracked<FractionalResource<Map::<u32, u32>, 2>>))
    requires
        Self::new_pre()
    ensures 
        out.0.inv(),
        out.1@.valid(out.0.id(), 1),
        out.1@.val() == Map::<u32, u32>::empty()
    ; 

    /*
    fn deposit<Lin: MutLinearizer<BankDepositOperation>>(&self, a: u32, v: u32, lin: Tracked<Lin>) 
        -> (out: (u32, Tracked<Lin::ApplyResult>))
    requires
        self.inv(),
        lin@.pre(deposit_op(self.id(), a, v))
    ensures 
        lin@.post(deposit_op(self.id(), a, v), out.0, out.1@)
    ;

    fn withdraw<Lin: MutLinearizer<BankWithdrawOperation>>(&self, a: u32, v: u32, lin: Tracked<Lin>) 
        -> (out: (u32, Tracked<Lin::ApplyResult>))
    requires
        self.inv(),
        lin@.pre(withdraw_op(self.id(), a, v))
    ensures
        lin@.post(withdraw_op(self.id(), a, v), out.0, out.1@)
    ;
    */
}
}