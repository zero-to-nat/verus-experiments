use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use crate::frac::*;
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

/// bank deposit
pub struct BankDepositOperation {
    pub id: int,
    pub a: u32,
    pub v: usize
}

impl MutOperation for BankDepositOperation {
    type Resource = FractionalResource<Map::<u32, usize>, 2>;
    type ExecResult = usize;
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.valid(self.id, 1)
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] + self.v <= usize::MAX
        &&& e == r.val()[self.a] + self.v
    }

    open spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& post.valid(self.id, 1)
        &&& post.val() == pre.val().insert(self.a, (self.v + pre.val()[self.a]) as usize)
    }

    open spec fn peek_requires(self, r: Self::Resource) -> bool { 
        &&& r.valid(self.id, 1)
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool { 
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] + self.v <= usize::MAX
    }
}

/// bank withdraw
pub struct BankWithdrawOperation {
    pub id: int,
    pub a: u32,
    pub v: usize
}

impl MutOperation for BankWithdrawOperation {
    type Resource = FractionalResource<Map::<u32, usize>, 2>;
    type ExecResult = usize;
    type ApplyHint = ();

    open spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool {
        &&& r.valid(self.id, 1)
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] - self.v >= 0
        &&& e == r.val()[self.a] - self.v
    }

    open spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool {
        &&& post.valid(self.id, 1)
        &&& post.val() == pre.val().insert(self.a, (pre.val()[self.a] - self.v) as usize)
    }

    open spec fn peek_requires(self, r: Self::Resource) -> bool { 
        &&& r.valid(self.id, 1)
    }

    open spec fn peek_ensures(self, r: Self::Resource) -> bool { 
        &&& r.val().contains_key(self.a)
        &&& r.val()[self.a] - self.v >= 0
    }
}

pub open spec fn deposit_op(id: int, a: u32, v: usize) -> BankDepositOperation {
    BankDepositOperation{ id, a, v }
}

pub open spec fn withdraw_op(id: int, a: u32, v: usize) -> BankWithdrawOperation {
    BankWithdrawOperation{ id, a, v }
}

struct ShardedBankLockedState {
    left_client: Tracked<FractionalResource<Map::<u32, usize>, 2>>,
    right_client: Tracked<FractionalResource<Map::<u32, usize>, 2>>,
    bank_owned: Tracked<FractionalResource<Map::<u32, usize>, 2>>,
}

struct ShardedBankPred {
    left_id: int,
    right_id: int,
    bank_id: int
}

impl RwLockPredicate<ShardedBankLockedState> for ShardedBankPred {
    closed spec fn inv(self, v: ShardedBankLockedState) -> bool {
        &&& v.left_client@.valid(self.left_id, 1)
        &&& v.right_client@.valid(self.right_id, 1)
        &&& v.bank_owned@.valid(self.bank_id, 1)
        &&& forall |k: u32| #![trigger val_or_none(v.bank_owned@.val(), k)] {
            sum_option_spec(val_or_none(v.left_client@.val(), k), val_or_none(v.right_client@.val(), k), val_or_none(v.bank_owned@.val(), k))
        }
    }
}

struct ShardedBank<Store: KVStore<u32, usize>>  {
    pub locked_state: RwLock<ShardedBankLockedState, ShardedBankPred>,
    pub left_store: Store,
    pub right_store: Store
}

struct KVStoreExclusiveGetLinearizer {
    pub client: FractionalResource<Map::<u32, usize>, 2>,
}

impl ReadLinearizer<KVStoreGetOperation<u32, usize>> for KVStoreExclusiveGetLinearizer {
    type ApplyResult = FractionalResource<Map::<u32, usize>, 2>;

    open spec fn pre(self, op: KVStoreGetOperation<u32, usize>) -> bool {
        self.client.valid(op.id, 1)
    }

    open spec fn post(self, op: KVStoreGetOperation<u32, usize>, r: <KVStoreGetOperation<u32, usize> as ReadOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.valid(op.id, 1)
        &&& match r {
            None => !ar.val().contains_key(op.k),
            Some(v) => ar.val().contains_key(op.k) && ar.val()[op.k] == v
        }
        &&& self.client.val() == ar.val()
    }

    proof fn apply(tracked self, op: KVStoreGetOperation<u32, usize>, tracked r: &<KVStoreGetOperation<u32, usize> as ReadOperation>::Resource, e: &<KVStoreGetOperation<u32, usize> as ReadOperation>::ExecResult) -> (tracked out: Self::ApplyResult) {
        self.client.agree(r.borrow());
        self.client
    }

    proof fn peek(tracked &self, op: KVStoreGetOperation<u32, usize>, tracked r: &<KVStoreGetOperation<u32, usize> as ReadOperation>::Resource) {}
}

struct KVStoreExclusivePutLinearizer {
    pub client: FractionalResource<Map::<u32, usize>, 2>,
}

impl MutLinearizer<KVStorePutOperation<u32, usize>> for KVStoreExclusivePutLinearizer {
    type ApplyResult = FractionalResource<Map::<u32, usize>, 2>;

    open spec fn pre(self, op: KVStorePutOperation<u32, usize>) -> bool {
        self.client.valid(op.id, 1)
    }

    open spec fn post(self, op: KVStorePutOperation<u32, usize>, r: <KVStorePutOperation<u32, usize> as MutOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.valid(op.id, 1)
        &&& ar.val() == self.client.val().insert(op.k, op.v)
    }

    proof fn apply(tracked self, op: KVStorePutOperation<u32, usize>, hint: <KVStorePutOperation<u32, usize> as MutOperation>::ApplyHint, tracked r: &mut <KVStorePutOperation<u32, usize> as MutOperation>::Resource, e: &<KVStorePutOperation<u32, usize> as MutOperation>::ExecResult) -> (tracked out: Self::ApplyResult) {
        r.combine_mut(self.client);
        r.update_mut(r.val().insert(op.k, op.v));
        let tracked out = r.split_mut(1);
        out
    }

    proof fn peek(tracked &self, op: KVStorePutOperation<u32, usize>, tracked r: &<KVStorePutOperation<u32, usize> as MutOperation>::Resource) {}
}

impl<Store: KVStore<u32, usize>> ShardedBank<Store> {
    spec fn id(&self) -> int {
        self.locked_state.pred().bank_id
    }

    spec fn inv(&self) -> bool {
        &&& self.left_store.inv()
        &&& self.right_store.inv()
        &&& self.left_store.id() == self.locked_state.pred().left_id
        &&& self.right_store.id() == self.locked_state.pred().right_id
    }

    fn deposit<Lin: MutLinearizer<BankDepositOperation>>(&self, a: u32, v: usize, lin: Tracked<Lin>) 
        -> (new_balance: usize)
        requires
            self.inv(),
            lin@.pre(deposit_op(self.id(), a, v))
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        proof { lin.borrow().peek(deposit_op(self.id(), a, v), state.bank_owned.borrow()) };
        assert(unwrap_or_zero_spec(val_or_none(state.bank_owned@.val(), a)) + v <= usize::MAX);

        assert(forall |k| sum_option_spec(val_or_none(state.left_client@.val(), k), val_or_none(state.right_client@.val(), k), val_or_none(state.bank_owned@.val(), k)));

        let left_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.left_client.get() });
        let (old_left, left_client) = self.left_store.get::<KVStoreExclusiveGetLinearizer>(a, left_lin);
        state.left_client = left_client;

        let right_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.right_client.get() });
        let (old_right, right_client) = self.right_store.get::<KVStoreExclusiveGetLinearizer>(a, right_lin);
        state.right_client = right_client;

        let new_left_balance = sum_option(old_left, Some(v));
        let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.left_client.get() });
        let left_client = self.left_store.put::<KVStoreExclusivePutLinearizer>(a, new_left_balance.unwrap(), put_lin);
        state.left_client = left_client;

        let new_balance = sum_option(new_left_balance, old_right).unwrap();
        assert(new_balance == unwrap_or_zero_spec(val_or_none(state.bank_owned@.val(), a)) + v);
        let tracked ar = lin.get().apply(deposit_op(self.id(), a, v), (), state.bank_owned.borrow_mut(), &new_balance);

        lock_handle.release_write(state);
        new_balance
    }

    fn withdraw<Lin: MutLinearizer<BankWithdrawOperation>>(&self, a: u32, v: usize, lin: Tracked<Lin>) 
        -> (new_balance: usize)
        requires
            self.inv(),
            lin@.pre(withdraw_op(self.id(), a, v))
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        proof { lin.borrow().peek(withdraw_op(self.id(), a, v), state.bank_owned.borrow()) };
        assert(unwrap_or_zero_spec(val_or_none(state.bank_owned@.val(), a)) - v >= 0);

        assert(forall |k| sum_option_spec(val_or_none(state.left_client@.val(), k), val_or_none(state.right_client@.val(), k), val_or_none(state.bank_owned@.val(), k)));
        let ghost ghost_left_client = state.left_client;
        let ghost ghost_bank = state.bank_owned;

        let left_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.left_client.get() });
        let (old_left, left_client) = self.left_store.get::<KVStoreExclusiveGetLinearizer>(a, left_lin);
        state.left_client = left_client;

        let right_lin = Tracked(KVStoreExclusiveGetLinearizer { client: state.right_client.get() });
        let (old_right, right_client) = self.right_store.get::<KVStoreExclusiveGetLinearizer>(a, right_lin);
        state.right_client = right_client;

        let left_withdraw_amt = if (v > unwrap_or_zero(old_left)) { unwrap_or_zero(old_left) } else { v };
        let right_withdraw_amt = if (v > unwrap_or_zero(old_left)) { v - left_withdraw_amt } else { 0 };
        let new_left_balance = diff_option(old_left, left_withdraw_amt);
        let new_right_balance = diff_option(old_right, right_withdraw_amt);

        if (left_withdraw_amt > 0) {
            let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.left_client.get() });
            let left_client = self.left_store.put::<KVStoreExclusivePutLinearizer>(a, new_left_balance.unwrap(), put_lin); 
            state.left_client = left_client;
        }

        if (right_withdraw_amt > 0) {
            let put_lin = Tracked(KVStoreExclusivePutLinearizer { client: state.right_client.get() });
            let right_client = self.right_store.put::<KVStoreExclusivePutLinearizer>(a, new_right_balance.unwrap(), put_lin); 
            state.right_client = right_client;
        }

        let new_balance = sum_option(new_left_balance, new_right_balance).unwrap();
        assert(new_balance == unwrap_or_zero_spec(val_or_none(state.bank_owned@.val(), a)) - v);
        let tracked ar = lin.get().apply(withdraw_op(self.id(), a, v), (), state.bank_owned.borrow_mut(), &new_balance);
        assert(sum_option_spec(val_or_none(state.left_client@.val(), a), val_or_none(state.right_client@.val(), a), val_or_none(state.bank_owned@.val(), a)));
        assert forall |k| k != a implies sum_option_spec(val_or_none(state.left_client@.val(), k), val_or_none(state.right_client@.val(), k), val_or_none(state.bank_owned@.val(), k)) by {
            assert(val_or_none(state.left_client@.val(), k) == val_or_none(ghost_left_client@.val(), k));
            assert(val_or_none(state.bank_owned@.val(), k) == val_or_none(ghost_bank@.val(), k))
        }
        assert(lock_handle.rwlock().pred().inv(state));

        lock_handle.release_write(state);
        new_balance
    }

}
}