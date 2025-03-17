use builtin::*;
use vstd::prelude::*;
use vstd::rwlock::*;
use crate::logatom::*;
use crate::kvstore::*;
use crate::bank::*;

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

    proof fn peek(tracked &self, op: KVStoreGetOperation<u32, u32>, tracked inst: <KVStoreGetOperation<u32, u32> as ReadOperation>::Instance, tracked r: &<KVStoreGetOperation<u32, u32> as ReadOperation>::Resource) {}
}

struct KVStoreExclusivePutLinearizer {
    pub client: KVStoreSM::client<u32, u32>,
}

impl MutLinearizer<KVStorePutOperation<u32, u32>> for KVStoreExclusivePutLinearizer {
    type ApplyResult = KVStoreSM::client<u32, u32>;

    open spec fn pre(self, op: KVStorePutOperation<u32, u32>) -> bool {
        self.client.instance_id() == op.id
    }

    open spec fn post(self, op: KVStorePutOperation<u32, u32>, r: <KVStorePutOperation<u32, u32> as MutOperation>::ExecResult, ar: Self::ApplyResult) -> bool {
        &&& ar.instance_id() == op.id
        &&& ar.value() == self.client.value().insert(op.k, op.v)
    }

    proof fn apply(tracked self, 
        op: KVStorePutOperation<u32, u32>, 
        hint: <KVStorePutOperation<u32, u32> as MutOperation>::ApplyHint, 
        tracked inst: <KVStorePutOperation<u32, u32> as MutOperation>::Instance,
        tracked r: &mut <KVStorePutOperation<u32, u32> as MutOperation>::Resource, 
        e: &<KVStorePutOperation<u32, u32> as MutOperation>::ExecResult,) 
    -> (tracked out: Self::ApplyResult) 
    {
        let tracked cl = inst.borrow().put(op.k, op.v, r, self.client);
        cl
    }

    proof fn peek(tracked &self, op: KVStorePutOperation<u32, u32>, tracked inst: <KVStorePutOperation<u32, u32> as MutOperation>::Instance, tracked r: &<KVStorePutOperation<u32, u32> as MutOperation>::Resource) {}
}


struct ShardedBankLockedState {
    left_client: Tracked<KVStoreSM::client<u32, u32>>,
    right_client: Tracked<KVStoreSM::client<u32, u32>>,
    bank_inst: Tracked<BankSM::Instance>,
    bank_owned: Tracked<BankSM::inner>,
}

struct ShardedBankPred {
    left_id: InstanceId,
    right_id: InstanceId,
    bank_id: InstanceId
}

impl RwLockPredicate<ShardedBankLockedState> for ShardedBankPred {
    closed spec fn inv(self, v: ShardedBankLockedState) -> bool {
        &&& v.left_client@.instance_id() == self.left_id
        &&& v.right_client@.instance_id() == self.right_id
        &&& v.bank_owned@.instance_id() == self.bank_id
        &&& v.bank_inst@.id() == self.bank_id
        &&& forall |k: u32| #![trigger v.bank_owned@.value().contains_key(k)] {
            sum_option_spec(val_or_none(v.left_client@.value(), k), val_or_none(v.right_client@.value(), k), val_or_none(v.bank_owned@.value(), k))
        }
    }
}

struct ShardedBank<Store: KVStore<u32, u32>>  {
    pub locked_state: RwLock<ShardedBankLockedState, ShardedBankPred>,
    pub left_store: Store,
    pub right_store: Store
}

impl<Store: KVStore<u32, u32>> Bank for ShardedBank<Store> {
    closed spec fn id(&self) -> InstanceId {
        self.locked_state.pred().bank_id
    }

    closed spec fn inv_namespace(self) -> int {
        1
    }

    closed spec fn inv(&self) -> bool {
        &&& self.left_store.inv()
        &&& self.right_store.inv()
        &&& self.left_store.id() == self.locked_state.pred().left_id
        &&& self.right_store.id() == self.locked_state.pred().right_id
    }

    open spec fn new_pre() -> bool {
        Store::new_pre()
    }

    fn new() 
        -> (out: (Self, Tracked<BankSM::client>))
    {
        let (left_store, left_client) = Store::new();
        let (right_store, right_client) = Store::new();
        let tracked (
            Tracked(inst),
            Tracked(inner),
            Tracked(client_opt)
        ) = BankSM::Instance::initialize();
        let tracked client = client_opt.tracked_unwrap();

        let state = ShardedBankLockedState { left_client, right_client, bank_inst: Tracked(inst), bank_owned: Tracked(inner) };

        let ghost pred = ShardedBankPred { left_id: left_client@.instance_id(), right_id: right_client@.instance_id(), bank_id: inner.instance_id() };
        let locked_state = RwLock::new(state, Ghost(pred));

        (ShardedBank{locked_state, left_store, right_store}, Tracked(client))
    }

    fn deposit<Lin: MutLinearizer<BankDepositOperation>>(&self, a: u32, v: u32, Tracked(lin): Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        proof { lin.peek(deposit_op(self.id(), a, v), state.bank_inst, state.bank_owned.borrow()) };

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
        let tracked ar = lin.apply(deposit_op(self.id(), a, v), (), state.bank_inst, state.bank_owned.borrow_mut(), &());

        lock_handle.release_write(state);
        (Tracked(ar))
    }

    fn withdraw<Lin: MutLinearizer<BankWithdrawOperation>>(&self, a: u32, v: u32, Tracked(lin): Tracked<Lin>) 
        -> (out: Tracked<Lin::ApplyResult>)
    {
        let (mut state, lock_handle) = self.locked_state.acquire_write();

        proof { lin.peek(withdraw_op(self.id(), a, v), state.bank_inst, state.bank_owned.borrow()) };

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
        let tracked ar = lin.apply(withdraw_op(self.id(), a, v), (), state.bank_inst, state.bank_owned.borrow_mut(), &());

        lock_handle.release_write(state);
        Tracked(ar)
    }
}

}