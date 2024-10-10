use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    struct InvState {}
    struct InvParam {}
    struct InvPred {}

    impl InvariantPredicate<InvParam, InvState> for InvPred {
        closed spec fn inv(k: InvParam, v: InvState) -> bool { true }
    }

    trait T {
        spec fn namespace() -> int;
        fn f(&self) opens_invariants [ Self::namespace() ];
    }

    struct S {
        inv: AtomicInvariant<InvParam, InvState, InvPred>,
    }

    impl T for S {
        spec fn namespace() -> int { 5 }
        fn f(&self) {
            open_atomic_invariant!(&self.inv => inner => {});
        }
    }
}
