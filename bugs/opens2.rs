use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    struct P {}
    impl InvariantPredicate<(), ()> for P {
        closed spec fn inv(k: (), v: ()) -> bool { true }
    }

    struct S {
        inv: AtomicInvariant<(), (), P>,
    }

    impl S {
        spec fn namespace() -> int { 5 }
        fn f(&self) opens_invariants [ Self::namespace() ] {
            assume(self.inv.namespace() == 5);
            open_atomic_invariant!(&self.inv => inner => {});
        }
    }
}
