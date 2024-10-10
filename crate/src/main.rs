use vstd::prelude::*;
use vstd::invariant::*;

verus! {

    pub struct InvParam {}
    #[allow(dead_code)]
    pub struct InvState { x: u64 }
    pub struct InvPred {}

    impl InvariantPredicate<InvParam, InvState> for InvPred {
        closed spec fn inv(k: InvParam, v: InvState) -> bool {
            v.x == 5 || v.x == 10
        }
    }

    #[inline(never)]
    pub fn test1(Tracked(i): Tracked<&AtomicInvariant<InvParam, InvState, InvPred>>, Tracked(cr): Tracked<OpenInvariantCredit>) {
        proof {
            open_atomic_invariant!(cr => i => inner => {
                inner.x = 10u64
            });
        };
    }

    #[inline(never)]
    pub fn test2(Tracked(i): Tracked<&AtomicInvariant<InvParam, InvState, InvPred>>) {
    }

    #[inline(never)]
    pub fn test3() {
    }

    #[inline(never)]
    pub fn test4(
        x: u8,
        Ghost(i1): Ghost<u8>,
        Ghost(i2): Ghost<u8>,
        Ghost(i3): Ghost<u8>,
        Ghost(i4): Ghost<u8>) -> u8 {
            x
    }

    #[inline(never)]
    pub fn erasure_test(Ghost(x): Ghost<int>) -> Ghost<int> {
        let Ghost(mut g) = Ghost(x);
        for _i in 0..1000000 {
            let Ghost(n) = Ghost(g + 1);
            proof {
                g = n;
            };
        };
        Ghost(g)
    }

    #[allow(unused_variables)]
    fn main() {
        let inv_param = InvParam{};
        let inv_st = InvState{ x: 5 };
        let tracked i = AtomicInvariant::<_, _, InvPred>::new(inv_param, inv_st, 123int);

        let Tracked(cr) = create_open_invariant_credit();
        test1(Tracked(&i), Tracked(cr));

        test2(Tracked(&i));

        test3();

        let ghost ga0 = 0u8;
        let a0 = Ghost(ga0);
        let a1 = Ghost(1u8);

        let Ghost(x) = erasure_test(Ghost(0int));

        let y = test4(123u8, a0, a0, a0, a1);
        println!("{y}");

        // println!("{p1} {p2} {x}");
    }

} // verus!
