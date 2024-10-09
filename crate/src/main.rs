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
        Tracked(i1): Tracked<u8>,
        Tracked(i2): Tracked<u8>,
        Tracked(i3): Tracked<u8>,
        Tracked(i4): Tracked<u8>) -> u8 {
            x
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

        let y = test4(123u8, Tracked(0u8), Tracked(0u8), Tracked(0u8), Tracked(0u8));
        println!("{y}");

        // println!("{p1} {p2} {x}");
    }

} // verus!
