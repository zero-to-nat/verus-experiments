use vstd::prelude::*;

verus! {

    #[inline(never)]
    pub fn test1() {
    }

    #[inline(never)]
    pub fn test2(
        Ghost(i1): Ghost<u8>,
        Ghost(i2): Ghost<u8>,
        Ghost(i3): Ghost<u8>,
        Ghost(i4): Ghost<u8>) {
    }

    #[no_mangle]
    fn testfunc() {
        test1();

        let a0 = Ghost(0u8);
        let a1 = Ghost(1u8);
        let a2 = Ghost(1u8);
        let a3 = Ghost(1u8);

        test2(a0, a1, a2, a3);
    }

    fn main() {
        testfunc();
    }

} // verus!
