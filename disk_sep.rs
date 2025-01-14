mod disksep;

use disksep::disk::*;
use disksep::disk_view::*;
use vstd::prelude::*;

verus! {
    fn main() {
        let d = Disk::new(1024);
        let (mut dw, Tracked(mut f)) = DiskWrap::new(d);

        assert(f@[0] == d@[0]);

        let tracked mut f0 = f.split(set![0, 1, 2, 3]);
        let tracked mut f4 = f.split(set![4, 5, 6, 7]);

        assert(f0@[0] == 0);

        dw.write_one(0, 120, Tracked(&mut f0));
        dw.write_one(4, 124, Tracked(&mut f4));
        dw.write_one(5, 125, Tracked(&mut f4));
        dw.write_one(6, 126, Tracked(&mut f4));
        dw.write_one(7, 127, Tracked(&mut f4));
        dw.write_one(1, 121, Tracked(&mut f0));
        dw.write_one(2, 122, Tracked(&mut f0));
        dw.write_one(3, 123, Tracked(&mut f0));
        let x = dw.read_one(0, Tracked(&f0));
        assert(x == 120);
        let x = dw.read_one(4, Tracked(&f4));
        assert(x == 124);

        let x = dw.read(0, 4, Tracked(&f0));
        assert(x@ == seq![120u8, 121u8, 122u8, 123u8]);

        let x = dw.read(4, 4, Tracked(&f4));
        assert(x@ == seq![124u8, 125u8, 126u8, 127u8]);

        let mut a0 = DiskAddr::new(0, Ghost(4), Tracked(f0));
        let mut a4 = DiskAddr::new(4, Ghost(4), Tracked(f4));

        assert(a0@ == seq![120u8, 121u8, 122u8, 123u8]);
        assert(a4@ == seq![124u8, 125u8, 126u8, 127u8]);

        let x = dw.read_wrapped(&a0, 4);
        assert(x@ == a0@);

        let x = dw.read_wrapped(&a4, 4);
        assert(x@ == a4@);

        dw.write_wrapped(&mut a0, &[10, 11, 12, 13]);
        dw.write_wrapped(&mut a4, &[14, 15, 16, 17]);

        assert(a0@ == seq![10u8, 11u8, 12u8, 13u8]);
        assert(a4@ == seq![14u8, 15u8, 16u8, 17u8]);

        let x = dw.read_wrapped(&a0, 4);
        assert(x@ == a0@);
    }
}
