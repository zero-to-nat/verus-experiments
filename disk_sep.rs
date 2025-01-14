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

        let a0 = DiskAddr::new(0, Ghost(4), Tracked(f0));
        let a4 = DiskAddr::new(4, Ghost(4), Tracked(f4));

        assert(a0@ == seq![120u8, 121u8, 122u8, 123u8]);
        assert(a4@ == seq![124u8, 125u8, 126u8, 127u8]);
    }
}
