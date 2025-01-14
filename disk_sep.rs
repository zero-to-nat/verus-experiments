mod disksep;

use disksep::disk::*;
use disksep::disk_view::*;
use vstd::prelude::*;

verus! {
    fn main() {
        let d = Disk::new(1024);
        let (dw, Tracked(mut f)) = DiskWrap::new(d);

        assert(f@[0] == d@[0]);

        let tracked mut f0 = f.split(set![0, 1, 2, 3]);
        let tracked mut f4 = f.split(set![4, 5, 6, 7]);

        let a0 = DiskAddr::new(0, Ghost(4), Tracked(f0));
        let a4 = DiskAddr::new(4, Ghost(4), Tracked(f4));

        assert(a0@[0] == 0);
    }
}
