mod disk;

use disk::vecdisk::*;
use disk::disk_wrap::*;
use vstd::prelude::*;

verus! {
    fn main() {
        let d = Disk::new(1024);
        let (mut dw, Tracked(mut f0), Tracked(mut pf0)) = DiskWrap::new(d);

        let tracked mut f4 = f0.split(4);
        let tracked mut f8 = f4.split(4);

        let tracked mut pf4 = pf0.split(4);
        let tracked mut pf8 = pf4.split(4);

        assert(f0@ == seq![0u8, 0u8, 0u8, 0u8]);

        dw.write(0, &[120, 121, 122, 123], Tracked(&mut f0), Tracked(&mut pf0));
        dw.write(4, &[124, 125, 126, 127], Tracked(&mut f4), Tracked(&mut pf4));

        assert(f0@ == seq![120u8, 121u8, 122u8, 123u8]);

        let x = dw.read(0, 4, Tracked(&f0));
        assert(x@ == seq![120u8, 121u8, 122u8, 123u8]);
        let x = dw.read(4, 4, Tracked(&f4));
        assert(x@ == seq![124u8, 125u8, 126u8, 127u8]);
    }
}
