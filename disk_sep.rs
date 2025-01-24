mod disk;

use disk::vecdisk::*;
use disk::disk_wrap::*;
use disk::logatom::*;
use disk::seq_view::*;
use vstd::prelude::*;

verus! {
    struct PersistWriter {
        frac: SeqFrac<u8>,
    }

    impl MutLinearizer<WriteOp> for PersistWriter {
        type ApplyResult = SeqFrac<u8>;

        closed spec fn pre(self, op: WriteOp) -> bool {
            &&& self.frac.valid(op.persist_id)
            &&& self.frac.off() == op.addr
            &&& self.frac@.len() == op.data.len()
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut SeqAuth<u8>, e: &()) -> (tracked out: SeqFrac<u8>) {
            let tracked mut mself = self;
            mself.frac.agree(r);
            mself.frac.update(r, pstate);
            mself.frac
        }
    }

    fn main() {
        let d = Disk::new(1024);
        let (mut dw, Tracked(mut f0), Tracked(mut pf0)) = DiskWrap::new(d);

        let tracked mut f4 = f0.split(4);
        let tracked mut f8 = f4.split(4);

        let tracked mut pf4 = pf0.split(4);
        let tracked mut pf8 = pf4.split(4);

        assert(f0@ == seq![0u8, 0u8, 0u8, 0u8]);

        let Tracked(pf0) = dw.write::<PersistWriter>(0, &[120, 121, 122, 123], Tracked(&mut f0), Tracked(PersistWriter{ frac: pf0 }));
        let Tracked(pf4) = dw.write::<PersistWriter>(4, &[124, 125, 126, 127], Tracked(&mut f4), Tracked(PersistWriter{ frac: pf4 }));

        assert(f0@ == seq![120u8, 121u8, 122u8, 123u8]);

        let x = dw.read(0, 4, Tracked(&f0));
        assert(x@ == seq![120u8, 121u8, 122u8, 123u8]);
        let x = dw.read(4, 4, Tracked(&f4));
        assert(x@ == seq![124u8, 125u8, 126u8, 127u8]);
    }
}
