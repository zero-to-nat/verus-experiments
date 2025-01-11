use vstd::prelude::*;
use super::disk::Disk;
use super::map_view::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<MapAuth<u64, u8>>,
    }

    type DiskView = MapFrac<u64, u8>;

    impl DiskWrap {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.d@ =~= self.a@@
            &&& self.a@.inv()
        }

        pub closed spec fn id(self) -> int
        {
            self.a@.id()
        }

        pub fn read(&self, a: u64, Tracked(perm): Tracked<&DiskView>) -> (result: u8)
            requires
                self.inv(),
                perm.valid(self.id()),
                perm@.contains_key(a),
            ensures
                result == perm@[a]
        {
            proof {
                perm.agree(self.a.borrow());
            }
            self.d.read(a)
        }

        pub fn write(&mut self, a: u64, v: u8, Tracked(perm): Tracked<&mut DiskView>)
            requires
                old(self).inv(),
                old(perm).valid(old(self).id()),
                old(perm)@.contains_key(a),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                perm.valid(self.id()),
                perm@ =~= old(perm)@.insert(a, v),
        {
            proof {
                perm.agree(self.a.borrow());
            }
            self.d.write(a, v);
            proof {
                perm.update(self.a.borrow_mut(), map![a => v]);
            }
        }
    }
}
