use vstd::prelude::*;
use super::disk::Disk;
use super::map_view::*;

verus! {
    pub struct DiskWrap {
        d: Disk,
        a: Tracked<MapAuth<usize, u8>>,
    }

    type DiskView = MapFrac<usize, u8>;

    impl DiskWrap {
        spec fn disk_matches_view(self, a: usize) -> bool
        {
            &&& self.a@@.contains_key(a) ==> a < self.d@.len()
            &&& self.a@@.contains_key(a) ==> self.d@[a as int] == self.a@@[a]
        }

        pub closed spec fn inv(self) -> bool
        {
            &&& self.a@.inv()
            &&& forall |a: usize| self.disk_matches_view(a)
        }

        pub closed spec fn id(self) -> int
        {
            self.a@.id()
        }

        pub fn read(&self, a: usize, Tracked(perm): Tracked<&DiskView>) -> (result: u8)
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
            assert(self.disk_matches_view(a));
            self.d.read(a)
        }

        pub fn write(&mut self, a: usize, v: u8, Tracked(perm): Tracked<&mut DiskView>)
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
            assert(self.disk_matches_view(a));
            self.d.write(a, v);
            proof {
                perm.update(self.a.borrow_mut(), map![a => v]);
            }
            assert forall |x: usize| self.disk_matches_view(x) by {
                assert(old(self).disk_matches_view(x));
            }
        }
    }
}
