use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::hash_map::*;

use crate::frac::*;
use crate::disk::*;

verus!{

type DF = Frac<Seq<u8>>;

struct FracPair {
    cache_bot: DF,
    disk_top: DF,
}

struct Entry {
    phy: Vec<u8>,
    frac_pair: Tracked<FracPair>,
}

struct CacheState {
    present: HashMapWithView<usize, Entry>,
    absent: Tracked<Map<usize, FracPair>>, // disk tops for absent records
}

struct CachePred<'a> {
    disk: &'a Disk,
}

impl<'a> CachePred<'a> {
    closed spec fn inv_disjoint(self, v: CacheState) -> bool {
        forall |lba: usize| lba < self.disk.block_count()
            ==> (v.present@.contains_key(lba) ==> !v.absent@.contains_key(lba))
    }

    closed spec fn inv_union(self, v: CacheState) -> bool {
        forall |lba: usize| lba < self.disk.block_count()
            ==> v.present@.contains_key(lba) || v.absent@.contains_key(lba)
    }

    closed spec fn inv_disk_tops_valid(self, v: CacheState) -> bool {
        // TODO(nickolai): can we embed this invariant into the resources themselves
        // instead of a global inv about the map (or both maps)?
        forall |lba| v.absent@.contains_key(lba)
            ==> v.absent@[lba].disk_top.valid(self.disk.id(lba), 1)
    }
}

// TODO: try re-encoding the global invariant as
// a couple separation invariants (disjointness a la AllocatorPred::exclusive, and
// some resource the client holds that shows that the block must be in the cache
// somewhere).

impl<'a> RwLockPredicate<CacheState> for CachePred<'a> {
    closed spec fn inv(self, v: CacheState) -> bool {
        &&& self.inv_union(v)
        &&& self.inv_disjoint(v)
        &&& self.inv_disk_tops_valid(v)
    }
}

struct Cache<'a> {
    disk: Disk,
    rwlock: RwLock<CacheState, CachePred<'a>>,
}

proof fn tracked_split_map<K,U,V>(tracked mut inpair: Map<K, (U,V)>) -> (tracked out: (Map<K,U>, Map<K,V>))
requires inpair.dom().finite()
decreases inpair.dom().len()
{
    if inpair.is_empty()
    {
        (Map::tracked_empty(), Map::tracked_empty())
    } else {
        let k = choose |k| inpair.contains_key(k);

        let olddom = inpair.dom();
        let tracked (u,v) = inpair.tracked_remove(k);
//         assert( olddom.contains(k) );
//         assert( !inpair.dom().contains(k) );
//         assert( inpair.dom() == olddom.remove(k) );
//         assert( olddom.contains(k) );
//         assert( olddom.len() == olddom.remove(k).len() + 1int );
//         assert( inpair.dom().len() == olddom.len() - 1 );
        let tracked tpr = Tracked( tracked_split_map(inpair) );
        let tracked Tracked(pr) = tpr;
        let tracked (mut omu, mut omv) = pr;
        omu.tracked_insert(k, u);
        omv.tracked_insert(k, v);
        (omu, omv)
    }
}

proof fn tracked_zip<K,U,V>(tracked ku: &mut Map<K,U>, tracked kv: &mut Map<K,V>) -> (tracked out: Map<K,(U,V)>)
requires
    old(ku).dom().finite(),
    old(ku).dom() == old(kv).dom(),
ensures
    out.dom() == old(ku).dom(),
decreases old(ku).dom().len()
{
    if ku.is_empty()
    {
        let tracked out = Map::tracked_empty();
        assert( out.dom() == old(ku).dom() );   // extn equality
        out
    } else {
        let k = choose |k| ku.contains_key(k);
        let tracked u = ku.tracked_remove(k);
        let tracked v = kv.tracked_remove(k);
        let tracked mut out = tracked_zip(ku, kv);
        out.tracked_insert(k, (u, v));
//         assert( out.dom() == old(ku).dom() );
        out
    }
}

proof fn tracked_unzip<K,U,V>(tracked muv: &mut Map<K,(U,V)>) -> (tracked out: (Map<K,U>, Map<K,V>))
requires old(muv).dom().finite()
ensures
    out.0.dom() == old(muv).dom(),
    out.1.dom() == old(muv).dom(),
decreases old(muv).dom().len()
{
    if muv.is_empty()
    {
        let tracked out = (Map::tracked_empty(), Map::tracked_empty());
        assert( out.0.dom() == old(muv).dom() );
        assert( out.1.dom() == old(muv).dom() );
        out
    } else {
        let k = choose |k| muv.contains_key(k);
        let tracked (u,v) = muv.tracked_remove(k);
        let tracked (mut mu, mut mv) = tracked_unzip(muv);
        mu.tracked_insert(k, u);
        mv.tracked_insert(k, v);
        (mu, mv)
    }
}

trait TrackedApplyFn<U,V> : Sized {
    proof fn apply(&self, tracked u: U) -> (tracked v: V);
}

proof fn tracked_apply<K,U,V,A: TrackedApplyFn<U,V>>(tracked mu: &mut Map<K,U>, lambda: A) -> (tracked out: Map<K,V>)
requires old(mu).dom().finite()
ensures out.dom() == old(mu).dom()
decreases old(mu).dom().len()
{
    if mu.is_empty()
    {
        let tracked out = Map::tracked_empty();
        assert( out.dom() == old(mu).dom() );   // extn equality
        out
    } else {
        let k = choose |k| mu.contains_key(k);
        let tracked u = mu.tracked_remove(k);
        let tracked mut out = tracked_apply(mu, lambda);
        let tracked v = lambda.apply(u);
        out.tracked_insert(k, v);
        out
    }
}

proof fn make_cache_pairs(tracked disk_tops: &Map<usize, DF>, block_count: usize, out_count: usize) -> (tracked out: Map<usize, (DF, DF)>)
requires
    disk_tops.dom() == crate::disk::usize_set_range(block_count),
    out_count <= block_count,
ensures
    out.dom().finite(),
    out.dom() == crate::disk::usize_set_range(out_count),
decreases out_count
{
    if out_count == 0 {
        let tracked out = Map::tracked_empty();
        assert( out.dom() == crate::disk::usize_set_range(out_count) );
        out
    }
    else {
        let i = (out_count - 1) as usize;
        let tracked mut sub = make_cache_pairs(disk_tops, block_count, i);
        let tracked mut cache_bot = Frac::new(disk_tops[i]@);
        let tracked cache_top = cache_bot.split(1);
        sub.tracked_insert(i, (cache_bot, cache_top));
        assert( sub.dom() == crate::disk::usize_set_range(i).insert(i) );
        assert( sub.dom() == crate::disk::usize_set_range(out_count) );
        sub
    }
}

struct Reassociate<T> {
     t: core::marker::PhantomData<T>,
}

impl<T> Reassociate<T> {
    #[verifier::external_body]
    pub proof fn new() -> tracked Self {
         Self{t: core::marker::PhantomData::default()}
    }
}

impl<T> TrackedApplyFn<(T,(T,T)), ((T,T),T)> for Reassociate<T> {
    proof fn apply(&self, tracked t: (T,(T,T))) -> (tracked v: ((T,T),T))
    {
        let tracked (u,(v,w)) = t;
        ((u,v),w)
    }
}

struct Fracpairize { }

impl TrackedApplyFn<(DF,DF), FracPair> for Fracpairize {
    proof fn apply(&self, tracked t: (DF,DF)) -> (tracked v: FracPair)
    {
        let tracked (disk_top, cache_bot) = t;
        FracPair{cache_bot, disk_top}
    }
}

impl<'a> Cache<'a> {
    pub closed spec fn inv(self) -> bool
    {
        &&& self.disk == self.rwlock.pred().disk
    }

    pub exec fn new(&self, block_count: usize) -> (out: (Self, Tracked<Map<usize, DF>>))
    ensures
        out.0.inv(),
    {
        let (disk, Tracked(disk_tops)) = Disk::new(block_count);

        assert( forall |lba| disk_tops.contains_key(lba)
            ==> disk_tops[lba].valid(disk.id(lba), 1) );

        let tracked cache_pairs = make_cache_pairs(&disk_tops, block_count, block_count);

        assert( forall |lba| cache_pairs.contains_key(lba)
            ==> cache_pairs[lba].0.valid(disk.id(lba), 1) );

        assert( disk_tops.dom() == cache_pairs.dom() );
        let tracked z1 = tracked_zip(&mut disk_tops, &mut cache_pairs);
        let tracked reassociate = Reassociate::new();
        assert( z1.dom().finite() );
        let tracked z2 = tracked_apply::<usize, (DF, (DF, DF)), ((DF, DF), DF), Reassociate<DF>>(&mut z1, reassociate);
        let tracked (paired_absent, cache_tops) = tracked_unzip(&mut z2);
        let tracked absent = tracked_apply(&mut paired_absent, Fracpairize{});

        assume( vstd::std_specs::hash::obeys_key_model::<usize>() );
        let state = CacheState{
            present: HashMapWithView::new(),
            absent: Tracked(absent),
        };
        let ghost pred = CachePred{disk: &disk};
        proof { set_range_properties(block_count as int) }; // too bad we don't have spec ensures
//         assert( state.absent@.dom() == crate::disk::usize_set_range(block_count) );
//         assert forall |lba: usize| lba < pred.block_count implies state.absent@.contains_key(lba) by {
//         }
        assert( pred.inv_disk_tops_valid(state) );
        (Self{
            disk: disk,
            rwlock: RwLock::new(state, Ghost(pred)),
        },
        Tracked(cache_tops))
    }

    pub exec fn read(&self, lba: usize, block_top: &mut Tracked<DF>) -> (out: Vec<u8>)
    ensures out@ == block_top@@
    {
        loop
        {
            match self.try_memory_read(lba, block_top) {
                Some(value) => return value,
                None => self.fault_in(lba),
            }
        }
    }

    exec fn try_memory_read(&self, lba: usize, block_top: &mut Tracked<DF>) -> (out: Option<Vec<u8>>)
    {
        let out: Option<Vec<u8>>;
        let read_handle = self.rwlock.acquire_read();
        let entries = &read_handle.borrow().present;
        let out = match entries.get(&lba) {
            Some(entry) => Some(entry.phy.clone()),
            None => None,
        };
        read_handle.release_read();
        out
    }

    exec fn fault_in(&self, lba: usize)
    requires
        self.inv(),
        lba < self.disk.block_count(),  // TODO: use a resource instead of a classical property
    {
        let (mut cache_state, write_handle) = self.rwlock.acquire_write();
        // during this time nobody can read or write ANYTHING in the cache,
        // so we know there aren't concurrent writers.
        if !cache_state.present.contains_key(&lba) {
            proof { set_range_properties(self.disk.block_count() as int) }; // too bad we don't have spec ensures
            assert( !cache_state.present@.contains_key(lba) );
            assert( self.rwlock.pred().inv(cache_state) );
            assert( lba < self.disk.block_count() );
//             p ==> q ~ !q ==> !p
            assert( cache_state.present@.contains_key(lba) ==> !cache_state.absent@.contains_key(lba) );
            assert( cache_state.absent@.contains_key(lba) ==> !cache_state.present@.contains_key(lba) );
            assert( self.rwlock.pred().inv_union(cache_state) );
            assert( lba < self.disk.block_count() );
            assert( lba < self.rwlock.pred().disk.block_count() );
            assert( cache_state.present@.contains_key(lba) || cache_state.absent@.contains_key(lba) );
            assert( cache_state.absent@.contains_key(lba) );
            let frac_pair = Tracked(
                cache_state.absent.borrow_mut().tracked_remove(lba)
            );
            let value = self.disk.read(lba, Tracked( &frac_pair.borrow().disk_top) );
            cache_state.present.insert(lba, Entry {
                phy: value,
                frac_pair,
            });
        }
        write_handle.release_write(cache_state);
    }
}

}//verus!
