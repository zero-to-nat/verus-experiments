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

struct CachePred {
}

impl RwLockPredicate<CacheState> for CachePred {
    closed spec fn inv(self, v: CacheState) -> bool {
        &&& true
    }
}

struct Cache {
    disk: Disk,
    rwlock: RwLock<CacheState, CachePred>,
}

proof fn tracked_split_map<K,U,V>(tracked inpair: Map<K, (U,V)>) -> (tracked out: (Map<K,U>, Map<K,V>))
{
    if inpair.is_empty()
    {
        (Map::tracked_empty(), Map::tracked_empty())
    } else {
        let k = choose |k| inpair.contains_key(k);
        let tracked (u,v) = inpair.tracked_remove(k);
        let tracked tpr = Tracked( tracked_split_map(inpair) );
        let tracked Tracked(pr) = tpr;
        let tracked (omu, omv) = pr;
        omu.tracked_insert(k, u);
        omv.tracked_insert(k, v);
        (omu, omv)
    }
}

proof fn tracked_zip<K,U,V>(tracked ku: &mut Map<K,U>, tracked kv: &mut Map<K,V>) -> (tracked out: Map<K,(U,V)>)
{
    if ku.is_empty()
    {
        Map::tracked_empty()
    } else {
        let k = choose |k| ku.contains_key(k);
        let tracked u = ku.tracked_remove(k);
        let tracked v = kv.tracked_remove(k);
        let tracked out = tracked_zip(ku, kv);
        out.tracked_insert(k, (u, v));
        out
    }
}

proof fn tracked_unzip<K,U,V>(tracked muv: &mut Map<K,(U,V)>) -> (tracked out: (Map<K,U>, Map<K,V>))
{
    if muv.is_empty()
    {
        (Map::tracked_empty(), Map::tracked_empty())
    } else {
        let k = choose |k| muv.contains_key(k);
        let tracked (u,v) = muv.tracked_remove(k);
        let tracked (mu, mv) = tracked_unzip(muv);
        mu.tracked_insert(k, u);
        mv.tracked_insert(k, v);
        (mu, mv)
    }
}

proof fn tracked_apply<K,U,V>(tracked mu: &mut Map<K,U>, lambda: impl Fn(Tracked<U>) -> Tracked<V>) -> (tracked out: Map<K,V>)
{
    if mu.is_empty()
    {
        Map::tracked_empty()
    } else {
        let k = choose |k| mu.contains_key(k);
        let tracked u = mu.tracked_remove(k);
        let tracked out = tracked_apply(mu, lambda);
        let tracked Tracked(v) = lambda(Tracked(u));
        out.tracked_insert(k, v);
        out
    }
}

proof fn make_cache_pairs(tracked disk_tops: &Map<usize, DF>, block_count: usize) -> (tracked out: Map<usize, (DF, DF)>)
{
    if block_count == 0 { Map::tracked_empty() }
    else {
        let i = (block_count - 1) as usize;
        let tracked sub = make_cache_pairs(disk_tops, i);
        let tracked mut cache_bot = Frac::new(disk_tops[i]@);
        let tracked cache_top = cache_bot.split(1);
        sub.tracked_insert(i, (cache_bot, cache_top));
        sub
    }
}

impl Cache {
    pub exec fn new(&self, block_count: usize) -> (out: (Self, Tracked<Map<usize, DF>>))
    {
        let (disk, Tracked(disk_tops)) = Disk::new(block_count);
        let cache_pairs = make_cache_pairs(&disk_tops, block_count);
        let z1 = tracked_zip(&mut disk_tops, &mut cache_pairs);
        let z2 = tracked_apply::<usize, (DF, (DF, DF)), ((DF, DF), DF)>(&mut z1,
            |x: Tracked<(DF, (DF, DF))>|
                Tracked({
                    let Tracked(x) = x;
                    let (u,(v,w)) = x;
                    ((u,v),w)
                })
        );
        let tracked (paired_absent, cache_tops) = tracked_unzip(&mut z2);
        let absent = tracked_apply(&mut paired_absent,
            |x|
            Tracked({
                let Tracked(x) = x;
                let tracked (disk_top, cache_bot) = x;
                FracPair{cache_bot, disk_top}
            })
        );

        assume( vstd::std_specs::hash::obeys_key_model::<usize>() );
        let state = CacheState{
            present: HashMapWithView::new(),
            absent: Tracked(absent),
        };
        let ghost pred = CachePred{};
        (Self{
            disk,
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
        let entries = read_handle.borrow().present;
        let out = match entries.get(&lba) {
            Some(entry) => Some(entry.phy.clone()),
            None => None,
        };
        read_handle.release_read();
        out
    }

    exec fn fault_in(&self, lba: usize)
    {
        let (cache_state, write_handle) = self.rwlock.acquire_write();
        // during this time nobody can read or write ANYTHING in the cache,
        // so we know there aren't concurrent writers.
        if !cache_state.present.contains_key(&lba) {
            let frac_pair = Tracked(
                cache_state.absent.borrow_mut().tracked_remove(lba)
            );
            let value = self.disk.read(lba, &Tracked( frac_pair.borrow().disk_top) );
            cache_state.present.insert(lba, Entry {
                phy: value,
                frac_pair,
            });
        }
        write_handle.release_write(cache_state);
    }
}

}//verus!
