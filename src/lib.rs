//! A barrier which allows low-latency benchmarking of tasks.
//!
//! A [`RearmBarrier`] lets a single producer thread build a job, broadcast it
//! to a fixed set of `WORKERS` consumer threads behind a shared reference,
//! wait for every consumer to finish, observe their per-worker results and
//! then re-arm for the next job. All waiting is done by spinning, so there
//! is no OS involvement on the hot path.
//!
//! Completion is detected with a tree of counters ("tickets") of fan-in
//! `CLUSTER`, so that the cache line traffic on completion is spread across
//! many lines instead of all workers hammering one shared counter.
//!
//! The crate is `no_std` and performs no allocation.
//!
//! ```
//! use rearm_barrier::RearmBarrier;
//!
//! const WORKERS: usize = 4;
//! let barrier = RearmBarrier::<u64, u64, WORKERS, 2>::new();
//!
//! std::thread::scope(|s| {
//!     for id in 0..WORKERS {
//!         let barrier = &barrier;
//!         s.spawn(move || {
//!             barrier.consumer(100, id, 0, |_version, job, result| {
//!                 *result = job * id as u64;
//!             });
//!         });
//!     }
//!
//!     barrier.producer(100, |version| version as u64 + 1, |version, results| {
//!         for (id, r) in results.iter().enumerate() {
//!             assert_eq!(**r, (version as u64 + 1) * id as u64);
//!         }
//!     });
//! });
//! ```

#![no_std]
#![deny(missing_docs)]

#[cfg(not(target_pointer_width = "64"))]
compile_error!("Jesus Christ get bigger pointers dude, what is this 2003?");

use core::cell::UnsafeCell;
use core::mem::MaybeUninit;
use core::sync::atomic::{fence, AtomicBool, AtomicUsize, Ordering};

#[cfg(feature = "trace")]
pub mod trace;
#[cfg(not(feature = "trace"))]
mod trace;

/// A value which is forced to align to a cache line
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(C, align(64))]
pub struct CacheLine<T>(pub T);

impl<T> core::ops::Deref for CacheLine<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> core::ops::DerefMut for CacheLine<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// const C: usize = cluster size for the tree
// [tickets; (WORKERS + (C - 1)) / C]
//
// assume workers = 5
// assume C = 2
//
// +-------+ +-------+ +-------+ +-------+ +-------+ L = 0 (level)
// | core0 | | core1 | | core2 | | core3 | | core4 |
// +-------+ +-------+ +-------+ +-------+ +-------+
//     \         /         \         /         |
//       \     /             \     /           |
//         \ /                 \ /             |
//     +---------+         +---------+    +---------+
//     | ticket3 |         | ticket4 |    | ticket5 |
//     +---------+         +---------+    +---------+
//          \                   /              |
//            \               /                |
//              \           /                  |
//                \       /                    |
//                  \   /                      |
//               +---------+              +---------+
//               | ticket1 |              | ticket2 |
//               +---------+              +---------+
//                    \                        /
//                      \                    /
//                        \                /
//                          +---------+
//                          | ticket0 |
//                          +---------+
//
// Tickets are laid out as a heap: the children of node `i` are
// `i * C + 1 ..= i * C + C`, and the lowest level starts at index
// `ticket_tree_alloc(base_size, C)`.

/// Calculate the allocation size for the full tree of base `cluster`,
/// which has at least `base_size` at the next level.
const fn ticket_tree_alloc(base_size: usize, cluster: usize) -> usize {
    let mut size = 1;
    let mut bot_size = 1;
    while bot_size * cluster < base_size {
        bot_size *= cluster;
        size += bot_size;
    }
    size
}

/// Calculate the total number of tickets in the tree
pub const fn ticket_storage(workers: usize, cluster: usize) -> usize {
    let base_tickets = workers.div_ceil(cluster);
    ticket_tree_alloc(base_tickets, cluster) + base_tickets
}

/// Number of cache lines backing each worker in the ticket array.
///
/// `ticket_storage(workers, cluster) <= TICKETS_PER_WORKER * workers` holds
/// for every `workers >= 1` and `cluster >= 2`: the lowest level has
/// `ceil(workers / cluster)` nodes and every level above is at most as wide
/// as the level below it divided by `cluster`, so the whole tree is at most
/// `cluster / (cluster - 1) <= 2` times the size of the lowest level. This
/// lets the array be sized on stable Rust without `generic_const_exprs`, and
/// it is checked at compile time for each instantiation in [`RearmBarrier::new`].
const TICKETS_PER_WORKER: usize = 2;

/// A barrier which allows a producer to create a value, wait for consumers
/// to all process it, and then re-arm such that a new value can be created
/// and the cycle can repeat
///
/// `T` is the generic that is used for "jobs" that are given to workers. These
/// jobs are created once, broadcast to all threads behind a shared reference
/// and then re-armed for the next event!
///
/// `R` is the result that is given to workers via a `&mut R`, this value then
/// becomes visible to the producer behind a `&mut [CacheLine<R>; WORKERS]` to
/// observe the results of the workers
///
/// `WORKERS` is the number of workers that will be scheduled by the barrier
///
/// `CLUSTER` is the fan-in of the completion tree: how many workers (or
/// sub-trees) share one completion counter. Must be at least 2.
pub struct RearmBarrier<T, R, const WORKERS: usize, const CLUSTER: usize> {
    /// Completion counters, laid out as a flat heap (see the module diagram).
    /// Only the first `ticket_storage(WORKERS, CLUSTER)` entries are used.
    tickets: [[CacheLine<AtomicUsize>; TICKETS_PER_WORKER]; WORKERS],

    /// Holds the current ticket ID that indicates the state of the barrier.
    /// `2 * v + 1` means job `v` is published, `2 * v + 2` means every
    /// worker has finished job `v`.
    ticket_probe: CacheLine<AtomicUsize>,

    /// The user-controlled barrier value
    val: CacheLine<MaybeUninit<UnsafeCell<T>>>,

    /// The returned values from workers
    state: [MaybeUninit<CacheLine<UnsafeCell<R>>>; WORKERS],

    /// Set by producers to ensure exclusive producer access
    producer_lock: AtomicBool,

    /// Allows one-time allocation of unique consumer IDs
    consumer_lock: [AtomicBool; WORKERS],
}

// SAFETY: moving the barrier to another thread moves the `T` and the `R`s it
// owns, hence the `Send` bounds.
unsafe impl<T: Send, R: Send, const WORKERS: usize, const CLUSTER: usize> Send
    for RearmBarrier<T, R, WORKERS, CLUSTER>
{
}

// SAFETY: with a shared barrier, the producer thread writes the `T` and the
// consumer threads concurrently read it through `&T` (so `T: Send + Sync`).
// Each `R` is accessed by exactly one consumer thread and, once every consumer
// has finished, by the producer thread; the handover is synchronized by the
// tickets (so `R: Send`). `producer` and `consumer` verify on entry that at
// most one producer and one consumer per ID exist.
unsafe impl<T: Send + Sync, R: Send, const WORKERS: usize, const CLUSTER: usize> Sync
    for RearmBarrier<T, R, WORKERS, CLUSTER>
{
}

impl<T, R, const WORKERS: usize, const CLUSTER: usize> Default
    for RearmBarrier<T, R, WORKERS, CLUSTER>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T, R, const WORKERS: usize, const CLUSTER: usize> RearmBarrier<T, R, WORKERS, CLUSTER> {
    /// The number of tickets at the lowest level of the tree
    const BASE_SIZE: usize = WORKERS.div_ceil(CLUSTER);

    /// The size of the tree above the lowest level
    const TICKET_TREE_SIZE: usize = ticket_tree_alloc(Self::BASE_SIZE, CLUSTER);

    /// Compile-time validation of the const generic configuration
    const VALID_CONFIG: () = {
        assert!(WORKERS >= 1, "RearmBarrier needs at least one worker");
        assert!(CLUSTER >= 2, "Cluster should be >= 2 as a sane configuration");
        assert!(
            ticket_storage(WORKERS, CLUSTER) <= TICKETS_PER_WORKER * WORKERS,
            "ticket tree does not fit in its backing storage"
        );
    };

    /// Create a new barrier that is uninitialized (no producer has produced
    /// a value yet)
    ///
    /// This is a `const fn`, so a barrier can live in a `static`.
    pub const fn new() -> Self {
        let () = Self::VALID_CONFIG;

        Self {
            tickets: [const { [const { CacheLine(AtomicUsize::new(0)) }; TICKETS_PER_WORKER] }; WORKERS],
            ticket_probe: CacheLine(AtomicUsize::new(0)),
            state: [const { MaybeUninit::uninit() }; WORKERS],
            val: CacheLine(MaybeUninit::uninit()),
            producer_lock: AtomicBool::new(false),
            consumer_lock: [const { AtomicBool::new(false) }; WORKERS],
        }
    }

    /// The flat ticket array, so the heap indexing in the module diagram
    /// applies directly
    #[inline]
    fn tickets(&self) -> &[CacheLine<AtomicUsize>] {
        self.tickets.as_flattened()
    }

    /// Pointer to the job slot
    #[inline]
    fn val_ptr(&self) -> *mut T {
        UnsafeCell::raw_get(self.val.as_ptr())
    }

    /// Pointer to the result slot of `consumer_id`
    #[inline]
    fn state_ptr(&self, consumer_id: usize) -> *mut R {
        UnsafeCell::raw_get(self.state[consumer_id].as_ptr().cast::<UnsafeCell<R>>())
    }

    /// Produce `count` jobs. For each version, `func` builds the job, which is
    /// broadcast to every consumer; once every consumer has processed it,
    /// `complete` is invoked with the results of all workers, and the barrier
    /// is re-armed for the next version.
    ///
    /// Every consumer must be run with the same `count`, otherwise this spins
    /// forever.
    ///
    /// # Panics
    ///
    /// Panics if a producer has already been attached to this barrier.
    pub fn producer<F, C>(&self, count: usize, mut func: F, mut complete: C)
    where
        F: FnMut(usize) -> T,
        C: FnMut(usize, &mut [CacheLine<R>; WORKERS]),
    {
        assert!(
            self.producer_lock
                .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok(),
            "Attempted to create two producers to a RearmBarrier"
        );

        // Loop for versions
        for version in 0..count {
            let job = func(version);

            // SAFETY: we are the only producer. Either no job has ever been
            // written (probe == 0), or every consumer has finished with the
            // previous job (we observed probe == 2 * version below), so
            // nobody else is touching the slot.
            unsafe {
                if version > 0 {
                    self.val_ptr().drop_in_place();
                }
                self.val_ptr().write(job);
            }
            trace::record(trace::Event::JobWritten { version });

            // Mark task as ready
            let old = self.ticket_probe.fetch_add(1, Ordering::Release);
            trace::record(trace::Event::Publish { version, old });

            // Wait until every worker has completed this version
            let value = loop {
                let value = self.ticket_probe.load(Ordering::Relaxed);
                if value == (version + 1) * 2 {
                    break value;
                }
                core::hint::spin_loop();
            };
            fence(Ordering::Acquire);
            trace::record(trace::Event::ObserveDone { version, value });

            // SAFETY: all consumers have finished this version, so all
            // `WORKERS` states are initialized and no consumer touches them
            // until we publish the next version. `MaybeUninit` and
            // `UnsafeCell` are `repr(transparent)`, so the array of states
            // has the layout of `[CacheLine<R>; WORKERS]`.
            unsafe {
                complete(
                    version,
                    &mut *self.state.as_ptr().cast::<[CacheLine<R>; WORKERS]>().cast_mut(),
                );
            }
        }
    }

    /// Run consumer `consumer_id` for `count` versions, calling `func` with
    /// the version, a reference to the job and this worker's result slot
    /// (initialized from `state`) each time a job becomes available.
    ///
    /// # Panics
    ///
    /// Panics if `consumer_id >= WORKERS` or if a consumer with the same ID
    /// has already been attached to this barrier.
    pub fn consumer<F>(&self, count: usize, consumer_id: usize, state: R, mut func: F)
    where
        F: FnMut(usize, &T, &mut R),
    {
        // Make sure the consumer ID is valid
        assert!(consumer_id < WORKERS, "Consumer ID too large");

        // Ensure exclusive access for this consumer ID
        assert!(
            self.consumer_lock[consumer_id]
                .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok(),
            "Attempted to create two consumers with the same ID"
        );

        // SAFETY: we are the only consumer with this ID, and the producer only
        // touches the states after all consumers have finished a version.
        unsafe {
            self.state_ptr(consumer_id).write(state);
        }
        trace::record(trace::Event::StateInit { id: consumer_id });

        let tickets = self.tickets();

        for version in 0..count {
            // Wait until task is ready
            let value = loop {
                let value = self.ticket_probe.load(Ordering::Relaxed);
                if value > version * 2 {
                    break value;
                }
                core::hint::spin_loop();
            };
            fence(Ordering::Acquire);
            trace::record(trace::Event::ObserveReady { id: consumer_id, version, value });

            // SAFETY: the producer has published this version and will not
            // touch the job until we (and everyone else) increment the
            // tickets below; the state is ours alone.
            unsafe {
                func(version, &*self.val_ptr(), &mut *self.state_ptr(consumer_id));
            }

            let mut ticket_id = Self::TICKET_TREE_SIZE + consumer_id / CLUSTER;
            let mut win_id = consumer_id / CLUSTER;
            let mut win_size = CLUSTER;
            let mut merge_amount = 1;
            loop {
                // How many workers are in this window, limited by the total
                // number of workers
                let target_val = win_size.min(WORKERS - win_id * win_size);

                let old = tickets[ticket_id].fetch_add(merge_amount, Ordering::AcqRel);
                let new_val = old + merge_amount;
                trace::record(trace::Event::Ticket {
                    id: consumer_id,
                    version,
                    ticket: ticket_id,
                    amount: merge_amount,
                    old,
                });

                // Every worker has completed this version
                if new_val == WORKERS * (version + 1) {
                    let old = self.ticket_probe.fetch_add(1, Ordering::Release);
                    trace::record(trace::Event::Finish { id: consumer_id, version, old });
                    break;
                }

                // We reached the root of the tree, or didn't fill the window,
                // stop traversing the tree.
                if ticket_id == 0 || new_val != target_val * (version + 1) {
                    break;
                }

                merge_amount = target_val;
                ticket_id = (ticket_id - 1) / CLUSTER;
                win_id /= CLUSTER;
                win_size *= CLUSTER;
            }
        }
    }
}

impl<T, R, const WORKERS: usize, const CLUSTER: usize> Drop
    for RearmBarrier<T, R, WORKERS, CLUSTER>
{
    fn drop(&mut self) {
        // A job has been written iff the producer ever published one
        if *self.ticket_probe.get_mut() > 0 {
            // SAFETY: `&mut self` means no consumer is running, and the slot
            // was initialized by the producer.
            unsafe { self.val_ptr().drop_in_place() };
        }

        // A state is initialized iff its consumer ID was claimed
        for id in 0..WORKERS {
            if *self.consumer_lock[id].get_mut() {
                // SAFETY: as above, claimed IDs wrote their state before
                // doing anything else.
                unsafe { self.state_ptr(id).drop_in_place() };
            }
        }
    }
}

#[cfg(test)]
mod test {
    extern crate std;

    use crate::*;
    use std::sync::Arc;
    use std::vec::Vec;

    #[test]
    fn ticket_storage_fits() {
        for cluster in 2..=16 {
            for workers in 1..=4096 {
                assert!(
                    ticket_storage(workers, cluster) <= TICKETS_PER_WORKER * workers,
                    "workers={workers} cluster={cluster}"
                );
            }
        }
    }

    #[test]
    fn ticket_storage_examples() {
        // The configuration in the module diagram
        assert_eq!(ticket_storage(5, 2), 6);
        assert_eq!(ticket_storage(7, 2), 7);
        assert_eq!(ticket_storage(1, 2), 2);
        assert_eq!(ticket_storage(9, 3), 4);
    }

    fn run<const WORKERS: usize, const CLUSTER: usize>(count: usize) {
        #[derive(Debug)]
        enum Event {
            Foo(usize),
            Foop(usize),
        }

        let barrier = RearmBarrier::<Event, (usize, usize), WORKERS, CLUSTER>::new();

        std::thread::scope(|s| {
            // Create all worker threads
            for id in 0..WORKERS {
                let barrier = &barrier;
                s.spawn(move || {
                    barrier.consumer(count, id, (0, 0), |version, event, result| {
                        let v = match event {
                            Event::Foo(v) => {
                                assert_eq!(version % 2, 0);
                                *v
                            }
                            Event::Foop(v) => {
                                assert_eq!(version % 2, 1);
                                *v
                            }
                        };
                        assert_eq!(v, version);
                        *result = (id, version);
                    });
                });
            }

            // Schedule work
            let mut completions = 0;
            barrier.producer(
                count,
                |version| {
                    if version % 2 == 0 {
                        Event::Foo(version)
                    } else {
                        Event::Foop(version)
                    }
                },
                |version, results| {
                    assert_eq!(version, completions);
                    completions += 1;
                    for (id, r) in results.iter().enumerate() {
                        assert_eq!(**r, (id, version));
                    }
                },
            );
            assert_eq!(completions, count);
        });
    }

    #[test]
    fn workers_7_cluster_2() {
        run::<7, 2>(1000);
    }

    /// The configuration in which sizing the ticket array by `WORKERS`
    /// alone is too small
    #[test]
    fn workers_5_cluster_2() {
        run::<5, 2>(1000);
    }

    #[test]
    fn single_worker() {
        run::<1, 2>(1000);
    }

    #[test]
    fn various_shapes() {
        run::<2, 2>(200);
        run::<3, 2>(200);
        run::<4, 2>(200);
        run::<6, 2>(200);
        run::<8, 2>(200);
        run::<3, 3>(200);
        run::<5, 3>(200);
        run::<7, 3>(200);
        run::<8, 4>(200);
        run::<6, 8>(200);
    }

    #[test]
    fn zero_count_is_a_noop() {
        let barrier = RearmBarrier::<u8, u8, 2, 2>::new();
        std::thread::scope(|s| {
            for id in 0..2 {
                let barrier = &barrier;
                s.spawn(move || barrier.consumer(0, id, 0, |_, _, _| unreachable!()));
            }
            barrier.producer(0, |_| unreachable!(), |_, _| unreachable!());
        });
    }

    #[test]
    fn values_are_dropped() {
        const WORKERS: usize = 3;
        const COUNT: usize = 50;

        // Every job and every state holds an `Arc` clone; after the barrier is
        // dropped, all of them must be gone.
        let token = Arc::new(());
        {
            let barrier = RearmBarrier::<Arc<()>, Arc<()>, WORKERS, 2>::new();
            std::thread::scope(|s| {
                for id in 0..WORKERS {
                    let barrier = &barrier;
                    let token = token.clone();
                    s.spawn(move || barrier.consumer(COUNT, id, token, |_, _, _| {}));
                }
                barrier.producer(COUNT, |_| token.clone(), |_, _| {});
            });
            assert_eq!(Arc::strong_count(&token), 1 + WORKERS + 1);
        }
        assert_eq!(Arc::strong_count(&token), 1);
    }

    #[test]
    fn partially_used_barrier_drops_correctly() {
        let token = Arc::new(());
        {
            // Never used at all
            let _barrier = RearmBarrier::<Arc<()>, Arc<()>, 2, 2>::new();
        }
        {
            // Consumers attached but nothing produced
            let barrier = RearmBarrier::<Arc<()>, Arc<()>, 2, 2>::new();
            std::thread::scope(|s| {
                for id in 0..2 {
                    let barrier = &barrier;
                    let token = token.clone();
                    s.spawn(move || barrier.consumer(0, id, token, |_, _, _| {}));
                }
            });
            assert_eq!(Arc::strong_count(&token), 3);
        }
        assert_eq!(Arc::strong_count(&token), 1);
    }

    #[test]
    #[should_panic(expected = "two producers")]
    fn two_producers_panic() {
        let barrier = RearmBarrier::<u8, u8, 1, 2>::new();
        barrier.producer(0, |_| 0, |_, _| {});
        barrier.producer(0, |_| 0, |_, _| {});
    }

    #[test]
    #[should_panic(expected = "same ID")]
    fn duplicate_consumer_panics() {
        let barrier = RearmBarrier::<u8, u8, 1, 2>::new();
        barrier.consumer(0, 0, 0, |_, _, _| {});
        barrier.consumer(0, 0, 0, |_, _, _| {});
    }

    #[test]
    #[should_panic(expected = "too large")]
    fn consumer_id_out_of_range_panics() {
        let barrier = RearmBarrier::<u8, u8, 1, 2>::new();
        barrier.consumer(0, 1, 0, |_, _, _| {});
    }

    #[test]
    fn works_in_a_static() {
        static BARRIER: RearmBarrier<u32, u32, 2, 2> = RearmBarrier::new();
        std::thread::scope(|s| {
            for id in 0..2 {
                s.spawn(move || BARRIER.consumer(10, id, 0, |v, job, r| *r = job + v as u32));
            }
            let mut seen = Vec::new();
            BARRIER.producer(10, |v| v as u32, |v, r| seen.push((v, r[0].0, r[1].0)));
            for (v, a, b) in seen {
                assert_eq!(a, 2 * v as u32);
                assert_eq!(b, 2 * v as u32);
            }
        });
    }
}
