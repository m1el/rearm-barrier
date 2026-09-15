//! Round-trip latency of `RearmBarrier` against two simpler barriers with the
//! same interface, all using every core: one producer thread plus
//! `cores - 1` consumer threads.
//!
//! * `rearm C=..`: this crate, with completion counted by a tree of fan-in `C`.
//! * `atomic`: the same spin-on-probe protocol, but every worker increments one
//!   shared completion counter, so all of them hit the same cache line on
//!   every round.
//! * `mutex`: a single `std::sync::Mutex` holding the published version and
//!   the completion count; every thread spins by locking it to poll.
//!
//! One round = the producer builds a job, every consumer processes it and
//! writes its result, and the producer reads all results. A round's consumer
//! work is `WORK` iterations of xorshift, so `WORK = 0` measures coordination
//! overhead alone.
//!
//! Worker counts are const generics, so only the counts in `WORKER_STEPS`
//! are compiled in: every count up to 16, then common logical CPU counts up
//! to 768 together with one less (a producer plus that many workers fills
//! the machine). `--workers max` (the default) is `cores - 1`, `--workers
//! sweep` runs a geometric ladder of counts up to `cores - 1`. Asking for
//! more workers than that is refused unless `--oversubscribe` is given.
//!
//! ```text
//! cargo bench --bench barrier
//! cargo bench --bench barrier -- --workers sweep --cluster 4,16,64
//! cargo bench --bench barrier -- --workers 3,7 --cluster 2,4,8 --work 0,100,10000 --trials 7 --time-ms 1000
//! ```

use rearm_barrier::{CacheLine, RearmBarrier};
use std::cell::UnsafeCell;
use std::hint::black_box;
use std::sync::atomic::{fence, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

/// The interface shared by every barrier under test
trait Barrier<const W: usize>: Sync {
    fn new() -> Self;

    fn producer(
        &self,
        count: usize,
        func: impl FnMut(usize) -> u64,
        complete: impl FnMut(usize, &mut [CacheLine<u64>; W]),
    );

    fn consumer(&self, count: usize, id: usize, func: impl FnMut(usize, &u64, &mut u64));
}

impl<const W: usize, const C: usize> Barrier<W> for RearmBarrier<u64, u64, W, C> {
    fn new() -> Self {
        RearmBarrier::new()
    }

    fn producer(
        &self,
        count: usize,
        func: impl FnMut(usize) -> u64,
        complete: impl FnMut(usize, &mut [CacheLine<u64>; W]),
    ) {
        RearmBarrier::producer(self, count, func, complete)
    }

    fn consumer(&self, count: usize, id: usize, func: impl FnMut(usize, &u64, &mut u64)) {
        RearmBarrier::consumer(self, count, id, 0, func)
    }
}

/// The crate's protocol with the ticket tree replaced by one shared counter
struct AtomicBarrier<const W: usize> {
    /// `2 * v + 1`: job `v` published, `2 * v + 2`: every worker finished it
    probe: CacheLine<AtomicUsize>,
    /// Total number of completions over all versions
    done: CacheLine<AtomicUsize>,
    job: CacheLine<UnsafeCell<u64>>,
    results: UnsafeCell<[CacheLine<u64>; W]>,
}

// SAFETY: the job is written only while no consumer is between its fence and
// its completion increment, and each result slot is written by one consumer
// and read by the producer only after every consumer has finished the version.
unsafe impl<const W: usize> Sync for AtomicBarrier<W> {}

impl<const W: usize> Barrier<W> for AtomicBarrier<W> {
    fn new() -> Self {
        AtomicBarrier {
            probe: CacheLine(AtomicUsize::new(0)),
            done: CacheLine(AtomicUsize::new(0)),
            job: CacheLine(UnsafeCell::new(0)),
            results: UnsafeCell::new([CacheLine(0); W]),
        }
    }

    fn producer(
        &self,
        count: usize,
        mut func: impl FnMut(usize) -> u64,
        mut complete: impl FnMut(usize, &mut [CacheLine<u64>; W]),
    ) {
        for version in 0..count {
            let job = func(version);
            // SAFETY: every consumer finished the previous version (or none
            // has started), see the `Sync` impl
            unsafe { *self.job.get() = job };
            self.probe.fetch_add(1, Ordering::Release);

            while self.probe.load(Ordering::Relaxed) != 2 * version + 2 {
                core::hint::spin_loop();
            }
            fence(Ordering::Acquire);

            // SAFETY: every consumer finished this version
            complete(version, unsafe { &mut *self.results.get() });
        }
    }

    fn consumer(&self, count: usize, id: usize, mut func: impl FnMut(usize, &u64, &mut u64)) {
        assert!(id < W);
        for version in 0..count {
            while self.probe.load(Ordering::Relaxed) <= 2 * version {
                core::hint::spin_loop();
            }
            fence(Ordering::Acquire);

            // SAFETY: the job is published and stable until we count
            // ourselves done; result slot `id` is ours
            unsafe {
                let result = &mut (*self.results.get().cast::<CacheLine<u64>>().add(id)).0;
                func(version, &*self.job.get(), result);
            }

            if self.done.fetch_add(1, Ordering::AcqRel) + 1 == W * (version + 1) {
                self.probe.fetch_add(1, Ordering::Release);
            }
        }
    }
}

/// Everything behind one mutex; threads poll it by locking
struct MutexBarrier<const W: usize> {
    shared: Mutex<Counts>,
    job: CacheLine<UnsafeCell<u64>>,
    results: UnsafeCell<[CacheLine<u64>; W]>,
}

struct Counts {
    /// Number of versions published
    published: usize,
    /// Total number of completions over all versions
    done: usize,
}

// SAFETY: as for `AtomicBarrier`, with the mutex providing the ordering
unsafe impl<const W: usize> Sync for MutexBarrier<W> {}

impl<const W: usize> Barrier<W> for MutexBarrier<W> {
    fn new() -> Self {
        MutexBarrier {
            shared: Mutex::new(Counts { published: 0, done: 0 }),
            job: CacheLine(UnsafeCell::new(0)),
            results: UnsafeCell::new([CacheLine(0); W]),
        }
    }

    fn producer(
        &self,
        count: usize,
        mut func: impl FnMut(usize) -> u64,
        mut complete: impl FnMut(usize, &mut [CacheLine<u64>; W]),
    ) {
        for version in 0..count {
            let job = func(version);
            {
                let mut shared = self.shared.lock().unwrap();
                // SAFETY: under the lock, after every consumer finished the
                // previous version
                unsafe { *self.job.get() = job };
                shared.published = version + 1;
            }

            loop {
                if self.shared.lock().unwrap().done == W * (version + 1) {
                    break;
                }
                core::hint::spin_loop();
            }

            // SAFETY: every consumer finished this version
            complete(version, unsafe { &mut *self.results.get() });
        }
    }

    fn consumer(&self, count: usize, id: usize, mut func: impl FnMut(usize, &u64, &mut u64)) {
        assert!(id < W);
        for version in 0..count {
            loop {
                if self.shared.lock().unwrap().published > version {
                    break;
                }
                core::hint::spin_loop();
            }

            // SAFETY: as in `AtomicBarrier::consumer`
            unsafe {
                let result = &mut (*self.results.get().cast::<CacheLine<u64>>().add(id)).0;
                func(version, &*self.job.get(), result);
            }

            self.shared.lock().unwrap().done += 1;
        }
    }
}

/// The per-worker job: `work` rounds of xorshift seeded from the job and ID
#[inline]
fn work(job: u64, id: usize, iters: u64) -> u64 {
    let mut x = (job + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (id as u64 + 1);
    for _ in 0..iters {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
    }
    x
}

/// Run `rounds` rounds and return the mean time per round after `warmup`
fn run_once<B: Barrier<W>, const W: usize>(rounds: usize, warmup: usize, iters: u64) -> Duration {
    assert!(warmup >= 1 && rounds > warmup);
    let barrier = B::new();
    let mut start = None;
    let mut end = None;

    std::thread::scope(|s| {
        for id in 0..W {
            let barrier = &barrier;
            s.spawn(move || {
                barrier.consumer(rounds, id, |_version, job, result| {
                    *result = work(*job, id, black_box(iters));
                });
            });
        }

        barrier.producer(
            rounds,
            |version| version as u64,
            |version, results| {
                let sum = results.iter().fold(0u64, |a, r| a.wrapping_add(r.0));
                black_box(sum);
                if version + 1 == warmup {
                    start = Some(Instant::now());
                } else if version + 1 == rounds {
                    end = Some(Instant::now());
                }
            },
        );
    });

    (end.unwrap() - start.unwrap()) / (rounds - warmup) as u32
}

struct Stats {
    median: Duration,
    min: Duration,
    max: Duration,
    rounds: usize,
}

/// Calibrate the round count to about `time` per trial, then run `trials`
fn measure<B: Barrier<W>, const W: usize>(opts: &Opts, iters: u64) -> Stats {
    // Kept small so that slow configurations (a mutex polled by hundreds of
    // threads) finish in reasonable time; fast ones get more rounds below.
    const WARMUP: usize = 100;
    let estimate = run_once::<B, W>(WARMUP + 200, WARMUP, iters);
    let rounds = (opts.time.as_nanos() / estimate.as_nanos().max(1)).clamp(200, 50_000_000) as usize;

    let mut samples: Vec<Duration> =
        (0..opts.trials).map(|_| run_once::<B, W>(WARMUP + rounds, WARMUP, iters)).collect();
    samples.sort();
    Stats {
        median: samples[samples.len() / 2],
        min: samples[0],
        max: samples[samples.len() - 1],
        rounds,
    }
}

fn row(name: &str, stats: &Stats, baseline: Option<Duration>) {
    let ns = |d: Duration| d.as_nanos() as f64;
    let rel = match baseline {
        Some(b) => format!("{:>8.2}x", ns(stats.median) / ns(b)),
        None => format!("{:>9}", "1.00x"),
    };
    println!(
        "  {name:<12} {:>12.0} {:>12.0} {:>12.0} {:>14.0} {rel} {:>10}",
        ns(stats.median),
        ns(stats.min),
        ns(stats.max),
        1e9 / ns(stats.median),
        stats.rounds,
    );
}

/// Every barrier at `W` workers, for each configured work amount
fn run_all<const W: usize>(opts: &Opts) {
    for &iters in &opts.work {
        println!("\nworkers = {W} (+1 producer), work = {iters} xorshift iterations per worker per round");
        println!(
            "  {:<12} {:>12} {:>12} {:>12} {:>14} {:>9} {:>10}",
            "barrier", "median ns", "min ns", "max ns", "rounds/s", "vs best", "rounds"
        );

        let mut results: Vec<(String, Stats)> = Vec::new();
        for &c in &opts.clusters {
            let stats = match c {
                2 => measure::<RearmBarrier<u64, u64, W, 2>, W>(opts, iters),
                3 => measure::<RearmBarrier<u64, u64, W, 3>, W>(opts, iters),
                4 => measure::<RearmBarrier<u64, u64, W, 4>, W>(opts, iters),
                8 => measure::<RearmBarrier<u64, u64, W, 8>, W>(opts, iters),
                16 => measure::<RearmBarrier<u64, u64, W, 16>, W>(opts, iters),
                32 => measure::<RearmBarrier<u64, u64, W, 32>, W>(opts, iters),
                64 => measure::<RearmBarrier<u64, u64, W, 64>, W>(opts, iters),
                _ => {
                    eprintln!("unsupported cluster {c}: use 2, 3, 4, 8, 16, 32 or 64");
                    std::process::exit(2);
                }
            };
            results.push((format!("rearm C={c}"), stats));
        }
        results.push(("atomic".into(), measure::<AtomicBarrier<W>, W>(opts, iters)));
        results.push(("mutex".into(), measure::<MutexBarrier<W>, W>(opts, iters)));

        let best = results.iter().map(|(_, s)| s.median).min().unwrap();
        for (name, stats) in &results {
            row(name, stats, if stats.median == best { None } else { Some(best) });
        }
    }
}

/// Generates `WORKER_STEPS` (every supported worker count, ascending) and
/// `dispatch`. The small counts are listed as is; each CPU count `n` in the
/// second list also supports `n - 1` workers.
macro_rules! worker_steps {
    ([$($small:literal),* $(,)?], [$($cpus:literal),* $(,)?]) => {
        const WORKER_STEPS: &[usize] = &[$($small,)* $($cpus - 1, $cpus,)*];

        fn dispatch(opts: &Opts, w: usize) -> bool {
            match w {
                $($small => run_all::<$small>(opts),)*
                $(
                    w if w == $cpus - 1 => run_all::<{ $cpus - 1 }>(opts),
                    $cpus => run_all::<$cpus>(opts),
                )*
                _ => return false,
            }
            true
        }
    };
}

worker_steps!(
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
    [
        20, 24, 28, 32, 36, 40, 48, 56, 64, 72, 80, 88, 96, 112, 128, 144, 160, 176, 192,
        224, 256, 288, 320, 352, 384, 448, 512, 576, 640, 704, 768,
    ]
);

/// `--workers sweep`: roughly doubling steps, each one below a power-of-two
/// or common CPU count so a producer fits too, plus `max`
fn sweep(max: usize) -> Vec<usize> {
    let mut steps: Vec<usize> = [1, 3, 7, 11, 15, 23, 31, 47, 63, 95, 127, 191, 255, 383, 511, 767]
        .into_iter()
        .filter(|&w| w < max)
        .collect();
    steps.push(max);
    steps
}

struct Opts {
    workers: Vec<usize>,
    cores: usize,
    oversubscribe: bool,
    clusters: Vec<usize>,
    work: Vec<u64>,
    trials: usize,
    time: Duration,
}

fn parse_list<T: std::str::FromStr>(flag: &str, s: Option<String>) -> Vec<T> {
    let s = s.unwrap_or_else(|| usage(&format!("{flag} needs a value")));
    s.split(',')
        .map(|x| x.trim().parse().unwrap_or_else(|_| usage(&format!("bad value `{x}` for {flag}"))))
        .collect()
}

fn usage(msg: &str) -> ! {
    eprintln!(
        "{msg}\nusage: cargo bench --bench barrier -- [--workers max|sweep|N,..] [--cluster C,..] [--work ITERS,..] [--trials N] [--time-ms MS] [--oversubscribe]"
    );
    std::process::exit(2)
}

/// The largest supported worker count that leaves a core for the producer
fn max_workers(cores: usize) -> usize {
    let want = cores.saturating_sub(1).max(1);
    WORKER_STEPS.iter().copied().filter(|&w| w <= want).max().unwrap_or(1)
}

fn main() {
    let cores = std::thread::available_parallelism().map_or(2, |n| n.get());
    let mut opts = Opts {
        workers: Vec::new(),
        cores,
        oversubscribe: false,
        clusters: vec![2, 4, 8],
        work: vec![0, 1000],
        trials: 5,
        time: Duration::from_millis(500),
    };

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--workers" => {
                let max = max_workers(cores);
                opts.workers = match args.next().as_deref() {
                    Some("max") => vec![max],
                    Some("sweep") => sweep(max),
                    other => parse_list("--workers", other.map(str::to_owned)),
                }
            }
            "--cluster" => opts.clusters = parse_list("--cluster", args.next()),
            "--work" => opts.work = parse_list("--work", args.next()),
            "--trials" => opts.trials = parse_list::<usize>("--trials", args.next())[0].max(1),
            "--time-ms" => opts.time = Duration::from_millis(parse_list("--time-ms", args.next())[0]),
            "--oversubscribe" => opts.oversubscribe = true,
            // passed by `cargo bench`
            "--bench" => {}
            other => usage(&format!("unknown argument `{other}`")),
        }
    }

    println!(
        "{cores} cores; {} trials of ~{:?} each; times are per round (median/min/max over trials)",
        opts.trials, opts.time
    );
    if opts.workers.is_empty() {
        opts.workers = vec![max_workers(cores)];
    }
    // Check everything before running anything
    for &w in &opts.workers {
        if !WORKER_STEPS.contains(&w) {
            usage(&format!("unsupported worker count {w}; supported: {WORKER_STEPS:?}"));
        }
        // Every thread spins, so more threads than cores just burns the
        // machine and measures the scheduler
        if w + 1 > opts.cores && !opts.oversubscribe {
            usage(&format!(
                "{w} workers + 1 producer would oversubscribe {} cores with spinning threads; \
                 pass --oversubscribe if you really mean it",
                opts.cores
            ));
        }
    }
    for &w in &opts.workers {
        assert!(dispatch(&opts, w));
    }
}
