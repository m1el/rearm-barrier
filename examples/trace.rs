//! Trace harness for differential testing against the Lean model in `model/`.
//!
//! `trace run WORKERS CLUSTER COUNT SEED JITTER [TIMEOUT_SECS]` runs the
//! barrier for `COUNT` versions on real threads and prints a trace file that
//! `rearm-model check` understands: a `config` line followed by one event per
//! line, grouped by thread. The shape must be one of `SHAPES` because
//! `WORKERS` and `CLUSTER` are const generics. `JITTER` (0, 1 or 2) inserts
//! random delays into the user closures so that different runs exercise
//! different interleavings.
//!
//! If the run does not finish within `TIMEOUT_SECS` (default 60) — the
//! barrier hung — the events recorded so far are printed followed by a
//! `timeout` line and the process exits with status 3; the model checker then
//! reports whether it agrees that the recorded prefix leads to a deadlock.
//!
//! `trace storage MAX_WORKERS MAX_CLUSTER` prints `ticket_storage` for every
//! shape, in the same format as `rearm-model storage`.
//!
//! See `scripts/difftest.sh` for how the pieces fit together.

use rearm_barrier::trace::{self, Event};
use rearm_barrier::{ticket_storage, CacheLine, RearmBarrier};
use std::cell::UnsafeCell;
use std::fmt::Write as _;
use std::io::Write as _;
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Duration;

// Recording must not synchronize the barrier's threads with each other:
// a mutex, an allocation (the allocator's lock) or a write to stdout between
// two atomic operations adds happens-before edges that the barrier itself
// does not have, and hides exactly the weak-memory schedules the test is
// meant to exercise. So each thread appends fixed-size records to a log that
// was allocated before any thread was spawned and that only it writes, and
// the logs are formatted after the threads have been joined.
//
// The only atomics a recording thread touches are its own log's `len` and
// `overflow`. It writes them with `Release`, but only the watchdog ever
// acquires them, so the extra edges all point from a barrier thread to the
// watchdog, never between barrier threads.

/// One entry in a thread's log
#[derive(Clone, Copy)]
enum Rec {
    /// Reported by the crate
    Crate(Event),
    /// Consumer `id` ran its closure for `version` and saw `job`
    Func { id: usize, version: usize, job: usize },
    /// The producer's completion callback for `version`; followed by one
    /// `Result` per worker
    Complete { version: usize },
    /// One worker's result, part of the preceding `Complete`
    Result(Option<usize>),
}

/// A fixed-capacity, single-writer log
struct Log {
    recs: Box<[UnsafeCell<MaybeUninit<Rec>>]>,
    /// Number of initialized records; written only by the owning thread
    len: CacheLine<AtomicUsize>,
    /// Set by the owning thread if it ran out of capacity
    overflow: AtomicBool,
}

// SAFETY: a record is written once, by the owning thread, before `len` is
// raised past it; other threads only read records below a `len` they loaded.
unsafe impl Sync for Log {}

impl Log {
    fn new(capacity: usize) -> Self {
        Log {
            recs: (0..capacity).map(|_| UnsafeCell::new(MaybeUninit::uninit())).collect(),
            len: CacheLine(AtomicUsize::new(0)),
            overflow: AtomicBool::new(false),
        }
    }

    /// Append the records `rec(0), .., rec(count - 1)` as one unit, so a
    /// snapshot never sees half of them. Must only be called by the thread
    /// that owns this log.
    fn push_with(&self, count: usize, mut rec: impl FnMut(usize) -> Rec) {
        // Only this thread writes `len`, so reading it needs no synchronization
        let n = self.len.load(Ordering::Relaxed);
        if self.recs.len() - n < count {
            self.overflow.store(true, Ordering::Release);
            return;
        }
        for i in 0..count {
            // SAFETY: slots at and above `len` are only touched by this thread
            unsafe { (*self.recs[n + i].get()).write(rec(i)) };
        }
        self.len.store(n + count, Ordering::Release);
    }

    fn push(&self, rec: Rec) {
        self.push_with(1, |_| rec);
    }

    /// The records published so far
    fn snapshot(&self) -> &[Rec] {
        let n = self.len.load(Ordering::Acquire);
        // SAFETY: the first `n` records were initialized before `len` was
        // released as `n`, and are never written again.
        unsafe { core::slice::from_raw_parts(self.recs.as_ptr().cast::<Rec>(), n) }
    }
}

/// The logs of the current run: consumer `id` owns `LOGS[id]`, the producer
/// owns the last one. Set once, before any thread that records is spawned.
static LOGS: AtomicPtr<Vec<Log>> = AtomicPtr::new(core::ptr::null_mut());

/// Whether the trace has been printed (by the run finishing or the watchdog)
static PRINTED: Mutex<bool> = Mutex::new(false);

fn logs() -> &'static [Log] {
    // Stored before this thread was spawned, which already orders it
    // before us; `Relaxed` avoids adding an acquire of our own.
    let ptr = LOGS.load(Ordering::Relaxed);
    assert!(!ptr.is_null(), "trace logs not installed");
    // SAFETY: the pointer comes from `Box::leak` in `install_logs`
    unsafe { &*ptr }
}

/// Allocate every log for a run with `workers` consumers and `count` versions
fn install_logs(workers: usize, cluster: usize, count: usize) {
    // A consumer records at most `init` once and, per version, `ready`,
    // `func`, `finish` and one `ticket` per tree level (at most one per
    // ticket). The producer records `write`, `publish`, `wait` and `complete`
    // plus one result per worker per version.
    let per_version = 4 + workers + ticket_storage(workers, cluster);
    let capacity = 1 + count * per_version;
    let logs: Vec<Log> = (0..=workers).map(|_| Log::new(capacity)).collect();
    LOGS.store(Box::leak(Box::new(logs)), Ordering::Release);
}

fn consumer_log(id: usize) -> &'static Log {
    &logs()[id]
}

fn producer_log() -> &'static Log {
    logs().last().unwrap()
}

/// Format the logs in trace-file syntax: the producer, then each consumer
fn format_logs(out: &mut String) -> Result<(), String> {
    let logs = logs();
    let (consumers, producer) = logs.split_at(logs.len() - 1);
    // Take every snapshot before formatting any, so that a watchdog dump of a
    // run that is still moving gets prefixes that are as close as possible
    let snapshots: Vec<&[Rec]> = producer.iter().chain(consumers).map(Log::snapshot).collect();
    for (slot, (log, snapshot)) in producer.iter().chain(consumers).zip(snapshots).enumerate() {
        if log.overflow.load(Ordering::Acquire) {
            return Err(format!("trace log {slot} overflowed"));
        }
        let mut open = false;
        for rec in snapshot {
            if !matches!(rec, Rec::Result(_)) && open {
                out.push('\n');
                open = false;
            }
            let _ = match *rec {
                Rec::Crate(ev) => format_event(out, ev),
                Rec::Func { id, version, job } => writeln!(out, "c {id} func {version} {job}"),
                Rec::Complete { version } => {
                    open = true;
                    write!(out, "p complete {version}")
                }
                Rec::Result(Some(v)) => write!(out, " {v}"),
                Rec::Result(None) => write!(out, " -"),
            };
        }
        if open {
            out.push('\n');
        }
    }
    Ok(())
}

fn format_event(b: &mut String, ev: Event) -> core::fmt::Result {
    match ev {
        Event::JobWritten { version } => writeln!(b, "p write {version}"),
        Event::Publish { version, old } => writeln!(b, "p publish {version} {old}"),
        Event::ObserveDone { version, value } => writeln!(b, "p wait {version} {value}"),
        Event::StateInit { id } => writeln!(b, "c {id} init"),
        Event::ObserveReady { id, version, value } => {
            writeln!(b, "c {id} ready {version} {value}")
        }
        Event::Ticket { id, version, ticket, amount, old } => {
            writeln!(b, "c {id} ticket {version} {ticket} {amount} {old}")
        }
        Event::Finish { id, version, old } => writeln!(b, "c {id} finish {version} {old}"),
    }
}

/// Print the header and every log once; returns whether this call printed
fn dump(header: &str, complete: bool) -> bool {
    let mut printed = PRINTED.lock().unwrap();
    if *printed {
        return false;
    }
    let mut out = String::from(header);
    if let Err(e) = format_logs(&mut out) {
        eprintln!("{e}: increase the capacity in install_logs");
        std::process::exit(4);
    }
    if !complete {
        out.push_str("timeout\n");
    }
    let mut stdout = std::io::stdout().lock();
    stdout.write_all(out.as_bytes()).unwrap();
    stdout.flush().unwrap();
    *printed = true;
    true
}

/// The crate-side hook: append the event to the log of the thread that
/// performed it, which the event identifies
fn hook(ev: &Event) {
    let log = match *ev {
        Event::JobWritten { .. } | Event::Publish { .. } | Event::ObserveDone { .. } => {
            producer_log()
        }
        Event::StateInit { id }
        | Event::ObserveReady { id, .. }
        | Event::Ticket { id, .. }
        | Event::Finish { id, .. } => consumer_log(id),
    };
    log.push(Rec::Crate(*ev));
}

/// xorshift64, seeded per thread
struct Rng(u64);

impl Rng {
    fn new(seed: u64, stream: u64) -> Self {
        let x = seed
            .wrapping_add(0x9E37_79B9_7F4A_7C15)
            .wrapping_mul(0xBF58_476D_1CE4_E5B9)
            ^ stream.wrapping_mul(0x94D0_49BB_1331_11EB);
        Rng(if x == 0 { 0x2545_F491_4F6C_DD1D } else { x })
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
}

/// Perturb the schedule: `level` 0 does nothing, higher levels spin, yield
/// or sleep for a random while.
fn jitter(rng: &mut Rng, level: u32) {
    if level == 0 {
        return;
    }
    match rng.next() % 8 {
        0 => std::thread::yield_now(),
        1 if level >= 2 => std::thread::sleep(Duration::from_micros(rng.next() % 100)),
        2 | 3 => {
            let spins = rng.next() % (2000 * u64::from(level));
            for _ in 0..spins {
                std::hint::spin_loop();
            }
        }
        _ => {}
    }
}

/// Run one barrier for `count` versions; the trace ends up in `LOGS`
fn run<const W: usize, const C: usize>(count: usize, seed: u64, level: u32) {
    let barrier = RearmBarrier::<usize, Option<usize>, W, C>::new();

    std::thread::scope(|s| {
        for id in 0..W {
            let barrier = &barrier;
            s.spawn(move || {
                let mut rng = Rng::new(seed, id as u64 + 1);
                barrier.consumer(count, id, None, |version, job, result| {
                    jitter(&mut rng, level);
                    *result = Some(*job);
                    consumer_log(id).push(Rec::Func { id, version, job: *job });
                    jitter(&mut rng, level);
                });
            });
        }

        let mut rng_build = Rng::new(seed, 0);
        let mut rng_complete = Rng::new(seed, u64::MAX);
        barrier.producer(
            count,
            |version| {
                jitter(&mut rng_build, level);
                version
            },
            |version, results| {
                producer_log().push_with(1 + W, |i| match i {
                    0 => Rec::Complete { version },
                    i => Rec::Result(results[i - 1].0),
                });
                jitter(&mut rng_complete, level);
            },
        );
    });
}

macro_rules! shapes {
    ($(($w:literal, $c:literal)),* $(,)?) => {
        /// The `(WORKERS, CLUSTER)` instantiations available to `run`
        const SHAPES: &[(usize, usize)] = &[$(($w, $c)),*];

        fn dispatch(w: usize, c: usize, count: usize, seed: u64, level: u32) -> bool {
            match (w, c) {
                $(($w, $c) => run::<$w, $c>(count, seed, level),)*
                _ => return false,
            }
            true
        }
    };
}

shapes!(
    (1, 2), (2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (7, 2), (8, 2), (9, 2), (11, 2), (16, 2), (17, 2),
    (3, 3), (4, 3), (5, 3), (7, 3), (9, 3), (10, 3), (13, 3),
    (4, 4), (5, 4), (8, 4), (9, 4), (17, 4),
    (6, 8), (9, 8), (16, 16), (17, 16),
);

fn usage() -> ! {
    eprintln!(
        "usage:\n  trace shapes\n  trace storage MAX_WORKERS MAX_CLUSTER\n  trace run WORKERS CLUSTER COUNT SEED JITTER [TIMEOUT_SECS]"
    );
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    let num = |s: &str| s.parse::<u64>().unwrap_or_else(|_| usage());

    match args.as_slice() {
        ["shapes"] => {
            for (w, c) in SHAPES {
                println!("{w} {c}");
            }
        }
        ["storage", mw, mc] => {
            let (mw, mc) = (num(mw) as usize, num(mc) as usize);
            for c in 2..=mc {
                for w in 1..=mw {
                    println!("{w} {c} {}", ticket_storage(w, c));
                }
            }
        }
        ["run", w, c, count, seed, level, rest @ ..] if rest.len() <= 1 => {
            let (w, c, count) = (num(w) as usize, num(c) as usize, num(count) as usize);
            let timeout = Duration::from_secs(rest.first().map_or(60, |t| num(t)));
            if !SHAPES.contains(&(w, c)) {
                eprintln!("unsupported shape {w} {c}: add it to SHAPES in examples/trace.rs");
                std::process::exit(2);
            }
            let header = format!("config {w} {c} {count}\n");

            // Everything shared with the recording threads is set up before
            // any of them (or the watchdog) is spawned
            install_logs(w, c, count);
            trace::set_hook(hook);

            let watchdog_header = header.clone();
            std::thread::spawn(move || {
                std::thread::sleep(timeout);
                if dump(&watchdog_header, false) {
                    eprintln!("timed out after {timeout:?}; partial trace printed");
                    std::process::exit(3);
                }
            });

            dispatch(w, c, count, num(seed), num(level) as u32);
            dump(&header, true);
        }
        _ => usage(),
    }
}
