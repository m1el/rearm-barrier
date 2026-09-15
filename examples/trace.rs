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
use rearm_barrier::{ticket_storage, RearmBarrier};
use std::cell::RefCell;
use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::{Arc, Mutex};
use std::time::Duration;

/// Every thread's trace buffer, so that a watchdog can dump them all
static BUFFERS: Mutex<Vec<Arc<Mutex<String>>>> = Mutex::new(Vec::new());

/// Whether the trace has been printed (by the run finishing or the watchdog)
static PRINTED: Mutex<bool> = Mutex::new(false);

thread_local! {
    /// This thread's trace buffer; only program order within a thread matters
    static BUF: RefCell<Option<Arc<Mutex<String>>>> = const { RefCell::new(None) };
}

/// Give the current thread a trace buffer
fn attach() {
    let buf = Arc::new(Mutex::new(String::new()));
    BUFFERS.lock().unwrap().push(buf.clone());
    BUF.with(|b| *b.borrow_mut() = Some(buf));
}

fn emit(f: impl FnOnce(&mut String)) {
    BUF.with(|b| {
        if let Some(buf) = &*b.borrow() {
            f(&mut buf.lock().unwrap());
        }
    });
}

/// Print the header and every buffer once; returns whether this call printed
fn dump(header: &str, complete: bool) -> bool {
    let mut printed = PRINTED.lock().unwrap();
    if *printed {
        return false;
    }
    let mut out = String::from(header);
    for buf in BUFFERS.lock().unwrap().iter() {
        out.push_str(&buf.lock().unwrap());
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

/// The crate-side hook: format the event in trace-file syntax
fn hook(ev: &Event) {
    emit(|b| {
        let _ = match *ev {
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
        };
    });
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

/// Run one barrier for `count` versions; the trace ends up in `BUFFERS`
fn run<const W: usize, const C: usize>(count: usize, seed: u64, level: u32) {
    let barrier = RearmBarrier::<usize, Option<usize>, W, C>::new();

    std::thread::scope(|s| {
        for id in 0..W {
            let barrier = &barrier;
            s.spawn(move || {
                attach();
                let mut rng = Rng::new(seed, id as u64 + 1);
                barrier.consumer(count, id, None, |version, job, result| {
                    jitter(&mut rng, level);
                    *result = Some(*job);
                    emit(|b| writeln!(b, "c {id} func {version} {job}").unwrap());
                    jitter(&mut rng, level);
                });
            });
        }

        attach();
        let mut rng_build = Rng::new(seed, 0);
        let mut rng_complete = Rng::new(seed, u64::MAX);
        barrier.producer(
            count,
            |version| {
                jitter(&mut rng_build, level);
                version
            },
            |version, results| {
                emit(|b| {
                    write!(b, "p complete {version}").unwrap();
                    for r in results.iter() {
                        match r.0 {
                            Some(v) => write!(b, " {v}").unwrap(),
                            None => write!(b, " -").unwrap(),
                        }
                    }
                    b.push('\n');
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

            let watchdog_header = header.clone();
            std::thread::spawn(move || {
                std::thread::sleep(timeout);
                if dump(&watchdog_header, false) {
                    eprintln!("timed out after {timeout:?}; partial trace printed");
                    std::process::exit(3);
                }
            });

            trace::set_hook(hook);
            dispatch(w, c, count, num(seed), num(level) as u32);
            dump(&header, true);
        }
        _ => usage(),
    }
}
