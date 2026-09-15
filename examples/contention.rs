//! A cache-line cost model of barrier coordination, a lower bound for any
//! spin-waiting barrier with `RearmBarrier`'s interface, and a fit of the
//! model to `benches/barrier.rs` output. See `docs/contention-model.md`.
//!
//! # The model
//!
//! Cores run the barrier's programs over *cache lines* (each `CacheLine` in
//! the crate). A core holds a valid copy of a line or it does not; a write
//! makes the writer the only holder. Costs:
//!
//! | access | condition | cost |
//! |---|---|---|
//! | read (load, spin check) | holder | 0 |
//! | read | not a holder: **pull** | `t` |
//! | write (`fetch_add`, store) | only holder | 0 |
//! | write | holder among others: **upgrade** | `u` |
//! | write | not a holder: **RFO** | `t` |
//!
//! A spinning core that holds the line it spins on re-checks for free; when
//! someone else writes the line it must pull it again (that is how it sees
//! the change). Transfers on one line are served either one at a time
//! (`serial`: the line's owner hands it over to one core at a time) or with
//! reads in parallel (`parallel`: any number of pulls at once, writes
//! exclusive). The programs are the crate's (`rearm:C`) and the single shared
//! counter of the benchmark (`atomic`), optionally with the probe split into
//! a publish line and a done line (`+split`), a what-if the crate does not
//! implement.
//!
//! ```text
//! contention sim   [--workers N,..] [--design rearm:4,atomic,..] [--t NS] [--u NS] [--work NS] [--jitter NS]
//!                  [--discipline serial|parallel] [--results read|skip] [--rounds N]
//! contention fit   [--min-workers N] BENCH_OUTPUT..   fit t, u, jitter and a constant to `cargo bench --bench barrier` output
//! contention check TRACE..           compare per-ticket write counts of crate traces with the model
//! ```

use rearm_barrier::ticket_storage;
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

// ---------------------------------------------------------------------------
// Designs and parameters

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    /// The crate with fan-in `C`
    Rearm(usize),
    /// One shared completion counter
    Atomic,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Design {
    kind: Kind,
    /// Separate publish and done lines instead of one probe
    split: bool,
}

impl Design {
    fn parse(s: &str) -> Option<Design> {
        let (base, split) = match s.strip_suffix("+split") {
            Some(b) => (b, true),
            None => (s, false),
        };
        let kind = if base == "atomic" {
            Kind::Atomic
        } else {
            let c: usize = base.strip_prefix("rearm:")?.parse().ok()?;
            if c < 2 {
                return None;
            }
            Kind::Rearm(c)
        };
        Some(Design { kind, split })
    }

    fn name(&self) -> String {
        let base = match self.kind {
            Kind::Rearm(c) => format!("rearm C={c}"),
            Kind::Atomic => "atomic".into(),
        };
        if self.split {
            format!("{base}+split")
        } else {
            base
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Discipline {
    Serial,
    Parallel,
}

#[derive(Clone, Copy, Debug)]
struct Params {
    /// Cost of a pull or RFO
    t: f64,
    /// Cost of an upgrade (write by a holder that shares the line)
    u: f64,
    /// Per-worker work per round
    work: f64,
    /// Mean of the exponentially distributed extra delay before a woken
    /// spinner acts on the change it pulled (spin-loop period, SMT sibling,
    /// interrupts, ...)
    jitter: f64,
    discipline: Discipline,
    /// Whether the producer reads every result each round
    results: bool,
}

// ---------------------------------------------------------------------------
// Simulation

/// What a line is used for, for reporting
#[derive(Clone, Copy, PartialEq)]
enum Class {
    Signal,
    Job,
    Result,
    Counter,
}

const CLASSES: [(Class, &str); 4] =
    [(Class::Signal, "signal"), (Class::Job, "job"), (Class::Result, "result"), (Class::Counter, "counter")];

#[derive(Clone, Copy, Default, Debug)]
struct Counts {
    pulls: u64,
    rfos: u64,
    upgrades: u64,
}

impl Counts {
    fn sub(self, o: Counts) -> Counts {
        Counts { pulls: self.pulls - o.pulls, rfos: self.rfos - o.rfos, upgrades: self.upgrades - o.upgrades }
    }
}

struct Line {
    class: Class,
    /// Bitset of cores holding a valid copy
    holders: Vec<u64>,
    nholders: usize,
    value: usize,
    /// End of the last transfer (serial) / of any transfer (parallel)
    busy: f64,
    /// End of the last write transfer (parallel)
    busy_write: f64,
    /// Cores spinning on this line that must pull it when it is written
    spinners: Vec<usize>,
}

impl Line {
    fn new(class: Class, cores: usize) -> Line {
        Line {
            class,
            holders: vec![0; cores.div_ceil(64)],
            nholders: 0,
            value: 0,
            busy: 0.0,
            busy_write: 0.0,
            spinners: Vec::new(),
        }
    }

    fn holds(&self, core: usize) -> bool {
        self.holders[core / 64] >> (core % 64) & 1 == 1
    }

    fn add_holder(&mut self, core: usize) {
        if !self.holds(core) {
            self.holders[core / 64] |= 1 << (core % 64);
            self.nholders += 1;
        }
    }

    fn make_exclusive(&mut self, core: usize) {
        self.holders.iter_mut().for_each(|w| *w = 0);
        self.nholders = 0;
        self.add_holder(core);
    }
}

#[derive(Clone, Copy, Debug)]
enum Pred {
    Gt(usize),
    Eq(usize),
}

#[derive(Clone, Copy, Debug)]
enum Act {
    Read(usize),
    Write(usize, usize),
    Spin(usize, Pred),
    Work(f64),
    Mark,
    Stop,
}

#[derive(Clone, Copy, Default)]
struct CoreState {
    /// Woken by a write while spinning: its next successful check is delayed
    woken: bool,
    version: usize,
    pc: u8,
    /// Producer: next result to read
    index: usize,
    // Consumer walk state, as in `RearmBarrier::consumer`
    ticket: usize,
    win_id: usize,
    win_size: usize,
    amount: usize,
}

/// Line layout: 0 publish/probe, 1 done (split only), 2 job, results, counters
struct Sim {
    design: Design,
    p: Params,
    workers: usize,
    rounds: usize,
    tree_size: usize,
    lines: Vec<Line>,
    cores: Vec<CoreState>,
    /// Per class, counts at each producer round mark
    marks: Vec<(f64, [Counts; 4])>,
    counts: [Counts; 4],
    heap: BinaryHeap<Reverse<(Time, u64, usize, bool)>>,
    seq: u64,
    rng: u64,
    /// Transfers whose effect is pending, per core
    pending: Vec<Option<Act>>,
}

/// Totally ordered simulation time
#[derive(Clone, Copy, PartialEq)]
struct Time(f64);
impl Eq for Time {}
impl PartialOrd for Time {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Time {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.0.total_cmp(&o.0)
    }
}

const PRODUCER: usize = 0;
const PUBLISH: usize = 0;
const JOB: usize = 2;
const RESULTS: usize = 3;

/// `ticket_tree_alloc` from the crate
fn ticket_tree_alloc(base_size: usize, cluster: usize) -> usize {
    let (mut size, mut bot) = (1, 1);
    while bot * cluster < base_size {
        bot *= cluster;
        size += bot;
    }
    size
}

impl Sim {
    fn new(design: Design, p: Params, workers: usize, rounds: usize) -> Sim {
        let cores = workers + 1;
        let (counters, tree_size) = match design.kind {
            Kind::Rearm(c) => {
                let base = workers.div_ceil(c);
                let tree = ticket_tree_alloc(base, c);
                assert_eq!(tree + base, ticket_storage(workers, c), "model and crate disagree on the tree");
                (tree + base, tree)
            }
            Kind::Atomic => (1, 0),
        };
        let mut lines = vec![Line::new(Class::Signal, cores), Line::new(Class::Signal, cores), Line::new(Class::Job, cores)];
        lines.extend((0..workers).map(|_| Line::new(Class::Result, cores)));
        lines.extend((0..counters).map(|_| Line::new(Class::Counter, cores)));
        Sim {
            design,
            p,
            workers,
            rounds,
            tree_size,
            lines,
            cores: vec![CoreState::default(); cores],
            marks: Vec::new(),
            counts: [Counts::default(); 4],
            heap: BinaryHeap::new(),
            seq: 0,
            rng: 0x2545_F491_4F6C_DD1D,
            pending: vec![None; cores],
        }
    }

    fn done_line(&self) -> usize {
        if self.design.split {
            1
        } else {
            PUBLISH
        }
    }

    fn counter(&self, i: usize) -> usize {
        RESULTS + self.workers + i
    }

    /// The action core `c` wants to perform next
    fn act(&self, c: usize) -> Act {
        let s = &self.cores[c];
        let split = self.design.split;
        if c == PRODUCER {
            if s.version == self.rounds {
                return Act::Stop;
            }
            return match s.pc {
                0 => Act::Write(JOB, 0),
                1 => Act::Write(PUBLISH, 1),
                2 => Act::Spin(self.done_line(), Pred::Eq(if split { s.version + 1 } else { 2 * s.version + 2 })),
                _ if self.p.results && s.index < self.workers => Act::Read(RESULTS + s.index),
                _ => Act::Mark,
            };
        }
        let id = c - 1;
        if s.version == self.rounds {
            return Act::Stop;
        }
        match s.pc {
            0 => Act::Spin(PUBLISH, Pred::Gt(if split { s.version } else { 2 * s.version })),
            1 => Act::Read(JOB),
            2 => Act::Work(self.p.work),
            3 => Act::Write(RESULTS + id, 0),
            4 => match self.design.kind {
                Kind::Rearm(_) => Act::Write(self.counter(s.ticket), s.amount),
                Kind::Atomic => Act::Write(self.counter(0), 1),
            },
            _ => Act::Write(self.done_line(), 1),
        }
    }

    /// Core `c` completed its action and observed `value`
    fn advance(&mut self, c: usize, value: usize) {
        let w = self.workers;
        let tree_size = self.tree_size;
        let kind = self.design.kind;
        let s = &mut self.cores[c];
        if c == PRODUCER {
            match s.pc {
                0 | 1 => s.pc += 1,
                2 => {
                    s.pc = 3;
                    s.index = 0;
                }
                _ if self.p.results && s.index < w => s.index += 1,
                _ => {
                    s.pc = 0;
                    s.version += 1;
                }
            }
            return;
        }
        let id = c - 1;
        let next_version = |s: &mut CoreState| {
            s.pc = 0;
            s.version += 1;
        };
        match s.pc {
            0..=2 => s.pc += 1,
            3 => {
                s.pc = 4;
                if let Kind::Rearm(cl) = kind {
                    s.ticket = tree_size + id / cl;
                    s.win_id = id / cl;
                    s.win_size = cl;
                    s.amount = 1;
                }
            }
            4 => {
                if value == w * (s.version + 1) {
                    s.pc = 5;
                    return;
                }
                match kind {
                    Kind::Atomic => next_version(s),
                    Kind::Rearm(cl) => {
                        let target = s.win_size.min(w - s.win_id * s.win_size);
                        if s.ticket == 0 || value != target * (s.version + 1) {
                            next_version(s);
                        } else {
                            s.amount = target;
                            s.ticket = (s.ticket - 1) / cl;
                            s.win_id /= cl;
                            s.win_size *= cl;
                        }
                    }
                }
            }
            _ => next_version(s),
        }
    }

    fn push(&mut self, time: f64, core: usize, effect: bool) {
        self.seq += 1;
        self.heap.push(Reverse((Time(time), self.seq, core, effect)));
    }

    fn rand(&mut self) -> u64 {
        let mut x = self.rng;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.rng = x;
        x
    }

    /// An exponentially distributed delay with the given mean
    fn exp(&mut self, mean: f64) -> f64 {
        if mean == 0.0 {
            return 0.0;
        }
        let unit = ((self.rand() >> 11) as f64 + 0.5) / (1u64 << 53) as f64;
        -mean * unit.ln()
    }

    /// Apply a read/spin/write of core `c` at `now`
    fn apply(&mut self, now: f64, c: usize, act: Act) {
        match act {
            Act::Read(l) => {
                self.lines[l].add_holder(c);
                let v = self.lines[l].value;
                self.advance(c, v);
                self.push(now, c, false);
            }
            Act::Spin(l, pred) => {
                self.lines[l].add_holder(c);
                let v = self.lines[l].value;
                let ok = match pred {
                    Pred::Gt(x) => v > x,
                    Pred::Eq(x) => v == x,
                };
                if ok {
                    let delay = if std::mem::take(&mut self.cores[c].woken) { self.exp(self.p.jitter) } else { 0.0 };
                    self.advance(c, v);
                    self.push(now + delay, c, false);
                } else {
                    self.lines[l].spinners.push(c);
                }
            }
            Act::Write(l, add) => {
                let line = &mut self.lines[l];
                line.make_exclusive(c);
                line.value += add;
                let v = line.value;
                let mut woken = std::mem::take(&mut line.spinners);
                // No core is favoured when several spinners race to pull
                for i in (1..woken.len()).rev() {
                    let j = (self.rand() % (i as u64 + 1)) as usize;
                    woken.swap(i, j);
                }
                for s in woken {
                    self.cores[s].woken = true;
                    self.push(now, s, false);
                }
                self.advance(c, v);
                self.push(now, c, false);
            }
            _ => unreachable!(),
        }
    }

    fn request(&mut self, now: f64, c: usize) {
        let act = self.act(c);
        let (l, write) = match act {
            Act::Stop => return,
            Act::Mark => {
                self.marks.push((now, self.counts));
                self.advance(c, 0);
                self.push(now, c, false);
                return;
            }
            Act::Work(w) => {
                self.advance(c, 0);
                self.push(now + w, c, false);
                return;
            }
            Act::Read(l) | Act::Spin(l, _) => (l, false),
            Act::Write(l, _) => (l, true),
        };
        let line = &self.lines[l];
        let class = CLASSES.iter().position(|(k, _)| *k == line.class).unwrap();
        let holds = line.holds(c);
        let cost = if !write {
            if holds {
                0.0
            } else {
                self.counts[class].pulls += 1;
                self.p.t
            }
        } else if holds && line.nholders == 1 {
            0.0
        } else if holds {
            self.counts[class].upgrades += 1;
            self.p.u
        } else {
            self.counts[class].rfos += 1;
            self.p.t
        };
        if cost == 0.0 {
            self.apply(now, c, act);
            return;
        }
        let line = &mut self.lines[l];
        let end = match (self.p.discipline, write) {
            (Discipline::Serial, _) | (Discipline::Parallel, true) => {
                let end = now.max(line.busy) + cost;
                line.busy = end;
                line.busy_write = end;
                end
            }
            (Discipline::Parallel, false) => {
                let end = now.max(line.busy_write) + cost;
                line.busy = line.busy.max(end);
                end
            }
        };
        self.pending[c] = Some(act);
        self.push(end, c, true);
    }

    /// Run and return (time per round, transfers per round per class)
    fn run(mut self, warmup: usize) -> (f64, [Counts; 4]) {
        for c in 0..self.cores.len() {
            self.push(0.0, c, false);
        }
        while let Some(Reverse((Time(now), _, c, effect))) = self.heap.pop() {
            if effect {
                let act = self.pending[c].take().unwrap();
                self.apply(now, c, act);
            } else {
                self.request(now, c);
            }
        }
        assert_eq!(self.marks.len(), self.rounds, "model deadlocked");
        let (t0, c0) = self.marks[warmup - 1];
        let (t1, c1) = self.marks[self.rounds - 1];
        let n = (self.rounds - warmup) as f64;
        let per = std::array::from_fn(|k| c1[k].sub(c0[k]));
        ((t1 - t0) / n, per)
    }
}

/// Mean time per round and transfers per round
fn simulate(design: Design, p: Params, workers: usize, rounds: usize) -> (f64, [f64; 12]) {
    let warmup = (rounds / 3).max(2);
    let (time, per) = Sim::new(design, p, workers, rounds).run(warmup);
    let n = (rounds - warmup) as f64;
    let mut flat = [0.0; 12];
    for (k, c) in per.iter().enumerate() {
        flat[3 * k] = c.pulls as f64 / n;
        flat[3 * k + 1] = c.rfos as f64 / n;
        flat[3 * k + 2] = c.upgrades as f64 / n;
    }
    (time, flat)
}

// ---------------------------------------------------------------------------
// Lower bound

/// Fastest time for information created on one core at time 0 to reach
/// `n` other cores, when a core informs a line by writing it (cost `w`, one
/// write at a time per core) and a core learns a line by pulling it (cost
/// `t`, one pull at a time per line under the serial discipline). Every
/// informed core and line keeps informing as early as it can, which is
/// optimal because being informed earlier never removes an option.
fn spread_time(n: usize, t: f64, w: f64, discipline: Discipline) -> f64 {
    if n == 0 {
        return 0.0;
    }
    if discipline == Discipline::Parallel || w == 0.0 {
        // One write, then everyone pulls it at once; or free writes to as
        // many lines as there are workers, each pulled by one of them
        return w + t;
    }
    // (free at, is a line)
    let mut free: BinaryHeap<Reverse<(Time, bool)>> = BinaryHeap::new();
    free.push(Reverse((Time(0.0), false)));
    let mut informed = 0;
    loop {
        let Reverse((Time(at), is_line)) = free.pop().unwrap();
        if is_line {
            // An uninformed core pulls this line
            let done = at + t;
            informed += 1;
            if informed == n {
                return done;
            }
            free.push(Reverse((Time(done), true)));
            free.push(Reverse((Time(done), false)));
        } else {
            // This core writes a fresh line
            let done = at + w;
            free.push(Reverse((Time(done), true)));
            free.push(Reverse((Time(done), false)));
        }
    }
}

/// Lower bound on the time per round of any barrier with this interface in
/// the model: the job must reach every worker, and every completion (and,
/// with `results`, every result line) must reach the producer.
///
/// * Dissemination takes at least `spread_time(W)`.
/// * Collection: a transfer merges what one core and one line know, so the
///   largest set of known completions at most doubles per `min(t, u)`; the
///   producer needs all `W`, so at least `ceil(log2 W) * min(t, u)` after
///   the first completion, plus its final pull.
/// * With `results`, the producer alone pulls `W` distinct lines, one at a
///   time, none before the first worker has written its result.
/// * Every worker has to notice the job by spinning, and the round waits for
///   the slowest: with i.i.d. exponential detection delays of mean `jitter`
///   that is `jitter * H_W` in expectation, whatever the design; the producer
///   then notices completion with one more such delay.
fn lower_bound(p: Params, workers: usize) -> f64 {
    let w = p.t.min(p.u);
    let dissem = spread_time(workers, p.t, w, p.discipline) + p.jitter * harmonic(workers);
    let first_done = w + p.t + p.work + w;
    let last_done = dissem + p.work + w;
    let merge = (workers as f64).log2().ceil() * w;
    let collect = (last_done + p.t).max(first_done + merge + p.t) + p.jitter;
    if p.results {
        collect.max(first_done + workers as f64 * p.t)
    } else {
        collect
    }
}

/// `H_n = 1 + 1/2 + .. + 1/n`, the expected maximum of `n` unit exponentials
fn harmonic(n: usize) -> f64 {
    (1..=n).map(|k| 1.0 / k as f64).sum()
}

// ---------------------------------------------------------------------------
// Closed form (serial discipline, steady state), checked against `simulate`

/// Tree depth above the leaves the crate walks in the worst case
fn walk_levels(workers: usize, c: usize) -> usize {
    let mut levels = 0;
    let mut n = workers.div_ceil(c);
    while n > 1 {
        n = n.div_ceil(c);
        levels += 1;
    }
    levels
}

/// Number of `fetch_add`s on counters per round, and how many of them are
/// RFOs: a counter that only one worker can ever write stays exclusive to it
fn counter_writes(design: Design, workers: usize) -> (usize, usize) {
    match design.kind {
        Kind::Atomic => (workers, if workers > 1 { workers } else { 0 }),
        Kind::Rearm(c) => {
            let base = workers.div_ceil(c);
            let tree = ticket_tree_alloc(base, c);
            let mut writes = vec![0usize; tree + base];
            let mut rfos = 0;
            let mut vals = vec![0usize; tree + base];
            for id in 0..workers {
                let (mut ticket, mut win_id, mut win_size, mut amount) = (tree + id / c, id / c, c, 1);
                loop {
                    let target = win_size.min(workers - win_id * win_size);
                    vals[ticket] += amount;
                    writes[ticket] += 1;
                    if target > 1 {
                        rfos += 1;
                    }
                    let new = vals[ticket];
                    if new == workers || ticket == 0 || new != target {
                        break;
                    }
                    amount = target;
                    ticket = (ticket - 1) / c;
                    win_id /= c;
                    win_size *= c;
                }
            }
            (writes.iter().sum(), rfos)
        }
    }
}

/// Transfer counts per round: (pulls, RFOs, upgrades). Upper estimates: a
/// spinner whose pull of the finish write is served after the next publish
/// sees both with one pull, which the simulation counts and this does not.
fn closed_counts(design: Design, p: Params, w: usize) -> (usize, usize, usize) {
    // Workers pull the publish; the producer and the W - 1 idle workers
    // spinning on the same probe pull the finish (split: only the producer)
    let signal_pulls = if design.split { w + 1 } else { 2 * w };
    let pulls = signal_pulls + w + if p.results { w } else { 0 };
    // With split, the finisher writes a done line it does not hold
    let rfos = counter_writes(design, w).1 + usize::from(design.split);
    // publish, job, finish (unless split), and each worker's result line
    // (shared with the producer only if it reads results)
    let upgrades = 2 + usize::from(!design.split) + if p.results { w } else { 0 };
    (pulls, rfos, upgrades)
}

/// Approximate time per round under the serial discipline:
///
/// ```text
/// T ≈ 2u                publish: job and probe writes (rearm/atomic)
///   + (W + 1) t         the W workers pull the probe one after another, then the job
///   + F + u'            work, result write (u' = u if results are read, else 0)
///   + (1 + h) t + u     the last worker's counter writes up h levels, then the finish write
///   + k t               the producer's pull of the finish, behind k spinners
///   + R W t             reading results (R = 1 or 0)
/// ```
///
/// `k` counts the pulls of the finish write the producer waits for. With
/// `+split` only the producer pulls it: `k = 1` (and the finish write is an
/// RFO, `t` instead of `u`). Otherwise the `W - 1` idle workers spinning on
/// the probe pull it too, in random order: the producer's own pull comes
/// after `(W + 1) / 2` of them on average, and if it does not read results
/// its next publish waits for the rest as well, `k = W`. `h` is 0 for
/// `atomic`; with one worker the counter writes are free.
fn closed_time(design: Design, p: Params, w: usize) -> f64 {
    let wf = w as f64;
    let h = match design.kind {
        Kind::Rearm(c) => walk_levels(w, c) as f64,
        Kind::Atomic => 0.0,
    };
    let counters = if w > 1 { 1.0 + h } else { 0.0 };
    let k = match (design.split, p.results) {
        (true, _) => 1.0,
        (false, true) => (wf + 1.0) / 2.0,
        (false, false) => wf,
    };
    let finish = if design.split { p.t } else { p.u };
    let r = if p.results { 1.0 } else { 0.0 };
    2.0 * p.u + (wf + 1.0) * p.t + p.work + r * p.u + counters * p.t + finish + k * p.t + r * wf * p.t
        + p.jitter * (harmonic(w) + 1.0)
}

/// Approximate time per round with parallel reads, when detection jitter
/// dominates line transfers (`jitter >> C t`) so that workers reach shared
/// counters one at a time and nobody queues:
///
/// ```text
/// T ≈ 2u + 2t           publish writes; every worker pulls probe and job at once
///   + jitter * H_W      the slowest of W spinners notices
///   + F + R u           work, result write
///   + (1 + h) t + u     the last worker's counter writes, the finish write
///   + t + jitter        the producer pulls and notices the finish
///   + R W t             reading results
/// ```
///
/// `None` for `atomic` (and for `rearm` with few, wide windows) where the
/// shared counter does queue: use the simulation.
fn closed_time_parallel(design: Design, p: Params, w: usize) -> Option<f64> {
    let h = match design.kind {
        Kind::Rearm(c) if w > 1 && c * 4 <= w => walk_levels(w, c) as f64,
        Kind::Rearm(_) | Kind::Atomic if w == 1 => 0.0,
        _ => return None,
    };
    let counters = if w > 1 { 1.0 + h } else { 0.0 };
    let finish = if design.split { p.t } else { p.u };
    let r = if p.results { 1.0 } else { 0.0 };
    Some(
        2.0 * p.u + 2.0 * p.t + p.jitter * harmonic(w) + p.work + r * p.u + counters * p.t + finish
            + p.t + p.jitter + r * w as f64 * p.t,
    )
}

// ---------------------------------------------------------------------------
// Commands

fn cmd_sim(args: &[String]) {
    let mut workers = vec![1, 3, 7, 15, 31, 63, 127, 255, 511, 767];
    let mut designs = vec!["rearm:4", "rearm:16", "atomic", "rearm:4+split", "atomic+split"]
        .into_iter()
        .map(|d| Design::parse(d).unwrap())
        .collect::<Vec<_>>();
    // Defaults: the best physically meaningful parallel fit to a sweep on a
    // Threadripper 3970X (see docs/contention-model.md)
    let mut p = Params { t: 21.3, u: 0.0, work: 0.0, jitter: 340.0, discipline: Discipline::Parallel, results: true };
    // The slowest of W exponential delays varies a lot between rounds: at
    // jitter 340 ns and W = 255 its standard deviation is ~440 ns, so 200
    // rounds leave about ±1.5% of sampling noise on the mean
    let mut rounds = 200;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut val = || it.next().unwrap_or_else(|| die(&format!("{a} needs a value"))).clone();
        match a.as_str() {
            "--workers" => workers = list(&val()),
            "--design" => {
                designs = val().split(',').map(|d| Design::parse(d).unwrap_or_else(|| die(&format!("bad design {d}")))).collect()
            }
            "--t" => p.t = num(&val()),
            "--u" => p.u = num(&val()),
            "--work" => p.work = num(&val()),
            "--jitter" => p.jitter = num(&val()),
            "--rounds" => rounds = num(&val()) as usize,
            "--discipline" => p.discipline = discipline(&val()),
            "--results" => p.results = results(&val()),
            _ => die(&format!("unknown argument {a}")),
        }
    }
    println!(
        "t = {} ns, u = {} ns, work = {} ns, jitter = {} ns, {:?} lines, results {}",
        p.t,
        p.u,
        p.work,
        p.jitter,
        p.discipline,
        if p.results { "read" } else { "skip" }
    );
    println!(
        "{:>5} {:<16} {:>10} {:>10} {:>10} {:>7}   transfers/round: pulls rfo upg by class (signal job result counter)",
        "W", "design", "model ns", "formula", "bound ns", "gap"
    );
    for &w in &workers {
        let lb = lower_bound(p, w);
        for &d in &designs {
            let (time, per) = simulate(d, p, w, rounds);
            let formula = match p.discipline {
                Discipline::Serial => format!("{:>10.0}", closed_time(d, p, w)),
                Discipline::Parallel => match closed_time_parallel(d, p, w) {
                    Some(x) => format!("{x:>10.0}"),
                    None => format!("{:>10}", "-"),
                },
            };
            let classes: Vec<String> =
                (0..4).map(|k| format!("{:.0}/{:.0}/{:.0}", per[3 * k], per[3 * k + 1], per[3 * k + 2])).collect();
            let (cp, cr, cu) = closed_counts(d, p, w);
            let (sp, sr, su) = (
                per.iter().step_by(3).sum::<f64>(),
                per.iter().skip(1).step_by(3).sum::<f64>(),
                per.iter().skip(2).step_by(3).sum::<f64>(),
            );
            // Totals: simulated, and the closed form's upper estimate
            let totals = format!("  total {:.0}/{:.0}/{:.0} (closed form ≤ {cp}/{cr}/{cu})", sp, sr, su);
            println!(
                "{w:>5} {:<16} {time:>10.0} {formula} {lb:>10.0} {:>6.2}x   {}{totals}",
                d.name(),
                time / lb,
                classes.join(" ")
            );
        }
    }
}

/// One measured row of benchmark output
struct Row {
    workers: usize,
    design: Design,
    results: bool,
    ns: f64,
}

fn parse_bench(text: &str) -> Vec<Row> {
    let mut rows = Vec::new();
    let (mut workers, mut work, mut results) = (0, u64::MAX, true);
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("workers = ") {
            workers = rest.split_whitespace().next().unwrap().parse().unwrap();
            work = rest.split("work = ").nth(1).and_then(|r| r.split_whitespace().next()).unwrap().parse().unwrap();
            results = !rest.contains("results skip");
            continue;
        }
        if work != 0 {
            // The model has no calibrated cost for the xorshift work
            continue;
        }
        let design = if let Some(rest) = line.strip_prefix("rearm C=") {
            let c = rest.split_whitespace().next().unwrap().parse().unwrap();
            Design { kind: Kind::Rearm(c), split: false }
        } else if line.starts_with("atomic ") {
            Design { kind: Kind::Atomic, split: false }
        } else {
            continue;
        };
        // The name may contain a space ("rearm C=4"); the median follows it
        let fields: Vec<&str> = line.split_whitespace().collect();
        let skip = if line.starts_with("rearm") { 2 } else { 1 };
        let ns = fields[skip].parse().unwrap();
        rows.push(Row { workers, design, results, ns });
    }
    rows
}

fn cmd_fit(args: &[String]) {
    let mut rows = Vec::new();
    let mut min_workers = 1;
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == "--min-workers" {
            min_workers = num(it.next().unwrap_or_else(|| die("--min-workers needs a value"))) as usize;
            continue;
        }
        rows.extend(parse_bench(&std::fs::read_to_string(a).unwrap_or_else(|e| die(&format!("{a}: {e}")))));
    }
    rows.retain(|r| r.workers >= min_workers);
    if rows.len() < 3 {
        die("need at least 3 rows with work = 0");
    }
    println!("{} rows (work = 0, rearm and atomic)", rows.len());

    struct Fit {
        discipline: Discipline,
        rho: f64,
        sigma: f64,
        t: f64,
        c0: f64,
        err: f64,
        model: Vec<f64>,
    }
    let params = |f: &Fit, results: bool| Params {
        t: f.t,
        u: f.rho * f.t,
        work: 0.0,
        jitter: f.sigma * f.t,
        discipline: f.discipline,
        results,
    };
    let mut fits = Vec::new();
    for discipline in [Discipline::Serial, Discipline::Parallel] {
        for sigma in [0.0, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0] {
            let mut best: Option<Fit> = None;
            for rho in [0.0, 0.25, 0.5, 1.0] {
                // With no work, time is homogeneous in (t, u, jitter): simulate
                // with t = 1 and fit the scale
                let model: Vec<f64> = rows
                    .iter()
                    .map(|r| {
                        let p = Params { t: 1.0, u: rho, work: 0.0, jitter: sigma, discipline, results: r.results };
                        simulate(r.design, p, r.workers, 90).0
                    })
                    .collect();
                // Weighted least squares for ns ≈ c0 + t * model, relative errors
                let (mut sw, mut sx, mut sy, mut sxx, mut sxy) = (0.0, 0.0, 0.0, 0.0, 0.0);
                for (r, &x) in rows.iter().zip(&model) {
                    let wt = 1.0 / (r.ns * r.ns);
                    sw += wt;
                    sx += wt * x;
                    sy += wt * r.ns;
                    sxx += wt * x * x;
                    sxy += wt * x * r.ns;
                }
                let mut t = (sw * sxy - sx * sy) / (sw * sxx - sx * sx);
                let mut c0 = (sy - t * sx) / sw;
                if c0 < 0.0 {
                    // A per-round constant cannot be negative: refit through 0
                    c0 = 0.0;
                    t = sxy / sxx;
                }
                if t <= 0.0 {
                    continue;
                }
                let err = (rows.iter().zip(&model).map(|(r, &x)| ((c0 + t * x - r.ns) / r.ns).powi(2)).sum::<f64>()
                    / rows.len() as f64)
                    .sqrt();
                if best.as_ref().is_none_or(|b| err < b.err) {
                    best = Some(Fit { discipline, rho, sigma, t, c0, err, model });
                }
            }
            fits.extend(best);
        }
    }
    if fits.is_empty() {
        die("no fit with positive costs");
    }

    println!("\nbest fit per discipline and jitter/t:");
    for f in &fits {
        println!(
            "  {:<8} jitter/t {:>4}: t = {:>6.1} ns, u = {:>6.1} ns, jitter = {:>6.0} ns, constant = {:>5.0} ns, rms error {:>5.1}%",
            format!("{:?}", f.discipline),
            f.sigma,
            f.t,
            f.rho * f.t,
            f.sigma * f.t,
            f.c0,
            100.0 * f.err
        );
    }
    let f = fits.iter().min_by(|a, b| a.err.total_cmp(&b.err)).unwrap();
    println!(
        "\nbest: {:?}, t = {:.1} ns, u = {:.1} ns, jitter = {:.0} ns, constant = {:.0} ns, rms error {:.1}%",
        f.discipline,
        f.t,
        f.rho * f.t,
        f.sigma * f.t,
        f.c0,
        100.0 * f.err
    );
    println!(
        "{:>5} {:<12} {:>8} {:>10} {:>10} {:>7} {:>10} {:>8}",
        "W", "design", "results", "measured", "model", "error", "bound", "gap"
    );
    for (r, &x) in rows.iter().zip(&f.model) {
        let pred = f.c0 + f.t * x;
        let lb = f.c0 + lower_bound(params(f, r.results), r.workers);
        println!(
            "{:>5} {:<12} {:>8} {:>10.0} {:>10.0} {:>6.1}% {:>10.0} {:>7.2}x",
            r.workers,
            r.design.name(),
            if r.results { "read" } else { "skip" },
            r.ns,
            pred,
            100.0 * (pred - r.ns) / r.ns,
            lb,
            r.ns / lb
        );
    }
    println!(
        "\nbound = constant + lower_bound; gap = measured / bound. Extrapolate with:\n  contention sim --t {:.1} --u {:.1} --jitter {:.0} --discipline {} --results read|skip",
        f.t,
        f.rho * f.t,
        f.sigma * f.t,
        match f.discipline {
            Discipline::Serial => "serial",
            Discipline::Parallel => "parallel",
        }
    );
}

/// Compare the crate's per-ticket write counts in traces with the model walk
fn cmd_check(args: &[String]) {
    for f in args {
        let text = std::fs::read_to_string(f).unwrap_or_else(|e| die(&format!("{f}: {e}")));
        let mut lines = text.lines();
        let cfg: Vec<usize> = lines
            .next()
            .and_then(|l| l.strip_prefix("config "))
            .unwrap_or_else(|| die(&format!("{f}: no config line")))
            .split_whitespace()
            .map(|x| x.parse().unwrap())
            .collect();
        let (w, c, count) = (cfg[0], cfg[1], cfg[2]);
        // (version, ticket) -> writes
        let mut seen: BTreeMap<(usize, usize), usize> = BTreeMap::new();
        let mut timeout = false;
        for l in lines {
            let ws: Vec<&str> = l.split_whitespace().collect();
            if ws.first() == Some(&"timeout") {
                timeout = true;
            }
            if ws.len() == 7 && ws[0] == "c" && ws[2] == "ticket" {
                *seen.entry((ws[3].parse().unwrap(), ws[4].parse().unwrap())).or_default() += 1;
            }
        }
        let design = Design { kind: Kind::Rearm(c), split: false };
        let expected = counter_writes(design, w).0;
        let mut bad = 0;
        for v in 0..count {
            let got: usize = seen.range((v, 0)..(v + 1, 0)).map(|(_, n)| n).sum();
            if got != expected {
                bad += 1;
            }
        }
        if timeout {
            println!("{f}: timeout trace, skipped");
        } else if bad == 0 {
            println!("{f}: ok, {expected} counter writes per round in all {count} rounds (W = {w}, C = {c})");
        } else {
            println!("{f}: {bad} of {count} rounds differ from the model's {expected} counter writes");
            std::process::exit(1);
        }
    }
}

fn list(s: &str) -> Vec<usize> {
    s.split(',').map(|x| x.trim().parse().unwrap_or_else(|_| die(&format!("bad number {x}")))).collect()
}

fn num(s: &str) -> f64 {
    s.parse().unwrap_or_else(|_| die(&format!("bad number {s}")))
}

fn discipline(s: &str) -> Discipline {
    match s {
        "serial" => Discipline::Serial,
        "parallel" => Discipline::Parallel,
        _ => die("--discipline takes serial or parallel"),
    }
}

fn results(s: &str) -> bool {
    match s {
        "read" => true,
        "skip" => false,
        _ => die("--results takes read or skip"),
    }
}

fn die(msg: &str) -> ! {
    eprintln!(
        "{msg}\nusage:\n  contention sim [--workers N,..] [--design rearm:C|atomic[+split],..] [--t NS] [--u NS] [--work NS] [--jitter NS] [--discipline serial|parallel] [--results read|skip] [--rounds N]\n  contention fit [--min-workers N] BENCH_OUTPUT..\n  contention check TRACE.."
    );
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("sim") => cmd_sim(&args[1..]),
        Some("fit") => cmd_fit(&args[1..]),
        Some("check") => cmd_check(&args[1..]),
        _ => die("expected a command"),
    }
}
