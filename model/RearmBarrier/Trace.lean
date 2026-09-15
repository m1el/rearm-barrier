import Std.Data.HashMap
import RearmBarrier.Spec

/-!
# Trace files and replay

A trace file is produced by the crate's instrumentation (`examples/trace.rs`,
feature `trace`). It starts with a `config WORKERS CLUSTER COUNT` line, then
one event per line, prefixed with the thread (`p` or `c ID`), in the syntax of
`Event.toString`. Only the order of the lines *of each thread* matters. A
final `timeout` line marks a partial trace: the crate hung and these are the
events recorded before the harness gave up.

`replay` decides whether the per-thread event sequences are a possible
execution of the model, and checks the invariants along the way. It builds a
global interleaving greedily: repeatedly pick a thread whose next event the
model can produce right now, preferring events that do not modify a shared
atomic. This is complete, i.e. it never gets stuck on a trace that has a
consistent interleaving:

* events that do not touch a shared counter are always enabled and commute
  with everything else;
* a spin-loop exit that observed value `x` must happen while the counter is
  `x`, i.e. before the next `fetch_add` on it, so it is safe to run first;
* two `fetch_add`s on the same counter that both observed the same old value
  cannot both be in the trace.
-/

namespace RearmBarrier

structure Trace where
  cfg : Config
  events : List Event
  /-- the crate timed out after these events -/
  timedOut : Bool := false
deriving Repr, Inhabited

/-! ## Parsing -/

private def parseNat (w : String) : Except String Nat :=
  match w.toNat? with
  | some n => .ok n
  | none => .error s!"expected a number, got `{w}`"

private def parseOptNat (w : String) : Except String (Option Nat) :=
  if w == "-" then .ok none else (some ·) <$> parseNat w

private def parseProducerEvent : List String → Except String Event
  | ["write", v] => .jobWrite <$> parseNat v
  | ["publish", v, old] => .publish <$> parseNat v <*> parseNat old
  | ["wait", v, value] => .observeDone <$> parseNat v <*> parseNat value
  | "complete" :: v :: rs => .complete <$> parseNat v <*> rs.mapM parseOptNat
  | ws => .error s!"unknown producer event `{" ".intercalate ws}`"

private def parseConsumerEvent (id : Nat) : List String → Except String Event
  | ["init"] => .ok (.init id)
  | ["ready", v, value] => .observeReady id <$> parseNat v <*> parseNat value
  | ["func", v, job] => .func id <$> parseNat v <*> parseOptNat job
  | ["ticket", v, t, amount, old] =>
    .ticket id <$> parseNat v <*> parseNat t <*> parseNat amount <*> parseNat old
  | ["finish", v, old] => .finish id <$> parseNat v <*> parseNat old
  | ws => .error s!"unknown consumer event `{" ".intercalate ws}`"

private def words (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")

/-- Parse one event line. -/
def parseEvent (line : String) : Except String Event :=
  match words line with
  | "p" :: rest => parseProducerEvent rest
  | "c" :: id :: rest => do parseConsumerEvent (← parseNat id) rest
  | _ => .error s!"cannot parse `{line}`"

def parseTrace (text : String) : Except String Trace := do
  let lines := (text.splitOn "\n").map (·.trimAscii.toString) |>.filter fun l => l ≠ "" && !l.startsWith "#"
  match lines with
  | [] => throw "empty trace"
  | header :: rest =>
    let cfg ← match words header with
      | ["config", w, c, n] => do
        pure { workers := ← parseNat w, cluster := ← parseNat c, count := ← parseNat n : Config }
      | _ => throw s!"expected `config WORKERS CLUSTER COUNT`, got `{header}`"
    let timedOut := rest.contains "timeout"
    let events ← (rest.zipIdx.filter fun (l, _) => l ≠ "timeout").mapM fun (l, i) =>
      match parseEvent l with
      | .ok e => pure e
      | .error m => throw s!"line {i + 2}: {m}"
    pure { cfg, events, timedOut }

/-! ## Replay -/

structure Replay where
  cfg : Config
  timedOut : Bool
  state : State
  /-- remaining events per thread, indexed by `threadIndex` -/
  queues : Array (List Event)
  /-- the interleaving chosen so far -/
  history : Array (Thread × Option Event)
  replayed : Nat
deriving Inhabited

/-- Two events with the same shape and location but different observed values.
Such a pair means "the trace event may still become possible later". -/
private def sameOp : Event → Event → Bool
  | .publish v _, .publish v' _ => v == v'
  | .observeDone v _, .observeDone v' _ => v == v'
  | .observeReady i v _, .observeReady i' v' _ => i == i' && v == v'
  | .ticket i v t a _, .ticket i' v' t' a' _ => i == i' && v == v' && t == t' && a == a'
  | .finish i v _, .finish i' v' _ => i == i' && v == v'
  | _, _ => false

/-- Whether the spin loop the thread is in would exit after loading `value`. -/
private def spinAccepts (s : State) (t : Thread) : Option (Nat → Bool) :=
  match t with
  | .producer =>
    match s.producer with
    | .waiting v => some fun value => value == (v + 1) * 2
    | _ => none
  | .consumer id =>
    match s.consumers[id]? with
    | some (.waitReady v) => some fun value => value > v * 2
    | _ => none

private def observedValue : Event → Option Nat
  | .observeDone _ value => some value
  | .observeReady _ _ value => some value
  | _ => none

inductive Attempt
  /-- the thread has no events left, or its next event is not possible yet -/
  | notNow (r : Replay)
  /-- one trace event was consumed -/
  | consumed (r : Replay)
  | mismatch (msg : String)
deriving Inhabited

private def describeState (r : Replay) : String :=
  s!"after {r.replayed} events, model state:\n{r.state.describe}"

private def commit (r : Replay) (t : Thread) (s : State) (ev : Option Event) : Replay :=
  { r with state := s, history := r.history.push (t, ev) }

/-- Run the silent steps of `t` and then try to match its next trace event. -/
private partial def tryThread (r : Replay) (t : Thread) : Attempt :=
  let idx := threadIndex t
  match r.queues[idx]? with
  | none | some [] => .notNow r
  | some (target :: rest) =>
    match step r.cfg r.state t with
    | .fault m => .mismatch s!"model fault on thread `{t}`: {m}\n{describeState r}"
    | .race m => .mismatch s!"thread `{t}`: {m}\n{describeState r}"
    | .step s none => tryThread (commit r t s none) t
    | .step s (some ev) =>
      if ev == target then
        .consumed { commit r t s (some ev) with
                    queues := r.queues.set! idx rest, replayed := r.replayed + 1 }
      else if sameOp ev target then
        .notNow r
      else
        .mismatch s!"thread `{t}`: the trace says `{target}` but the model does `{ev}`\n{describeState r}"
    | .blocked =>
      match observedValue target, spinAccepts r.state t with
      | some value, some accepts =>
        if !accepts value then
          .mismatch s!"thread `{t}`: the trace leaves a spin loop after observing `{target}`, which the model would keep spinning on\n{describeState r}"
        else
          -- the counter has not reached `value` yet (or has passed it)
          .notNow r
      | _, _ =>
        .mismatch s!"thread `{t}`: the trace continues with `{target}` but the model thread is blocked\n{describeState r}"

/-- Try every thread once; non-mutating events first. -/
private def sweep (r : Replay) : Attempt := Id.run do
  let ts := threads r.cfg
  let order := ts.filter (fun t => nextMutates r t == some false) ++
               ts.filter (fun t => nextMutates r t != some false)
  let mut cur := r
  for t in order do
    match tryThread cur t with
    | .consumed r' => return .consumed r'
    | .notNow r' => cur := r'
    | .mismatch m => return .mismatch m
  return .notNow cur
where
  nextMutates (r : Replay) (t : Thread) : Option Bool :=
    match r.queues[threadIndex t]? with
    | some (e :: _) => some e.mutates
    | _ => none

private def stuckReport (r : Replay) : String := Id.run do
  let mut msg := "no interleaving continues the trace:\n"
  if r.timedOut then
    msg := msg ++ "  (the trace is a timeout snapshot: an operation performed just before the snapshot may be missing)\n"
  for t in threads r.cfg do
    match r.queues[threadIndex t]? with
    | some (e :: _) => msg := msg ++ s!"  thread `{t}` wants `{e}`\n"
    | _ => msg := msg ++ s!"  thread `{t}` is finished\n"
  return msg ++ describeState r

structure ReplayResult where
  replayed : Nat
  history : Array (Thread × Option Event)
  final : State

private partial def run (r : Replay) : Except String ReplayResult :=
  if let msg :: _ := violations r.cfg r.state then
    throw s!"invariant violated: {msg}\n{describeState r}"
  else if r.queues.all (·.isEmpty) then
    if r.timedOut then
      -- every recorded event is an action of the model; is what follows a deadlock?
      match enabled r.cfg r.state with
      | [] =>
        if r.state.isFinal then
          throw s!"the trace is marked `timeout` but every thread has finished in the model\n{describeState r}"
        else
          throw s!"the crate hung, and the model confirms the deadlock: no thread is enabled\n{describeState r}"
      | ts =>
        throw s!"the crate hung, but the model can still make progress with {ts}: either the timeout was too short or the crate lost a wakeup\n{describeState r}"
    else
      match finalViolations r.cfg r.state with
      | msg :: _ => throw s!"at the end of the trace: {msg}\n{describeState r}"
      | [] => pure { replayed := r.replayed, history := r.history, final := r.state }
  else
    match sweep r with
    | .consumed r' => run r'
    | .notNow r' => throw (stuckReport r')
    | .mismatch m => throw m

/-- Check that a trace is an execution of the model satisfying every invariant. -/
def replay (tr : Trace) : Except String ReplayResult := do
  if !tr.cfg.valid then
    throw s!"invalid configuration: WORKERS = {tr.cfg.workers}, CLUSTER = {tr.cfg.cluster}"
  let n := tr.cfg.workers + 1
  let queues := tr.events.foldl (init := Array.replicate n ([] : List Event)) fun qs e =>
    let i := threadIndex e.thread
    qs.modify i (e :: ·)
  let queues := queues.map List.reverse
  for e in tr.events do
    if threadIndex e.thread ≥ n then
      throw s!"event `{e}` belongs to a consumer outside 0..{tr.cfg.workers}"
  run { cfg := tr.cfg, timedOut := tr.timedOut, state := State.init tr.cfg, queues,
        history := #[], replayed := 0 }

/-! ## Random simulation

Produces traces in the file syntax from the model itself, for round-trip
testing of `replay` and for eyeballing executions. -/

private def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- Run the model under a pseudo-random schedule. Returns the trace lines and
the final state, or the first problem found. -/
partial def simulate (cfg : Config) (seed : UInt64) : Except String (List String × State) :=
  go (State.init cfg) (if seed == 0 then 0x9E3779B97F4A7C15 else seed) [] 0
where
  go (s : State) (rng : UInt64) (acc : List String) (steps : Nat) : Except String (List String × State) := do
    if let msg :: _ := violations cfg s then
      throw s!"invariant violated: {msg}\n{s.describe}"
    match enabled cfg s with
    | [] =>
      match finalViolations cfg s with
      | msg :: _ => throw s!"{msg}\n{s.describe}"
      | [] => pure (acc.reverse, s)
    | ts =>
      let rng := xorshift rng
      let t := ts[(rng.toNat % ts.length)]!
      match step cfg s t with
      | .step s' ev =>
        let acc := match ev with
          | some e => s!"{t} {e}" :: acc
          | none => acc
        go s' rng acc (steps + 1)
      | .fault m => throw s!"model fault on `{t}`: {m}\n{s.describe}"
      | .race m => throw s!"{m}\n{s.describe}"
      | .blocked => throw "enabled thread is blocked"

end RearmBarrier
