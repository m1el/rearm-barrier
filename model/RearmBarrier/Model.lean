import RearmBarrier.Tree

/-!
# The barrier as a transition system

Every thread of `RearmBarrier::producer` / `RearmBarrier::consumer` is a
small state machine; the shared memory is the `ticket_probe` counter, the
completion tickets, the job slot and the per-worker result slots. A `step`
executes one action of one thread. Actions are

* an atomic read-modify-write (`fetch_add`) or the *successful* load of a
  spin loop — one action each, matching the atomics in `src/lib.rs`, or
* half of a non-atomic access: the job write, the result initialisation, the
  call of `func` and the call of `complete` each take two steps (begin / end)
  so that overlapping accesses are visible as states.

Loads inside a spin loop that do not satisfy the loop condition are not
modelled as steps: the thread is simply not enabled.

## Ticket engines

The completion tickets are the only part of the state with a non-trivial
representation, and the only part whose update logic is interesting. They are
abstracted as an `Engine τ κ`: `τ` is the representation of all tickets and
`κ` a consumer's cursor into them during its completion walk. Two engines are
provided — `RearmBarrier.Flat` mirrors the crate's heap-indexed array, and
`RearmBarrier.TreeModel` is a structural tree — plus `RearmBarrier.Product`,
which runs two engines in lockstep and faults if they disagree.

## Memory model

The model interleaves the actions sequentially consistently. This is exact
for the counters: every shared counter is modified only by `fetch_add`, so
each location has a single modification order that every thread agrees on,
and the counters only grow, so a stale relaxed load can only delay a thread,
never let it through early. The write a successful spin-loop load reads from
is therefore the latest one in the interleaving.

On top of the interleaving the model tracks the C11 *happens-before* relation
with vector clocks, the way Miri's data race detector and loom do:

* every thread has a clock; every atomic location has a release clock;
* a `fetch_add` with a release ordering joins the thread's clock into the
  location's release clock, one with an acquire ordering joins the location's
  release clock into the thread's; since all writes are read-modify-writes,
  the release clock accumulates over the whole modification order (release
  sequences);
* a relaxed spin-loop load followed by `fence(Acquire)` acquires the release
  clock of the write it read; without the fence it acquires nothing;
* every non-atomic access to the job slot or a result slot must happen after
  every conflicting earlier access (FastTrack style: last write epoch plus a
  per-thread read clock), otherwise the step is a data race.

The orderings the crate uses are the defaults of `Orderings`; each can be
weakened to explore what would go wrong. By the C11 data-race-freedom
theorem, if every interleaving is race-free under this relation, the crate
has no non-SC executions, which is what justifies interleaving in the first
place.
-/

namespace RearmBarrier

/-- A memory ordering of an atomic read-modify-write. -/
inductive MemOrd
  | relaxed
  | acquire
  | release
  | acqRel
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

def MemOrd.acquires : MemOrd → Bool
  | .acquire | .acqRel => true
  | _ => false

def MemOrd.releases : MemOrd → Bool
  | .release | .acqRel => true
  | _ => false

/-- The orderings of the crate's atomics. The defaults are what `src/lib.rs`
uses; any of them can be weakened for an experiment. -/
structure Orderings where
  /-- producer: `ticket_probe.fetch_add(1, Release)` -/
  publish : MemOrd := .release
  /-- producer: `fence(Acquire)` after its spin loop -/
  producerFence : Bool := true
  /-- consumer: `fence(Acquire)` after its spin loop -/
  consumerFence : Bool := true
  /-- consumer: `tickets[ticket_id].fetch_add(merge_amount, AcqRel)` -/
  ticket : MemOrd := .acqRel
  /-- consumer: `ticket_probe.fetch_add(1, Release)` -/
  finish : MemOrd := .release
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

/-- The const generics `WORKERS`, `CLUSTER` and the `count` argument. -/
structure Config where
  workers : Nat
  cluster : Nat
  count : Nat
  orderings : Orderings := {}
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

namespace Config

/-- `RearmBarrier::VALID_CONFIG` -/
def valid (cfg : Config) : Bool := 1 ≤ cfg.workers && 2 ≤ cfg.cluster

def baseSize (cfg : Config) : Nat := RearmBarrier.baseSize cfg.workers cfg.cluster
def treeSize (cfg : Config) : Nat := ticketTreeSize cfg.workers cfg.cluster
def storage (cfg : Config) : Nat := ticketStorage cfg.workers cfg.cluster

end Config

/-- The program counter of the producer thread, per version `v`. -/
inductive ProducerPhase
  /-- about to build the job and overwrite the slot -/
  | beforeWrite (version : Nat)
  /-- inside `drop_in_place` / `write` of the job slot -/
  | writing (version : Nat)
  /-- about to `fetch_add` the probe -/
  | publish (version : Nat)
  /-- spinning until `probe == 2 * (v + 1)` -/
  | waiting (version : Nat)
  /-- about to call `complete` -/
  | beforeComplete (version : Nat)
  /-- inside `complete` (holding `&mut` to all result slots) -/
  | completing (version : Nat)
  | done
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

/-- The program counter of a consumer thread; `κ` is its cursor into the
tickets during the completion walk. -/
inductive ConsumerPhase (κ : Type)
  /-- has claimed its ID, has not yet written its initial state -/
  | start
  /-- writing the initial state into its result slot -/
  | initializing
  /-- spinning until `probe > 2 * v` -/
  | waitReady (version : Nat)
  /-- about to call `func` -/
  | beforeFunc (version : Nat)
  /-- inside `func` (holding `&T` and `&mut R`) -/
  | inFunc (version : Nat)
  /-- about to `fetch_add` the ticket under the cursor -/
  | walk (version : Nat) (cursor : κ)
  /-- about to `fetch_add` the probe: this consumer completed the version -/
  | finish (version : Nat)
  | done
deriving Repr, BEq, Hashable, Inhabited

def ConsumerPhase.mapCursor {κ κ' : Type} (f : κ → κ') : ConsumerPhase κ → ConsumerPhase κ'
  | .start => .start
  | .initializing => .initializing
  | .waitReady v => .waitReady v
  | .beforeFunc v => .beforeFunc v
  | .inFunc v => .inFunc v
  | .walk v c => .walk v (f c)
  | .finish v => .finish v
  | .done => .done

inductive Thread
  | producer
  | consumer (id : Nat)
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

def Thread.toString : Thread → String
  | .producer => "p"
  | .consumer id => s!"c {id}"

instance : ToString Thread := ⟨Thread.toString⟩

/-- Index of a thread in vector clocks: the producer is 0, consumer `i` is `i + 1`. -/
def threadIndex : Thread → Nat
  | .producer => 0
  | .consumer id => id + 1

def threadOf : Nat → Thread
  | 0 => .producer
  | i + 1 => .consumer i

/-! ## Happens-before bookkeeping -/

/-- A vector clock, one entry per thread (see `threadIndex`). -/
abbrev VC := Array Nat

def VC.zero (n : Nat) : VC := Array.replicate n 0

def VC.join (a b : VC) : VC := a.zipWith max b

/-- `a ≤ b` pointwise -/
def VC.le (a b : VC) : Bool := (a.zip b).all fun (x, y) => x ≤ y

/-- Happens-before bookkeeping for a non-atomic location, FastTrack style. -/
structure Slot where
  /-- thread and clock of the last write -/
  lastWrite : Option (Nat × Nat) := none
  /-- for every thread, its own clock at its last read since the last write (0: none) -/
  reads : VC
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

def Slot.init (n : Nat) : Slot := { reads := VC.zero n }

/-- The earlier access that a read by a thread with clock `vc` is not ordered
after, if any. -/
def Slot.readConflict (s : Slot) (vc : VC) : Option String :=
  match s.lastWrite with
  | some (tw, c) => if c > vc[tw]! then some s!"the write by `{threadOf tw}` at clock {c}" else none
  | none => none

/-- The earlier access that a write by a thread with clock `vc` is not ordered
after, if any. -/
def Slot.writeConflict (s : Slot) (vc : VC) : Option String :=
  match s.readConflict vc with
  | some m => some m
  | none =>
    (s.reads.toList.zipIdx.find? fun (r, i) => r > vc[i]!).map fun (r, i) =>
      s!"the read by `{threadOf i}` at clock {r}"

def Slot.read (s : Slot) (t : Nat) (vc : VC) : Slot :=
  { s with reads := s.reads.set! t vc[t]! }

def Slot.write (s : Slot) (t : Nat) (vc : VC) : Slot :=
  { lastWrite := some (t, vc[t]!), reads := VC.zero s.reads.size }

/-! ## Events -/

/-- The observable actions; these are exactly the lines of a trace file. -/
inductive Event
  /-- producer finished writing job `version` -/
  | jobWrite (version : Nat)
  /-- producer `fetch_add(1)` on the probe, which returned `old` -/
  | publish (version old : Nat)
  /-- producer left its spin loop after loading `value` -/
  | observeDone (version value : Nat)
  /-- producer finished `complete`, having seen these results -/
  | complete (version : Nat) (results : List (Option Nat))
  /-- consumer `id` wrote its initial state -/
  | init (id : Nat)
  /-- consumer `id` left its spin loop after loading `value` -/
  | observeReady (id version value : Nat)
  /-- consumer `id` finished `func`, having seen `job` -/
  | func (id version : Nat) (job : Option Nat)
  /-- consumer `id` did `fetch_add(amount)` on `ticketId`, which returned `old` -/
  | ticket (id version ticketId amount old : Nat)
  /-- consumer `id` `fetch_add(1)` on the probe, which returned `old` -/
  | finish (id version old : Nat)
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

/-! ## Ticket engines -/

/-- What one `fetch_add` on a ticket looked like: the heap index of the
ticket, the amount added and the value returned. -/
structure Rmw where
  ticketId : Nat
  amount : Nat
  old : Nat
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString Rmw := ⟨fun r => s!"ticket {r.ticketId} += {r.amount} (was {r.old})"⟩

/-- What a consumer does after a `fetch_add` on a ticket. -/
inductive Next (κ : Type)
  /-- `new_val == WORKERS * (version + 1)`: bump the probe -/
  | finished
  /-- the root was reached, or the window is not full yet: this version is done -/
  | stop
  /-- the window filled: continue at the parent -/
  | continue (cursor : κ)
deriving Repr, BEq, Hashable, Inhabited

def Next.kind {κ : Type} : Next κ → String
  | .finished => "finished"
  | .stop => "stop"
  | .continue _ => "continue"

inductive EngineResult (τ κ : Type)
  /-- the tickets after the `fetch_add`, the thread's clock after the
  acquire part of the ordering, the operation performed, and what follows -/
  | ok (tickets : τ) (vc : VC) (rmw : Rmw) (next : Next κ)
  /-- the Rust code would panic (an index out of bounds) -/
  | fault (msg : String)
deriving Inhabited

/-- A representation `τ` of the completion tickets together with the logic of
one iteration of the consumer's walk, using cursor type `κ`. -/
structure Engine (τ κ : Type) where
  /-- the tickets of a fresh barrier -/
  init : Config → τ
  /-- the cursor with which consumer `id` starts its walk -/
  start : Config → Nat → κ
  /-- one `fetch_add(merge_amount)` by a consumer at version `version` whose
  clock is `vc`, with the given ordering -/
  step : Config → τ → κ → (version : Nat) → VC → MemOrd → EngineResult τ κ
  /-- invariants of the tickets, given every consumer's phase (a walking
  consumer carries a contribution that is in flight) -/
  violations : Config → τ → Array (ConsumerPhase κ) → List String
  /-- one-line summary of the tickets, for reports -/
  summary : τ → String

/-! ## State -/

structure State (τ κ : Type) where
  probe : Nat
  tickets : τ
  /-- `some v` once job `v` is written; `none` while it is being overwritten -/
  job : Option Nat
  /-- `some v` once the slot holds the result of version `v` -/
  results : Array (Option Nat)
  producer : ProducerPhase
  consumers : Array (ConsumerPhase κ)
  /-- vector clock of every thread -/
  clocks : Array VC
  /-- release clock of `ticket_probe` -/
  probeRel : VC
  /-- happens-before bookkeeping of the job slot -/
  jobSlot : Slot
  /-- happens-before bookkeeping of every result slot -/
  resultSlots : Array Slot
deriving Repr, BEq, Hashable, Inhabited

variable {τ κ : Type}

/-- The barrier right after `new`, with the producer and every consumer
attached (locks taken) but before any of them has done anything. -/
def State.init (E : Engine τ κ) (cfg : Config) : State τ κ :=
  { probe := 0
    tickets := E.init cfg
    job := none
    results := Array.replicate cfg.workers none
    producer := if cfg.count = 0 then .done else .beforeWrite 0
    consumers := Array.replicate cfg.workers .start
    clocks := Array.replicate (cfg.workers + 1) (VC.zero (cfg.workers + 1))
    probeRel := VC.zero (cfg.workers + 1)
    jobSlot := Slot.init (cfg.workers + 1)
    resultSlots := Array.replicate cfg.workers (Slot.init (cfg.workers + 1)) }

/-! ### Clock operations -/

/-- Advance thread `t`'s own clock: every step is a new epoch. -/
def State.tick (s : State τ κ) (t : Nat) : State τ κ :=
  { s with clocks := s.clocks.modify t fun vc => vc.modify t (· + 1) }

/-- Thread `t` acquires the release clock of `ticket_probe`. -/
def State.acquireProbe (s : State τ κ) (t : Nat) : State τ κ :=
  { s with clocks := s.clocks.modify t (VC.join · s.probeRel) }

def State.releaseProbe (s : State τ κ) (t : Nat) : State τ κ :=
  { s with probeRel := s.probeRel.join s.clocks[t]! }

/-- Clock effects of a `fetch_add` on `ticket_probe` by thread `t`. -/
def State.rmwProbe (s : State τ κ) (t : Nat) (ord : MemOrd) : State τ κ :=
  let s := if ord.acquires then s.acquireProbe t else s
  if ord.releases then s.releaseProbe t else s

/-- Clock effects of a `fetch_add` on a ticket whose release clock is `rel`,
by a thread with clock `vc`: the thread's new clock and the ticket's new
release clock. -/
def rmwTicketClocks (vc rel : VC) (ord : MemOrd) : VC × VC :=
  let vc := if ord.acquires then vc.join rel else vc
  let rel := if ord.releases then rel.join vc else rel
  (vc, rel)

/-- A non-atomic access to the job slot or a result slot. -/
inductive Access
  | readJob
  | writeJob
  | writeResult (i : Nat)
  | writeAllResults
deriving Repr

/-- Perform a non-atomic access by thread `t`, or report the data race. -/
def State.access (s : State τ κ) (t : Nat) (a : Access) : Except String (State τ κ) :=
  let vc := s.clocks[t]!
  let race (loc : String) (what : String) (conflict : String) :=
    s!"data race on {loc}: the {what} by `{threadOf t}` is not ordered after {conflict}"
  match a with
  | .readJob =>
    match s.jobSlot.readConflict vc with
    | some c => throw (race "the job slot" "read" c)
    | none => pure { s with jobSlot := s.jobSlot.read t vc }
  | .writeJob =>
    match s.jobSlot.writeConflict vc with
    | some c => throw (race "the job slot" "write" c)
    | none => pure { s with jobSlot := s.jobSlot.write t vc }
  | .writeResult i =>
    match s.resultSlots[i]! |>.writeConflict vc with
    | some c => throw (race s!"result slot {i}" "write" c)
    | none => pure { s with resultSlots := s.resultSlots.modify i (·.write t vc) }
  | .writeAllResults =>
    s.resultSlots.toList.zipIdx.foldlM (init := s) fun s (slot, i) =>
      match slot.writeConflict vc with
      | some c => throw (race s!"result slot {i}" "write (inside complete)" c)
      | none => pure { s with resultSlots := s.resultSlots.modify i (·.write t vc) }

/-! ## Steps -/

/-- Result of trying to run one action of one thread. -/
inductive Outcome (τ κ : Type)
  /-- the thread is finished or its spin condition does not hold -/
  | blocked
  | step (s : State τ κ) (ev : Option Event)
  /-- the model itself cannot continue (e.g. an index out of bounds in the
  Rust code, which would panic) -/
  | fault (msg : String)
  /-- the step is a non-atomic access that races with an earlier one -/
  | race (msg : String)
deriving Inhabited

/-- Run a non-atomic access and continue with the state, or report the race. -/
def Outcome.accessing (s : State τ κ) (t : Nat) (a : Access)
    (k : State τ κ → Outcome τ κ) : Outcome τ κ :=
  match s.access t a with
  | .ok s => k s
  | .error m => .race m

def nextProducer (cfg : Config) (v : Nat) : ProducerPhase :=
  if v + 1 < cfg.count then .beforeWrite (v + 1) else .done

def nextConsumer (cfg : Config) (v : Nat) : ConsumerPhase κ :=
  if v + 1 < cfg.count then .waitReady (v + 1) else .done

def producerStep (cfg : Config) (s : State τ κ) : Outcome τ κ :=
  let t := threadIndex .producer
  match s.producer with
  | .beforeWrite v =>
    .accessing s t .writeJob fun s =>
      .step { s with producer := .writing v, job := none } none
  | .writing v =>
    .step { s with producer := .publish v, job := some v } (some (.jobWrite v))
  | .publish v =>
    .step { s.rmwProbe t cfg.orderings.publish with producer := .waiting v, probe := s.probe + 1 }
          (some (.publish v s.probe))
  | .waiting v =>
    if s.probe = (v + 1) * 2 then
      let s := if cfg.orderings.producerFence then s.acquireProbe t else s
      .step { s with producer := .beforeComplete v } (some (.observeDone v s.probe))
    else
      .blocked
  | .beforeComplete v =>
    .accessing s t .writeAllResults fun s =>
      .step { s with producer := .completing v } none
  | .completing v =>
    .step { s with producer := nextProducer cfg v } (some (.complete v s.results.toList))
  | .done => .blocked

def State.setConsumer (s : State τ κ) (id : Nat) (ph : ConsumerPhase κ) : State τ κ :=
  { s with consumers := s.consumers.setIfInBounds id ph }

def consumerStep (E : Engine τ κ) (cfg : Config) (s : State τ κ) (id : Nat) : Outcome τ κ :=
  let t := threadIndex (.consumer id)
  match s.consumers[id]? with
  | none => .fault s!"consumer {id} does not exist"
  | some ph =>
    match ph with
    | .start =>
      .accessing s t (.writeResult id) fun s =>
        .step (s.setConsumer id .initializing) none
    | .initializing =>
      let next := if cfg.count = 0 then .done else .waitReady 0
      .step { s.setConsumer id next with results := s.results.setIfInBounds id none } (some (.init id))
    | .waitReady v =>
      if s.probe > v * 2 then
        let s := if cfg.orderings.consumerFence then s.acquireProbe t else s
        .step (s.setConsumer id (.beforeFunc v)) (some (.observeReady id v s.probe))
      else
        .blocked
    | .beforeFunc v =>
      .accessing s t .readJob fun s =>
        .accessing s t (.writeResult id) fun s =>
          .step (s.setConsumer id (.inFunc v)) none
    | .inFunc v =>
      .step { s.setConsumer id (.walk v (E.start cfg id)) with
                results := s.results.setIfInBounds id (some v) }
            (some (.func id v s.job))
    | .walk v cursor =>
      match E.step cfg s.tickets cursor v s.clocks[t]! cfg.orderings.ticket with
      | .fault m => .fault s!"consumer {id}: {m}"
      | .ok tickets vc rmw next =>
        let s := { s with tickets, clocks := s.clocks.set! t vc }
        let ph := match next with
          | .finished => .finish v
          | .stop => nextConsumer cfg v
          | .continue cursor => .walk v cursor
        .step (s.setConsumer id ph) (some (.ticket id v rmw.ticketId rmw.amount rmw.old))
    | .finish v =>
      .step { (s.rmwProbe t cfg.orderings.finish).setConsumer id (nextConsumer cfg v) with
                probe := s.probe + 1 }
            (some (.finish id v s.probe))
    | .done => .blocked

/-- One action of thread `t`. Every step is a new epoch of the thread's clock. -/
def step (E : Engine τ κ) (cfg : Config) (s : State τ κ) (t : Thread) : Outcome τ κ :=
  let raw := match t with
    | .producer => producerStep cfg s
    | .consumer id => consumerStep E cfg s id
  match raw with
  | .step s' ev => .step (s'.tick (threadIndex t)) ev
  | o => o

def threads (cfg : Config) : List Thread :=
  .producer :: (List.range cfg.workers).map .consumer

/-- The threads that can take a step. -/
def enabled (E : Engine τ κ) (cfg : Config) (s : State τ κ) : List Thread :=
  (threads cfg).filter fun t =>
    match step E cfg s t with
    | .blocked => false
    | _ => true

def State.isFinal [BEq κ] (s : State τ κ) : Bool :=
  s.producer == .done && s.consumers.all (· == .done)

/-! ## Printing -/

def optNat : Option Nat → String
  | none => "-"
  | some n => toString n

/-- The trace-file syntax of an event (without the thread prefix). -/
def Event.toString : Event → String
  | .jobWrite v => s!"write {v}"
  | .publish v old => s!"publish {v} {old}"
  | .observeDone v value => s!"wait {v} {value}"
  | .complete v rs => s!"complete {v}" ++ String.join (rs.map fun r => " " ++ optNat r)
  | .init _ => "init"
  | .observeReady _ v value => s!"ready {v} {value}"
  | .func _ v job => s!"func {v} {optNat job}"
  | .ticket _ v t amount old => s!"ticket {v} {t} {amount} {old}"
  | .finish _ v old => s!"finish {v} {old}"

instance : ToString Event := ⟨Event.toString⟩

/-- The thread an event belongs to. -/
def Event.thread : Event → Thread
  | .jobWrite _ | .publish .. | .observeDone .. | .complete .. => .producer
  | .init id | .observeReady id .. | .func id .. | .ticket id .. | .finish id .. => .consumer id

/-- Whether an event modifies a shared atomic. -/
def Event.mutates : Event → Bool
  | .publish .. | .ticket .. | .finish .. => true
  | _ => false

def ProducerPhase.toString : ProducerPhase → String
  | .beforeWrite v => s!"beforeWrite {v}"
  | .writing v => s!"writing {v}"
  | .publish v => s!"publish {v}"
  | .waiting v => s!"waiting {v}"
  | .beforeComplete v => s!"beforeComplete {v}"
  | .completing v => s!"completing {v}"
  | .done => "done"

instance : ToString ProducerPhase := ⟨ProducerPhase.toString⟩

def ConsumerPhase.toString [ToString κ] : ConsumerPhase κ → String
  | .start => "start"
  | .initializing => "initializing"
  | .waitReady v => s!"waitReady {v}"
  | .beforeFunc v => s!"beforeFunc {v}"
  | .inFunc v => s!"inFunc {v}"
  | .walk v c => s!"walk {v} ({c})"
  | .finish v => s!"finish {v}"
  | .done => "done"

instance [ToString κ] : ToString (ConsumerPhase κ) := ⟨ConsumerPhase.toString⟩

def State.describe [ToString κ] (E : Engine τ κ) (s : State τ κ) : String :=
  let consumers := s.consumers.toList.zipIdx.map fun (ph, i) =>
    s!"  c {i}: {ph}, clock {s.clocks[i + 1]!}\n"
  s!"probe = {s.probe}, {E.summary s.tickets}, job = {optNat s.job}, results = {s.results.toList.map optNat}\n" ++
  s!"  p: {s.producer}, clock {s.clocks[0]!}\n" ++ String.join consumers

end RearmBarrier
