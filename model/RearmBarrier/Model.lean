import RearmBarrier.TreeModel

/-!
# The barrier as a transition system

Every thread of `RearmBarrier::producer` / `RearmBarrier::consumer` is a
small state machine; the shared memory is the `ticket_probe` counter, the
completion tree (`RearmBarrier.TreeModel`), the job slot and the per-worker
result slots. A `step` executes one action of one thread. Actions are

* an atomic read-modify-write (`fetch_add`) or the *successful* load of a
  spin loop — one action each, matching the atomics in `src/lib.rs`, or
* half of a non-atomic access: the job write, the result initialisation, the
  call of `func` and the call of `complete` each take two steps (begin / end)
  so that overlapping accesses are visible as states.

Loads inside a spin loop that do not satisfy the loop condition are not
modelled as steps: the thread is simply not enabled.

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

def ProducerPhase.toString : ProducerPhase → String
  | .beforeWrite v => s!"beforeWrite {v}"
  | .writing v => s!"writing {v}"
  | .publish v => s!"publish {v}"
  | .waiting v => s!"waiting {v}"
  | .beforeComplete v => s!"beforeComplete {v}"
  | .completing v => s!"completing {v}"
  | .done => "done"

instance : ToString ProducerPhase := ⟨ProducerPhase.toString⟩

structure State where
  probe : Nat
  tree : Tree
  /-- `some v` once job `v` is written; `none` while it is being overwritten -/
  job : Option Nat
  /-- `some v` once the slot holds the result of version `v` -/
  results : Array (Option Nat)
  producer : ProducerPhase
  consumers : Array ConsumerPhase
  /-- vector clock of every thread -/
  clocks : Array VC
  /-- release clock of `ticket_probe` -/
  probeRel : VC
  /-- happens-before bookkeeping of the job slot -/
  jobSlot : Slot
  /-- happens-before bookkeeping of every result slot -/
  resultSlots : Array Slot
deriving Repr, BEq, Hashable, Inhabited

/-- The barrier right after `new`, with the producer and every consumer
attached (locks taken) but before any of them has done anything. -/
def State.init (cfg : Config) : State :=
  { probe := 0
    tree := Tree.init cfg
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
def State.tick (s : State) (t : Nat) : State :=
  { s with clocks := s.clocks.modify t fun vc => vc.modify t (· + 1) }

/-- Thread `t` acquires the release clock of `ticket_probe`. -/
def State.acquireProbe (s : State) (t : Nat) : State :=
  { s with clocks := s.clocks.modify t (VC.join · s.probeRel) }

def State.releaseProbe (s : State) (t : Nat) : State :=
  { s with probeRel := s.probeRel.join s.clocks[t]! }

/-- Clock effects of a `fetch_add` on `ticket_probe` by thread `t`. -/
def State.rmwProbe (s : State) (t : Nat) (ord : MemOrd) : State :=
  let s := if ord.acquires then s.acquireProbe t else s
  if ord.releases then s.releaseProbe t else s

/-- A non-atomic access to the job slot or a result slot. -/
inductive Access
  | readJob
  | writeJob
  | writeResult (i : Nat)
  | writeAllResults
deriving Repr

/-- Write every result slot in turn (what `complete` does through its
`&mut [CacheLine<R>; WORKERS]`), stopping at the first race. -/
def writeAllSlots (t : Nat) (vc : VC) (race : Nat → String → String) :
    List (Slot × Nat) → Array Slot → Except String (Array Slot)
  | [], rs => pure rs
  | (slot, i) :: l, rs =>
    match slot.writeConflict vc with
    | some c => throw (race i c)
    | none => writeAllSlots t vc race l (rs.modify i (·.write t vc))

/-- Perform a non-atomic access by thread `t`, or report the data race. -/
def State.access (s : State) (t : Nat) (a : Access) : Except String State :=
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
    match writeAllSlots t vc (fun i c => race s!"result slot {i}" "write (inside complete)" c)
        s.resultSlots.toList.zipIdx s.resultSlots with
    | .ok rs => pure { s with resultSlots := rs }
    | .error m => throw m

/-! ## Steps -/

/-- Result of trying to run one action of one thread. -/
inductive Outcome
  /-- the thread is finished or its spin condition does not hold -/
  | blocked
  | step (s : State) (ev : Option Event)
  /-- the model itself cannot continue (e.g. an index out of bounds in the
  Rust code, which would panic) -/
  | fault (msg : String)
  /-- the step is a non-atomic access that races with an earlier one -/
  | race (msg : String)
deriving Inhabited

/-- Run a non-atomic access and continue with the state, or report the race. -/
def Outcome.accessing (s : State) (t : Nat) (a : Access) (k : State → Outcome) : Outcome :=
  match s.access t a with
  | .ok s => k s
  | .error m => .race m

def nextProducer (cfg : Config) (v : Nat) : ProducerPhase :=
  if v + 1 < cfg.count then .beforeWrite (v + 1) else .done

def nextConsumer (cfg : Config) (v : Nat) : ConsumerPhase :=
  if v + 1 < cfg.count then .waitReady (v + 1) else .done

def producerStep (cfg : Config) (s : State) : Outcome :=
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

def State.setConsumer (s : State) (id : Nat) (ph : ConsumerPhase) : State :=
  { s with consumers := s.consumers.setIfInBounds id ph }

def consumerStep (cfg : Config) (s : State) (id : Nat) : Outcome :=
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
      .step { s.setConsumer id (.walk v (Cursor.start cfg id)) with
                results := s.results.setIfInBounds id (some v) }
            (some (.func id v s.job))
    | .walk v cursor =>
      match s.tree.walk cfg cursor v s.clocks[t]! cfg.orderings.ticket with
      | .fault m => .fault s!"consumer {id}: {m}"
      | .ok tree vc rmw next =>
        let s := { s with tree, clocks := s.clocks.set! t vc }
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
def step (cfg : Config) (s : State) (t : Thread) : Outcome :=
  let raw := match t with
    | .producer => producerStep cfg s
    | .consumer id => consumerStep cfg s id
  match raw with
  | .step s' ev => .step (s'.tick (threadIndex t)) ev
  | o => o

def threads (cfg : Config) : List Thread :=
  .producer :: (List.range cfg.workers).map .consumer

/-- The threads that can take a step. -/
def enabled (cfg : Config) (s : State) : List Thread :=
  (threads cfg).filter fun t =>
    match step cfg s t with
    | .blocked => false
    | _ => true

def State.isFinal (s : State) : Bool :=
  s.producer == .done && s.consumers.all (· == .done)

def State.describe (cfg : Config) (s : State) : String :=
  let consumers := s.consumers.toList.zipIdx.map fun (ph, i) =>
    s!"  c {i}: {ph}, clock {s.clocks[i + 1]!}\n"
  s!"probe = {s.probe}, tickets = {s.tree.toCounters cfg} (tree (version, finished) = {s.tree.summary}), job = {optNat s.job}, results = {s.results.toList.map optNat}\n" ++
  s!"  p: {s.producer}, clock {s.clocks[0]!}\n" ++ String.join consumers

end RearmBarrier
