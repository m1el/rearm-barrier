import RearmBarrier.Tree

/-!
# The barrier as a transition system

Every thread of `RearmBarrier::producer` / `RearmBarrier::consumer` is a
small state machine; the shared memory is the `ticket_probe` counter, the
`tickets` array, the job slot and the per-worker result slots. A `step`
executes one action of one thread. Actions are

* an atomic read-modify-write (`fetch_add`) or the *successful* load of a
  spin loop — one action each, matching the atomics in `src/lib.rs`, or
* half of a non-atomic access: the job write, the result initialisation, the
  call of `func` and the call of `complete` each take two steps (begin / end)
  so that overlapping accesses are visible as states.

Loads inside a spin loop that do not satisfy the loop condition are not
modelled as steps: the thread is simply not enabled.

## Memory model

The model interleaves the actions sequentially consistently. This is
justified for what the model observes: every shared counter is modified only
by `fetch_add`, so each location has a single modification order that every
thread agrees on, and the counters only grow, so a stale relaxed load can only
delay a thread, never let it through early. The Release/Acquire pairs of the
crate order the non-atomic accesses along exactly the counter chains the model
walks; whether those chains suffice is what the race invariants in
`RearmBarrier.Spec` check.
-/

namespace RearmBarrier

/-- The const generics `WORKERS`, `CLUSTER` and the `count` argument. -/
structure Config where
  workers : Nat
  cluster : Nat
  count : Nat
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

/-- The locals of the ticket walk at the end of a consumer's iteration. -/
structure Walk where
  ticketId : Nat
  winId : Nat
  winSize : Nat
  mergeAmount : Nat
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

/-- The program counter of a consumer thread. -/
inductive ConsumerPhase
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
  /-- about to `fetch_add` ticket `w.ticketId` -/
  | walk (version : Nat) (w : Walk)
  /-- about to `fetch_add` the probe: this consumer completed the version -/
  | finish (version : Nat)
  | done
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

inductive Thread
  | producer
  | consumer (id : Nat)
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

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

structure State where
  probe : Nat
  tickets : Array Nat
  /-- `some v` once job `v` is written; `none` while it is being overwritten -/
  job : Option Nat
  /-- `some v` once the slot holds the result of version `v` -/
  results : Array (Option Nat)
  producer : ProducerPhase
  consumers : Array ConsumerPhase
deriving Repr, BEq, Hashable, Inhabited

/-- The barrier right after `new`, with the producer and every consumer
attached (locks taken) but before any of them has done anything. -/
def State.init (cfg : Config) : State :=
  { probe := 0
    tickets := Array.replicate cfg.storage 0
    job := none
    results := Array.replicate cfg.workers none
    producer := if cfg.count = 0 then .done else .beforeWrite 0
    consumers := Array.replicate cfg.workers .start }

/-- Result of trying to run one action of one thread. -/
inductive Outcome
  /-- the thread is finished or its spin condition does not hold -/
  | blocked
  | step (s : State) (ev : Option Event)
  /-- the model itself cannot continue (e.g. an index out of bounds in the
  Rust code, which would panic) -/
  | fault (msg : String)
deriving Repr, Inhabited

def nextProducer (cfg : Config) (v : Nat) : ProducerPhase :=
  if v + 1 < cfg.count then .beforeWrite (v + 1) else .done

def nextConsumer (cfg : Config) (v : Nat) : ConsumerPhase :=
  if v + 1 < cfg.count then .waitReady (v + 1) else .done

/-- The locals at the start of consumer `id`'s ticket walk. -/
def Walk.start (cfg : Config) (id : Nat) : Walk :=
  { ticketId := cfg.treeSize + id / cfg.cluster
    winId := id / cfg.cluster
    winSize := cfg.cluster
    mergeAmount := 1 }

def producerStep (cfg : Config) (s : State) : Outcome :=
  match s.producer with
  | .beforeWrite v =>
    .step { s with producer := .writing v, job := none } none
  | .writing v =>
    .step { s with producer := .publish v, job := some v } (some (.jobWrite v))
  | .publish v =>
    .step { s with producer := .waiting v, probe := s.probe + 1 } (some (.publish v s.probe))
  | .waiting v =>
    if s.probe = (v + 1) * 2 then
      .step { s with producer := .beforeComplete v } (some (.observeDone v s.probe))
    else
      .blocked
  | .beforeComplete v =>
    .step { s with producer := .completing v } none
  | .completing v =>
    .step { s with producer := nextProducer cfg v } (some (.complete v s.results.toList))
  | .done => .blocked

def State.setConsumer (s : State) (id : Nat) (ph : ConsumerPhase) : State :=
  { s with consumers := s.consumers.setIfInBounds id ph }

def consumerStep (cfg : Config) (s : State) (id : Nat) : Outcome :=
  match s.consumers[id]? with
  | none => .fault s!"consumer {id} does not exist"
  | some ph =>
    match ph with
    | .start =>
      .step (s.setConsumer id .initializing) none
    | .initializing =>
      let next := if cfg.count = 0 then .done else .waitReady 0
      .step { s.setConsumer id next with results := s.results.setIfInBounds id none } (some (.init id))
    | .waitReady v =>
      if s.probe > v * 2 then
        .step (s.setConsumer id (.beforeFunc v)) (some (.observeReady id v s.probe))
      else
        .blocked
    | .beforeFunc v =>
      .step (s.setConsumer id (.inFunc v)) none
    | .inFunc v =>
      .step { s.setConsumer id (.walk v (Walk.start cfg id)) with
                results := s.results.setIfInBounds id (some v) }
            (some (.func id v s.job))
    | .walk v w =>
      match s.tickets[w.ticketId]? with
      | none => .fault s!"consumer {id}: ticket {w.ticketId} is out of bounds"
      | some old =>
        if w.winId * w.winSize > cfg.workers then
          .fault s!"consumer {id}: WORKERS - win_id * win_size underflows"
        else
          let targetVal := min w.winSize (cfg.workers - w.winId * w.winSize)
          let newVal := old + w.mergeAmount
          let tickets := s.tickets.setIfInBounds w.ticketId newVal
          let ev := some (.ticket id v w.ticketId w.mergeAmount old)
          if newVal = cfg.workers * (v + 1) then
            -- every worker has completed this version
            .step { s.setConsumer id (.finish v) with tickets } ev
          else if w.ticketId = 0 || newVal != targetVal * (v + 1) then
            -- root reached or window not full: stop walking
            .step { s.setConsumer id (nextConsumer cfg v) with tickets } ev
          else
            let w' : Walk :=
              { ticketId := parent w.ticketId cfg.cluster
                winId := w.winId / cfg.cluster
                winSize := w.winSize * cfg.cluster
                mergeAmount := targetVal }
            .step { s.setConsumer id (.walk v w') with tickets } ev
    | .finish v =>
      .step { s.setConsumer id (nextConsumer cfg v) with probe := s.probe + 1 }
            (some (.finish id v s.probe))
    | .done => .blocked

def step (cfg : Config) (s : State) : Thread → Outcome
  | .producer => producerStep cfg s
  | .consumer id => consumerStep cfg s id

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

/-! ## Printing -/

def Thread.toString : Thread → String
  | .producer => "p"
  | .consumer id => s!"c {id}"

instance : ToString Thread := ⟨Thread.toString⟩

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

def ConsumerPhase.toString : ConsumerPhase → String
  | .start => "start"
  | .initializing => "initializing"
  | .waitReady v => s!"waitReady {v}"
  | .beforeFunc v => s!"beforeFunc {v}"
  | .inFunc v => s!"inFunc {v}"
  | .walk v w =>
    s!"walk {v} (ticket {w.ticketId}, win {w.winId}, winSize {w.winSize}, merge {w.mergeAmount})"
  | .finish v => s!"finish {v}"
  | .done => "done"

instance : ToString ConsumerPhase := ⟨ConsumerPhase.toString⟩

def State.describe (s : State) : String :=
  let consumers := s.consumers.toList.zipIdx.map fun (ph, i) => s!"  c {i}: {ph}\n"
  s!"probe = {s.probe}, tickets = {s.tickets}, job = {optNat s.job}, results = {s.results.toList.map optNat}\n" ++
  s!"  p: {s.producer}\n" ++ String.join consumers

end RearmBarrier
