import RearmBarrier.Tree

/-!
# Shared definitions

Configuration, memory orderings, vector clocks, the happens-before
bookkeeping of a non-atomic location, thread identities and the observable
events. See `RearmBarrier.Model` for how they fit together.
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

/-- Clock effects of a `fetch_add` on a location whose release clock is
`rel`, by a thread with clock `vc`: the thread's new clock and the location's
new release clock. -/
def rmwClocks (vc rel : VC) (ord : MemOrd) : VC × VC :=
  let vc := if ord.acquires then vc.join rel else vc
  let rel := if ord.releases then rel.join vc else rel
  (vc, rel)

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

/-- The observable actions; these are exactly the lines of a trace file.
Tickets are named by their index in the crate's flat heap array. -/
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

end RearmBarrier
