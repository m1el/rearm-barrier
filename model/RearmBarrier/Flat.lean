import RearmBarrier.Model

/-!
# The flat engine

Mirrors `src/lib.rs` literally: the tickets are a flat array laid out as a
heap (`(ticket_id - 1) / CLUSTER` is the parent), and the consumer's walk
keeps the locals `ticket_id`, `win_id`, `win_size` and `merge_amount`.
-/

namespace RearmBarrier.Flat

/-- Counters and release clocks of the flat ticket array. -/
structure Tickets where
  counts : Array Nat
  rel : Array VC
deriving Repr, BEq, Hashable, Inhabited

instance : ToString Tickets := ⟨fun t => s!"tickets = {t.counts}"⟩

/-- The locals of the ticket walk. -/
structure Walk where
  ticketId : Nat
  winId : Nat
  winSize : Nat
  mergeAmount : Nat
deriving Repr, BEq, Hashable, DecidableEq, Inhabited

instance : ToString Walk :=
  ⟨fun w => s!"ticket {w.ticketId}, win {w.winId}, winSize {w.winSize}, merge {w.mergeAmount}"⟩

/-- The locals at the start of consumer `id`'s ticket walk. -/
def Walk.start (cfg : Config) (id : Nat) : Walk :=
  { ticketId := cfg.treeSize + id / cfg.cluster
    winId := id / cfg.cluster
    winSize := cfg.cluster
    mergeAmount := 1 }

def init (cfg : Config) : Tickets :=
  { counts := Array.replicate cfg.storage 0
    rel := Array.replicate cfg.storage (VC.zero (cfg.workers + 1)) }

/-- One iteration of the `loop` in `consumer`. -/
def step (cfg : Config) (t : Tickets) (w : Walk) (v : Nat) (vc : VC) (ord : MemOrd) :
    EngineResult Tickets Walk :=
  match t.counts[w.ticketId]? with
  | none => .fault s!"ticket {w.ticketId} is out of bounds"
  | some old =>
    if w.winId * w.winSize > cfg.workers then
      .fault "WORKERS - win_id * win_size underflows"
    else
      -- How many workers are in this window, limited by the total number of workers
      let targetVal := min w.winSize (cfg.workers - w.winId * w.winSize)
      let newVal := old + w.mergeAmount
      let (vc, rel) := rmwTicketClocks vc t.rel[w.ticketId]! ord
      let t := { counts := t.counts.setIfInBounds w.ticketId newVal
                 rel := t.rel.setIfInBounds w.ticketId rel }
      let rmw := { ticketId := w.ticketId, amount := w.mergeAmount, old }
      if newVal = cfg.workers * (v + 1) then
        -- Every worker has completed this version
        .ok t vc rmw .finished
      else if w.ticketId = 0 || newVal != targetVal * (v + 1) then
        -- We reached the root of the tree, or didn't fill the window
        .ok t vc rmw .stop
      else
        .ok t vc rmw (.continue
          { ticketId := parent w.ticketId cfg.cluster
            winId := w.winId / cfg.cluster
            winSize := w.winSize * cfg.cluster
            mergeAmount := targetVal })

def violations (cfg : Config) (t : Tickets) (_ : Array (ConsumerPhase Walk)) : List String :=
  t.counts.toList.zipIdx.filterMap fun (c, i) =>
    if c > cfg.workers * cfg.count then
      some s!"ticket {i} = {c} exceeds WORKERS * count = {cfg.workers * cfg.count}"
    else none

def engine : Engine Tickets Walk :=
  { init, start := Walk.start, step, violations, summary := fun t => s!"tickets = {t.counts}" }

end RearmBarrier.Flat
