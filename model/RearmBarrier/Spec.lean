import RearmBarrier.Model

/-!
# What the barrier promises

State invariants that every reachable state must satisfy. Together with the
shape of the state machines they say:

* `func` is called on every consumer once per version, in order, and while it
  runs the job slot holds exactly the job of that version;
* `complete` is called once per version, after every consumer's `func` for
  that version, and sees every consumer's result of that version;
* no two accesses to the job slot or a result slot overlap unless both are
  shared reads (the `Send`/`Sync` argument of the crate), and, via the
  happens-before tracking in `step`, every such pair is ordered;
* the counters never run ahead of the protocol, and the completion tree
  satisfies its counting invariant (`Tree.invariant`).

Out-of-range tickets are faults of `Tree.walk`, and deadlock freedom is not
a state invariant: the explorer checks that every reachable state that has
no enabled thread is final.
-/

namespace RearmBarrier

def ConsumerPhase.insideFunc : ConsumerPhase → Bool
  | .inFunc _ => true
  | _ => false

def ConsumerPhase.writesResult : ConsumerPhase → Bool
  | .inFunc _ | .initializing => true
  | _ => false

/-- All violated invariants of `s`, as human-readable messages. -/
def violations (cfg : Config) (s : State) : List String := Id.run do
  let mut out : List String := []
  let cs := s.consumers.toList.zipIdx
  -- non-atomic accesses to the job slot
  if let .writing v := s.producer then
    for (ph, i) in cs do
      if ph.insideFunc then
        out := out ++ [s!"race on the job slot: producer writes job {v} while consumer {i} is inside func"]
  -- non-atomic accesses to the result slots
  if let .completing v := s.producer then
    for (ph, i) in cs do
      if ph.writesResult then
        out := out ++ [s!"race on result slot {i}: producer is inside complete for version {v} while consumer {i} writes its result"]
  -- the job seen by func
  for (ph, i) in cs do
    if let .inFunc v := ph then
      if s.job != some v then
        out := out ++ [s!"consumer {i} runs func for version {v} but the job slot holds {optNat s.job}"]
  -- the results seen by complete
  if let .completing v := s.producer then
    for (r, i) in s.results.toList.zipIdx do
      if r != some v then
        out := out ++ [s!"complete for version {v} sees result {optNat r} in slot {i}"]
  -- counters never run ahead of the protocol
  if s.probe > 2 * cfg.count then
    out := out ++ [s!"probe = {s.probe} exceeds 2 * count = {2 * cfg.count}"]
  return out ++ s.tree.invariant cfg s.consumers []

/-- What must hold once every thread has returned. -/
def finalViolations (cfg : Config) (s : State) : List String :=
  violations cfg s ++
  (if !s.isFinal then ["not every thread has finished"] else []) ++
  (if s.probe != 2 * cfg.count then [s!"final probe = {s.probe}, expected {2 * cfg.count}"] else [])

end RearmBarrier
