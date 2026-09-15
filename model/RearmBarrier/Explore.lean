import Std.Data.HashMap
import Std.Data.HashSet
import RearmBarrier.Spec

/-!
# Bounded exhaustive exploration

Depth-first enumeration of every reachable state of a configuration under
every interleaving, checking the invariants of `RearmBarrier.Spec` in every
state and deadlock freedom in every state without an enabled thread.
-/

namespace RearmBarrier

variable {τ κ : Type} [BEq τ] [Hashable τ] [BEq κ] [Hashable κ]

structure ExploreResult (τ κ : Type) where
  states : Nat
  transitions : Nat
  /-- the first problem found, with the path (thread, event) leading to it -/
  failure : Option (String × List (Thread × Option Event) × State τ κ)
  /-- the state budget was exhausted -/
  truncated : Bool
deriving Inhabited

private structure Frontier (τ κ : Type) [BEq τ] [Hashable τ] [BEq κ] [Hashable κ] where
  stack : List (State τ κ)
  visited : Std.HashSet (State τ κ)
  parents : Std.HashMap (State τ κ) (Thread × State τ κ)
  states : Nat
  transitions : Nat

private partial def pathTo (E : Engine τ κ) (cfg : Config)
    (parents : Std.HashMap (State τ κ) (Thread × State τ κ))
    (s : State τ κ) (acc : List (Thread × Option Event)) : List (Thread × Option Event) :=
  match parents[s]? with
  | none => acc
  | some (t, p) =>
    let ev := match step E cfg p t with
      | .step _ ev => ev
      | _ => none
    pathTo E cfg parents p ((t, ev) :: acc)

private partial def loop [Inhabited τ] [Inhabited κ] (E : Engine τ κ) (cfg : Config) (maxStates : Nat)
    (f : Frontier τ κ) : ExploreResult τ κ :=
  match f.stack with
  | [] => { states := f.states, transitions := f.transitions, failure := none, truncated := false }
  | s :: rest =>
    let fail (msg : String) : ExploreResult τ κ :=
      { states := f.states, transitions := f.transitions,
        failure := some (msg, pathTo E cfg f.parents s [], s), truncated := false }
    match violations E cfg s with
    | msg :: _ => fail msg
    | [] =>
      let succ := (threads cfg).filterMap fun t =>
        match step E cfg s t with
        | .blocked => none
        | .step s' _ => some (Sum.inl (t, s'))
        | .fault m => some (Sum.inr s!"{t}: {m}")
        | .race m => some (Sum.inr s!"{t}: {m}")
      match succ.find? (·.isRight) with
      | some (.inr m) => fail m
      | _ =>
        if succ.isEmpty && !s.isFinal then
          fail "deadlock: no thread is enabled but not every thread has finished"
        else if succ.isEmpty && s.probe != 2 * cfg.count then
          fail s!"final probe = {s.probe}, expected {2 * cfg.count}"
        else
          let f' := succ.foldl (init := { f with stack := rest }) fun f x =>
            match x with
            | .inr _ => f
            | .inl (t, s') =>
              let f := { f with transitions := f.transitions + 1 }
              if f.visited.contains s' then f
              else
                { f with
                  stack := s' :: f.stack
                  visited := f.visited.insert s'
                  parents := f.parents.insert s' (t, s)
                  states := f.states + 1 }
          if f'.states > maxStates then
            { states := f'.states, transitions := f'.transitions, failure := none, truncated := true }
          else
            loop E cfg maxStates f'

/-- Explore every interleaving of `cfg`, visiting at most `maxStates` states. -/
def explore [Inhabited τ] [Inhabited κ] (E : Engine τ κ) (cfg : Config) (maxStates : Nat := 2000000) :
    ExploreResult τ κ :=
  let s0 := State.init E cfg
  loop E cfg maxStates
    { stack := [s0], visited := Std.HashSet.emptyWithCapacity.insert s0, parents := {},
      states := 1, transitions := 0 }

end RearmBarrier
