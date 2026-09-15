/-!
# The completion game, proved

"Game" here means a small nondeterministic transition system, nothing
game-theoretic: a relation `Step` between trees with three rules, where any
rule whose precondition holds anywhere in the tree may fire next. A run is
any sequence of steps, and that is what stands in for "any ordering of
completion events"; the theorems quantify over all runs.

One version of the completion tree, abstracted from everything else and from
the consumers' identities, as such a game:

* a node is a counter `finished`, a flag `pending` (the node has filled but
  its contribution has not yet been added to its parent), a release clock,
  and children; a node without children is a consumer, of size 1, so a
  crate leaf is a node whose children are consumers;
* a consumer finishes (`Step.finish`): its counter becomes 1 and it is
  pending — this is the consumer's own `fetch_add` on its leaf;
* a pending child is applied to its parent (`Step.apply`): the parent's
  counter grows by the child's size, the parent's clock absorbs the child's
  (the `fetch_add` is `AcqRel`, so the consumer doing it has acquired the
  child's clock and releases it into the parent), the child is no longer
  pending, and the parent becomes pending if it filled;
* any of this can happen inside any child at any time (`Step.inner`).

Every interleaving of the crate's ticket walks for one version is a sequence
of these steps. What is proved, for every tree shape and every sequence of
steps:

* `Inv` is preserved (`Step.inv`) and holds initially (`Fresh.inv`);
* a node that is done has every consumer below it finished
  (`done_contributed`) and its clock dominates every one of their clocks
  (`done_clock`) — this is the happens-before edge from every result write
  to the `fetch_add` that completes the barrier, from which the producer's
  Acquire of the probe orders `complete` after all of them;
* a done node never changes again (`noStep_of_done`): the barrier completes
  exactly once;
* if every consumer has finished and the root is not done, some step is
  possible (`progress`), and every step decreases `measure`
  (`Step.measure_lt`), so every maximal run ends with the root done
  (`terminal_done`): any ordering of completion events finishes.
-/

namespace RearmBarrier.Completion

/-! ## Clocks -/

/-- Vector clocks as functions, which is all the proofs need. -/
def Clock := Nat → Nat

def Clock.join (a b : Clock) : Clock := fun i => max (a i) (b i)

def Clock.le (a b : Clock) : Prop := ∀ i, a i ≤ b i

theorem Clock.le_refl (a : Clock) : a.le a := fun _ => Nat.le_refl _

theorem Clock.le_trans {a b c : Clock} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  fun i => Nat.le_trans (h₁ i) (h₂ i)

theorem Clock.le_join_left (a b : Clock) : a.le (a.join b) := fun _ => Nat.le_max_left _ _

theorem Clock.le_join_right (a b : Clock) : b.le (a.join b) := fun _ => Nat.le_max_right _ _

/-! ## Nodes -/

inductive Node
  | mk (finished : Nat) (pending : Bool) (clock : Clock) (children : List Node)

namespace Node

def finished : Node → Nat
  | .mk f _ _ _ => f

def pending : Node → Bool
  | .mk _ p _ _ => p

def clock : Node → Clock
  | .mk _ _ c _ => c

def children : Node → List Node
  | .mk _ _ _ cs => cs

/-- The child is no longer pending: its contribution has been applied. -/
def unpend : Node → Node
  | .mk f _ c cs => .mk f false c cs

end Node

mutual
/-- The number of consumers under a node. -/
def Node.size : Node → Nat
  | .mk _ _ _ [] => 1
  | .mk _ _ _ (c :: cs) => sizes (c :: cs)

def sizes : List Node → Nat
  | [] => 0
  | c :: cs => c.size + sizes cs
end

theorem Node.size_nil (f p c) : (Node.mk f p c []).size = 1 := by simp [Node.size]

theorem Node.size_cons (f p c x cs) : (Node.mk f p c (x :: cs)).size = sizes (x :: cs) := by
  simp [Node.size]

theorem Node.size_of_ne_nil (f p c cs) (h : cs ≠ []) : (Node.mk f p c cs).size = sizes cs := by
  cases cs with
  | nil => exact absurd rfl h
  | cons x cs => simp [Node.size]

theorem sizes_cons (c cs) : sizes (c :: cs) = c.size + sizes cs := by simp [sizes]

theorem Node.size_pos : (n : Node) → 0 < n.size
  | .mk _ _ _ [] => by simp [Node.size]
  | .mk _ _ _ (c :: _) => by
    have := Node.size_pos c
    simp [Node.size, sizes]
    omega

theorem Node.size_unpend (n : Node) : n.unpend.size = n.size := by
  cases n with
  | mk f p c cs => cases cs <;> simp [Node.unpend, Node.size]

/-- The node has filled. -/
def Node.done (n : Node) : Prop := n.finished = n.size

/-- The node has filled and its contribution has reached its parent. -/
def Node.applied (n : Node) : Prop := n.done ∧ n.pending = false

instance : DecidablePred Node.applied := fun n =>
  inferInstanceAs (Decidable (n.finished = n.size ∧ n.pending = false))

/-- What a child currently contributes to its parent's counter. -/
def contrib (n : Node) : Nat := if n.applied then n.size else 0

def appliedSum : List Node → Nat
  | [] => 0
  | c :: cs => contrib c + appliedSum cs

theorem contrib_le (n : Node) : contrib n ≤ n.size := by
  unfold contrib; split <;> omega

theorem appliedSum_le_sizes : (cs : List Node) → appliedSum cs ≤ sizes cs
  | [] => Nat.le_refl _
  | c :: cs => by
    have := contrib_le c
    have := appliedSum_le_sizes cs
    simp [appliedSum, sizes]
    omega

/-- The counter reaches the size exactly when every child has been applied. -/
theorem all_applied_of_appliedSum_eq : (cs : List Node) → appliedSum cs = sizes cs →
    ∀ ch ∈ cs, ch.applied
  | [], _, _, h => by simp at h
  | c :: cs, h, ch, hm => by
    have h₁ := contrib_le c
    have h₂ := appliedSum_le_sizes cs
    have h₃ := Node.size_pos c
    simp [appliedSum, sizes] at h
    have hc : contrib c = c.size := by omega
    have hcs : appliedSum cs = sizes cs := by omega
    simp at hm
    rcases hm with rfl | hm
    · unfold contrib at hc
      split at hc
      · assumption
      · omega
    · exact all_applied_of_appliedSum_eq cs hcs ch hm

theorem exists_not_applied : (cs : List Node) → appliedSum cs ≠ sizes cs →
    ∃ ch ∈ cs, ¬ ch.applied
  | [], h => absurd rfl h
  | c :: cs, h => by
    by_cases hc : c.applied
    · have : appliedSum cs ≠ sizes cs := by
        intro h'
        apply h
        simp [appliedSum, sizes, contrib, hc, h']
      obtain ⟨ch, hm, hn⟩ := exists_not_applied cs this
      exact ⟨ch, by simp [hm], hn⟩
    · exact ⟨c, by simp, hc⟩

/-! ## Lists indexed by position -/

theorem mem_of_getElem? : (cs : List Node) → (k : Nat) → (ch : Node) → cs[k]? = some ch → ch ∈ cs
  | [], _, _, h => by simp at h
  | c :: cs, 0, ch, h => by simp at h; simp [h]
  | c :: cs, k + 1, ch, h => by
    simp at h
    exact List.mem_cons_of_mem _ (mem_of_getElem? cs k ch h)

theorem getElem?_of_mem : (cs : List Node) → (ch : Node) → ch ∈ cs → ∃ k : Nat, cs[k]? = some ch
  | [], _, h => by simp at h
  | c :: cs, ch, h => by
    simp at h
    rcases h with rfl | h
    · exact ⟨0, by simp⟩
    · obtain ⟨k, hk⟩ := getElem?_of_mem cs ch h
      exact ⟨k + 1, by simp [hk]⟩

theorem mem_of_mem_set : (cs : List Node) → (k : Nat) → (x y : Node) → y ∈ cs.set k x →
    y ∈ cs ∨ y = x
  | [], _, _, _, h => by simp at h
  | c :: cs, 0, x, y, h => by
    simp at h
    rcases h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (by simp [h])
  | c :: cs, k + 1, x, y, h => by
    simp at h
    rcases h with rfl | h
    · exact Or.inl (by simp)
    · rcases mem_of_mem_set cs k x y h with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr h

theorem sizes_set : (cs : List Node) → (k : Nat) → (ch ch' : Node) → cs[k]? = some ch →
    ch'.size = ch.size → sizes (cs.set k ch') = sizes cs
  | [], _, _, _, h, _ => by simp at h
  | c :: cs, 0, ch, ch', h, hs => by
    simp at h
    subst h
    simp [sizes, hs]
  | c :: cs, k + 1, ch, ch', h, hs => by
    simp at h
    simp [sizes, sizes_set cs k ch ch' h hs]

theorem appliedSum_set : (cs : List Node) → (k : Nat) → (ch ch' : Node) → cs[k]? = some ch →
    appliedSum (cs.set k ch') + contrib ch = appliedSum cs + contrib ch'
  | [], _, _, _, h => by simp at h
  | c :: cs, 0, ch, ch', h => by
    simp at h
    subst h
    simp [appliedSum]
    omega
  | c :: cs, k + 1, ch, ch', h => by
    simp at h
    have := appliedSum_set cs k ch ch' h
    simp [appliedSum]
    omega

/-! ## The invariant -/

/-- The counting and clock invariant of one node and everything below it. -/
inductive Inv : Node → Prop
  | leaf (f : Nat) (p : Bool) (c : Clock) (hf : f ≤ 1) (hp : p = true → f = 1) :
      Inv (.mk f p c [])
  | node (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (hne : cs ≠ [])
      (hf : f = appliedSum cs)
      (hp : p = true → f = sizes cs)
      (hcs : ∀ ch ∈ cs, Inv ch)
      (hclk : ∀ ch ∈ cs, ch.applied → ch.clock.le c) :
      Inv (.mk f p c cs)

theorem Inv.done_of_pending {n : Node} (h : Inv n) (hp : n.pending = true) : n.done := by
  cases h with
  | leaf f p c hf hp' => simp [Node.pending] at hp; simp [Node.done, Node.finished, Node.size, hp' hp]
  | node f p c cs hne hf hp' hcs hclk =>
    simp [Node.pending] at hp
    simp [Node.done, Node.finished, Node.size_of_ne_nil _ _ _ _ hne, hp' hp]

theorem Inv.unpend {n : Node} (h : Inv n) : Inv n.unpend := by
  cases h with
  | leaf f p c hf hp => exact .leaf f false c hf (by simp)
  | node f p c cs hne hf hp hcs hclk => exact .node f false c cs hne hf (by simp) hcs hclk

/-- A done inner node has every child applied. -/
theorem Inv.all_applied {f : Nat} {p : Bool} {c : Clock} {cs : List Node}
    (h : Inv (.mk f p c cs)) (hne : cs ≠ []) (hd : (Node.mk f p c cs).done) :
    ∀ ch ∈ cs, ch.applied := by
  cases h with
  | leaf => exact absurd rfl hne
  | node f p c cs _ hf hp hcs hclk =>
    simp [Node.done, Node.finished, Node.size_of_ne_nil _ _ _ _ hne] at hd
    exact all_applied_of_appliedSum_eq cs (hf ▸ hd)

/-! ## Steps -/

inductive Step : Node → Node → Prop
  /-- a consumer finishes: its `fetch_add` on its leaf -/
  | finish (c : Clock) : Step (.mk 0 false c []) (.mk 1 true c [])
  /-- the consumer that filled child `k` adds the child's size to this node -/
  | apply (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (k : Nat) (ch : Node)
      (hk : cs[k]? = some ch) (hp : ch.pending = true) :
      Step (.mk f p c cs)
           (.mk (f + ch.size) (decide (f + ch.size = sizes cs)) (c.join ch.clock)
                (cs.set k ch.unpend))
  /-- something happens inside child `k` -/
  | inner (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (k : Nat) (ch ch' : Node)
      (hk : cs[k]? = some ch) (h : Step ch ch') :
      Step (.mk f p c cs) (.mk f p c (cs.set k ch'))

theorem Step.size_eq {n n' : Node} (h : Step n n') : n'.size = n.size := by
  induction h with
  | finish c => simp [Node.size]
  | apply f p c cs k ch hk hp =>
    have hne : cs ≠ [] := by
      intro h; subst h; simp at hk
    have hne' : cs.set k ch.unpend ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
      exact hne this
    rw [Node.size_of_ne_nil _ _ _ _ hne', Node.size_of_ne_nil _ _ _ _ hne]
    exact sizes_set cs k ch ch.unpend hk (Node.size_unpend ch)
  | inner f p c cs k ch ch' hk _ ih =>
    have hne : cs ≠ [] := by
      intro h; subst h; simp at hk
    have hne' : cs.set k ch' ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
      exact hne this
    rw [Node.size_of_ne_nil _ _ _ _ hne', Node.size_of_ne_nil _ _ _ _ hne]
    exact sizes_set cs k ch ch' hk ih

/-- Nothing happens below or at a node once it is done: the barrier fills
exactly once. -/
theorem noStep_of_done {n : Node} (hinv : Inv n) (hd : n.done) : ∀ n', ¬ Step n n' := by
  induction hinv with
  | leaf f p c hf hp =>
    intro n' hs
    cases hs with
    | finish => simp [Node.done, Node.finished, Node.size] at hd
    | apply _ _ _ _ k ch hk => simp at hk
    | inner _ _ _ _ k ch ch' hk => simp at hk
  | node f p c cs hne hf hp hcs hclk ih =>
    intro n' hs
    have hall := Inv.all_applied (.node f p c cs hne hf hp hcs hclk) hne hd
    cases hs with
    | finish => exact absurd rfl hne
    | apply _ _ _ _ k ch hk hpend =>
      have := (hall ch (mem_of_getElem? cs k ch hk)).2
      rw [this] at hpend
      exact Bool.false_ne_true hpend
    | inner _ _ _ _ k ch ch' hk hstep =>
      have hm := mem_of_getElem? cs k ch hk
      exact ih ch hm (hall ch hm).1 ch' hstep

/-- A step never produces an applied node: filling makes a node pending, and
an applied node admits no step. -/
theorem Step.not_applied {n n' : Node} (hinv : Inv n) (hs : Step n n') : ¬ n'.applied := by
  intro happ
  cases hs with
  | finish c => simp [Node.applied, Node.pending] at happ
  | apply f p c cs k ch hk hp =>
    have hne : cs ≠ [] := by
      intro h; subst h; simp at hk
    obtain ⟨hd, hpend⟩ := happ
    simp [Node.pending] at hpend
    have hne' : cs.set k ch.unpend ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
      exact hne this
    simp [Node.done, Node.finished, Node.size_of_ne_nil _ _ _ _ hne',
      sizes_set cs k ch ch.unpend hk (Node.size_unpend ch)] at hd
    exact hpend hd
  | inner f p c cs k ch ch' hk hstep =>
    have hne : cs ≠ [] := by
      intro h; subst h; simp at hk
    have hne' : cs.set k ch' ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
      exact hne this
    obtain ⟨hd, hpend⟩ := happ
    simp [Node.done, Node.finished, Node.size_of_ne_nil _ _ _ _ hne',
      sizes_set cs k ch ch' hk hstep.size_eq] at hd
    have hdone : (Node.mk f p c cs).done := by
      simp [Node.done, Node.finished, Node.size_of_ne_nil _ _ _ _ hne, hd]
    exact noStep_of_done hinv hdone _ (.inner f p c cs k ch ch' hk hstep)

/-- The invariant is preserved by every step. -/
theorem Step.inv {n n' : Node} (hinv : Inv n) (hs : Step n n') : Inv n' := by
  induction hs with
  | finish c => exact .leaf 1 true c (Nat.le_refl _) (fun _ => rfl)
  | apply f p c cs k ch hk hpend =>
    cases hinv with
    | leaf => simp at hk
    | node _ _ _ _ hne hf hp hcs hclk =>
      have hm := mem_of_getElem? cs k ch hk
      have hchinv := hcs ch hm
      have hchdone := hchinv.done_of_pending hpend
      have hne' : cs.set k ch.unpend ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        exact hne this
      have hsum := appliedSum_set cs k ch ch.unpend hk
      have hnot : ¬ ch.applied := fun h => by
        rw [h.2] at hpend; exact Bool.false_ne_true hpend
      have happ' : ch.unpend.applied := by
        refine ⟨?_, by cases ch; simp [Node.unpend, Node.pending]⟩
        simp only [Node.done, Node.size_unpend]
        cases ch with
        | mk f' p' c' cs' => exact hchdone
      have hc : contrib ch = 0 := by simp [contrib, hnot]
      have hc' : contrib ch.unpend = ch.size := by simp [contrib, happ', Node.size_unpend]
      refine .node _ _ _ _ hne' ?_ ?_ ?_ ?_
      · omega
      · intro hdec
        simp at hdec
        rw [sizes_set cs k ch ch.unpend hk (Node.size_unpend ch)]
        exact hdec
      · intro x hx
        rcases mem_of_mem_set cs k ch.unpend x hx with hx | rfl
        · exact hcs x hx
        · exact hchinv.unpend
      · intro x hx hxapp
        rcases mem_of_mem_set cs k ch.unpend x hx with hx | rfl
        · exact Clock.le_trans (hclk x hx hxapp) (Clock.le_join_left _ _)
        · cases ch with
          | mk f' p' c' cs' => exact Clock.le_join_right _ _
  | inner f p c cs k ch ch' hk hstep ih =>
    cases hinv with
    | leaf => simp at hk
    | node _ _ _ _ hne hf hp hcs hclk =>
      have hm := mem_of_getElem? cs k ch hk
      have hchinv := hcs ch hm
      have hch' := ih hchinv
      have hne' : cs.set k ch' ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        exact hne this
      have hsum := appliedSum_set cs k ch ch' hk
      have hnot' : ¬ ch'.applied := hstep.not_applied hchinv
      have hnot : ¬ ch.applied := by
        intro happ
        exact noStep_of_done hchinv happ.1 ch' hstep
      have hc : contrib ch = 0 := by simp [contrib, hnot]
      have hc' : contrib ch' = 0 := by simp [contrib, hnot']
      refine .node _ _ _ _ hne' ?_ ?_ ?_ ?_
      · omega
      · intro hpt
        rw [sizes_set cs k ch ch' hk hstep.size_eq]
        exact hp hpt
      · intro x hx
        rcases mem_of_mem_set cs k ch' x hx with hx | rfl
        · exact hcs x hx
        · exact hch'
      · intro x hx hxapp
        rcases mem_of_mem_set cs k ch' x hx with hx | rfl
        · exact hclk x hx hxapp
        · exact absurd hxapp hnot'

/-! ## What done means -/

/-- Every consumer under the node has finished. -/
inductive Contributed : Node → Prop
  | leaf (p : Bool) (c : Clock) : Contributed (.mk 1 p c [])
  | node (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (hne : cs ≠ [])
      (h : ∀ ch ∈ cs, Contributed ch) : Contributed (.mk f p c cs)

/-- Every consumer under the node has a clock below `K`. -/
inductive LeavesLE (K : Clock) : Node → Prop
  | leaf (f : Nat) (p : Bool) (c : Clock) (h : c.le K) : LeavesLE K (.mk f p c [])
  | node (f : Nat) (p : Bool) (c : Clock) (cs : List Node) (hne : cs ≠ [])
      (h : ∀ ch ∈ cs, LeavesLE K ch) : LeavesLE K (.mk f p c cs)

theorem LeavesLE.mono {K K' : Clock} (hK : K.le K') {n : Node} (h : LeavesLE K n) :
    LeavesLE K' n := by
  induction h with
  | leaf f p c hc => exact .leaf f p c (Clock.le_trans hc hK)
  | node f p c cs hne _ ih => exact .node f p c cs hne ih

/-- A done node has every consumer below it finished. -/
theorem done_contributed {n : Node} (hinv : Inv n) (hd : n.done) : Contributed n := by
  induction hinv with
  | leaf f p c hf hp =>
    simp [Node.done, Node.finished, Node.size] at hd
    subst hd
    exact .leaf p c
  | node f p c cs hne hf hp hcs hclk ih =>
    have hall := Inv.all_applied (.node f p c cs hne hf hp hcs hclk) hne hd
    exact .node f p c cs hne fun ch hm => ih ch hm (hall ch hm).1

/-- A done node's clock dominates the clock of every consumer below it: every
result write happens before the `fetch_add` that completes the version. -/
theorem done_clock {n : Node} (hinv : Inv n) (hd : n.done) : LeavesLE n.clock n := by
  induction hinv with
  | leaf f p c hf hp => exact .leaf f p c (Clock.le_refl c)
  | node f p c cs hne hf hp hcs hclk ih =>
    have hall := Inv.all_applied (.node f p c cs hne hf hp hcs hclk) hne hd
    exact .node f p c cs hne fun ch hm =>
      (ih ch hm (hall ch hm).1).mono (hclk ch hm (hall ch hm))

/-! ## Progress and termination -/

/-- If every consumer has finished and the node is not done, a step is possible. -/
theorem progress {n : Node} (hinv : Inv n) (hc : Contributed n) (hd : ¬ n.done) :
    ∃ n', Step n n' := by
  induction hinv with
  | leaf f p c hf hp =>
    exfalso
    cases hc with
    | leaf => exact hd (by simp [Node.done, Node.finished, Node.size])
    | node _ _ _ _ hne => exact absurd rfl hne
  | node f p c cs hne hf hp hcs hclk ih =>
    have hc' : ∀ ch ∈ cs, Contributed ch := by
      cases hc with
      | leaf => exact absurd rfl hne
      | node _ _ _ _ _ h => exact h
    have hne_sum : appliedSum cs ≠ sizes cs := by
      intro h
      apply hd
      simp [Node.done, Node.finished, Node.size_of_ne_nil _ _ _ _ hne, hf, h]
    obtain ⟨ch, hm, hnot⟩ := exists_not_applied cs hne_sum
    obtain ⟨k, hk⟩ := getElem?_of_mem cs ch hm
    by_cases hpend : ch.pending = true
    · exact ⟨_, .apply f p c cs k ch hk hpend⟩
    · have hnd : ¬ ch.done := fun hdone => hnot ⟨hdone, by simpa using hpend⟩
      obtain ⟨ch', hs⟩ := ih ch hm (hc' ch hm) hnd
      exact ⟨_, .inner f p c cs k ch ch' hk hs⟩

/-- A maximal run of the game ends with the root done. -/
theorem terminal_done {n : Node} (hinv : Inv n) (hc : Contributed n)
    (hstuck : ∀ n', ¬ Step n n') : n.done := by
  apply Classical.byContradiction
  intro hd
  obtain ⟨n', hs⟩ := progress hinv hc hd
  exact hstuck n' hs

mutual
/-- Two for every node not yet done, one for every pending node. -/
def Node.measure : Node → Nat
  | .mk f p c cs => (if f = (Node.mk f p c cs).size then 0 else 2) + (if p then 1 else 0) + measures cs

def measures : List Node → Nat
  | [] => 0
  | c :: cs => c.measure + measures cs
end

theorem measures_set : (cs : List Node) → (k : Nat) → (ch ch' : Node) → cs[k]? = some ch →
    measures (cs.set k ch') + ch.measure = measures cs + ch'.measure
  | [], _, _, _, h => by simp at h
  | c :: cs, 0, ch, ch', h => by
    simp at h
    subst h
    simp [measures]
    omega
  | c :: cs, k + 1, ch, ch', h => by
    simp at h
    have := measures_set cs k ch ch' h
    simp [measures]
    omega

theorem Node.measure_mk (f p c cs) :
    (Node.mk f p c cs).measure =
      (if f = (Node.mk f p c cs).size then 0 else 2) + (if p then 1 else 0) + measures cs := by
  simp [Node.measure]

set_option linter.deprecated false in
/-- Every step decreases the measure: the game terminates. -/
theorem Step.measure_lt {n n' : Node} (hinv : Inv n) (hs : Step n n') : n'.measure < n.measure := by
  induction hs with
  | finish c => simp [Node.measure, Node.size, measures]
  | apply f p c cs k ch hk hpend =>
    cases hinv with
    | leaf => simp at hk
    | node _ _ _ _ hne hf hp hcs hclk =>
      have hm := mem_of_getElem? cs k ch hk
      have hchinv := hcs ch hm
      have hchdone := hchinv.done_of_pending hpend
      have hne' : cs.set k ch.unpend ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        exact hne this
      have hsz := sizes_set cs k ch ch.unpend hk (Node.size_unpend ch)
      have hms := measures_set cs k ch ch.unpend hk
      -- the node was not done: it has a pending child
      have hnd : f ≠ sizes cs := by
        intro h
        have hall := all_applied_of_appliedSum_eq cs (hf ▸ h)
        have := (hall ch hm).2
        rw [this] at hpend
        exact Bool.false_ne_true hpend
      have hpf : p = false := by
        cases p with
        | false => rfl
        | true => exact absurd (hp rfl) hnd
      -- the child's measure drops by one when it stops being pending
      have hchm : ch.unpend.measure + 1 = ch.measure := by
        cases ch with
        | mk f' p' c' cs' =>
          simp only [Node.pending] at hpend
          subst hpend
          have hsz : (Node.mk f' false c' cs').size = (Node.mk f' true c' cs').size := by
            cases cs' <;> simp [Node.size]
          simp only [Node.done, Node.finished] at hchdone
          simp only [Node.unpend]
          rw [Node.measure_mk f' false c' cs', Node.measure_mk f' true c' cs', hsz, if_pos hchdone]
          simp
          omega
      rw [Node.measure_mk, Node.measure_mk, Node.size_of_ne_nil _ _ _ _ hne',
        Node.size_of_ne_nil _ _ _ _ hne, hsz, hpf]
      simp [hnd]
      split <;> omega
  | inner f p c cs k ch ch' hk hstep ih =>
    cases hinv with
    | leaf => simp at hk
    | node _ _ _ _ hne hf hp hcs hclk =>
      have hm := mem_of_getElem? cs k ch hk
      have hlt := ih (hcs ch hm)
      have hne' : cs.set k ch' ≠ [] := by
        intro h
        have := congrArg List.length h
        simp at this
        exact hne this
      have hsz := sizes_set cs k ch ch' hk hstep.size_eq
      have hms := measures_set cs k ch ch' hk
      rw [Node.measure_mk, Node.measure_mk, Node.size_of_ne_nil _ _ _ _ hne',
        Node.size_of_ne_nil _ _ _ _ hne, hsz]
      omega

/-! ## The initial tree -/

/-- A tree in which nothing has happened yet. -/
inductive Fresh : Node → Prop
  | leaf (c : Clock) : Fresh (.mk 0 false c [])
  | node (c : Clock) (cs : List Node) (hne : cs ≠ []) (h : ∀ ch ∈ cs, Fresh ch) :
      Fresh (.mk 0 false c cs)

theorem Fresh.not_applied {n : Node} (h : Fresh n) : ¬ n.applied := by
  intro ⟨hd, _⟩
  have := Node.size_pos n
  cases h <;> simp [Node.done, Node.finished] at hd <;> omega

theorem appliedSum_eq_zero : (cs : List Node) → (∀ ch ∈ cs, ¬ ch.applied) → appliedSum cs = 0
  | [], _ => rfl
  | c :: cs, h => by
    have hc := h c (by simp)
    have := appliedSum_eq_zero cs fun ch hm => h ch (by simp [hm])
    simp [appliedSum, contrib, hc, this]

theorem Fresh.inv {n : Node} (h : Fresh n) : Inv n := by
  induction h with
  | leaf c => exact .leaf 0 false c (by omega) (by simp)
  | node c cs hne hf ih =>
    refine .node 0 false c cs hne ?_ (by simp) ih ?_
    · exact (appliedSum_eq_zero cs fun ch hm => (hf ch hm).not_applied).symm
    · intro ch hm happ
      exact absurd happ (hf ch hm).not_applied

/-! ## Runs -/

/-- Zero or more steps. -/
inductive Steps : Node → Node → Prop
  | refl (n : Node) : Steps n n
  | tail {a b c : Node} (h : Steps a b) (hs : Step b c) : Steps a c

theorem Steps.inv {n n' : Node} (hinv : Inv n) (h : Steps n n') : Inv n' := by
  induction h with
  | refl => exact hinv
  | tail _ hs ih => exact hs.inv ih

/-- Starting fresh, any run that can go no further has completed the
barrier, with every consumer finished and every consumer's clock acquired. -/
theorem run_completes {n n' : Node} (hf : Fresh n) (hc : Contributed n') (h : Steps n n')
    (hstuck : ∀ m, ¬ Step n' m) : n'.done ∧ LeavesLE n'.clock n' := by
  have hinv := h.inv hf.inv
  have hd := terminal_done hinv hc hstuck
  exact ⟨hd, done_clock hinv hd⟩

end RearmBarrier.Completion
