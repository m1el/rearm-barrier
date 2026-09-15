import RearmBarrier.TreeInvariant

/-!
# The initial tree

`Tree.init` satisfies the counting invariant at version `0` with every
consumer in `start`. The two facts that need work are about the layout:
`Cursor.start id` names a leaf whose window holds `id` (`init_leaves`) and no
other leaf holds it (`init_leaf_unique`). Both follow from a characterisation
of every node of a built tree by its path (`get_build_char`): the node at
path `q` is `build (H - |q|)` at `digits q * C ^ (H - |q| + 1)`.
-/

namespace RearmBarrier

/-! ## Children of a built node by index -/

theorem buildChildren_getElem? (child : Nat → Tree) (W w lo : Nat) :
    ∀ n k i, (Tree.buildChildren child W w lo n k)[i]? =
      if i < n ∧ lo + (k + i) * w < W then some (child (lo + (k + i) * w)) else none
  | 0, _, _ => by simp [Tree.buildChildren]
  | n + 1, k, i => by
    simp only [Tree.buildChildren]
    split
    · rename_i hk
      cases i with
      | zero => simp [hk]
      | succ i =>
        simp only [List.getElem?_cons_succ]
        rw [buildChildren_getElem? child W w lo n (k + 1) i]
        have e : k + 1 + i = k + (i + 1) := by omega
        rw [e]
        simp only [Nat.add_lt_add_iff_right]
    · rename_i hk
      simp only [List.getElem?_nil]
      symm
      rw [if_neg]
      rintro ⟨-, h⟩
      have : k * w ≤ (k + i) * w := Nat.mul_le_mul_right _ (by omega)
      omega

theorem Tree.get_singleton (t : Tree) (i : Nat) : t.get [i] = t.children[i]? := by
  have := t.get_append_singleton [] i
  simpa [Tree.get] using this

theorem build_get_child (W C h lo i : Nat) :
    (Tree.build W C (h + 1) lo).get [i] =
      if i < C ∧ lo + i * C ^ (h + 1) < W then some (Tree.build W C h (lo + i * C ^ (h + 1))) else none := by
  rw [Tree.get_singleton, build_children, buildChildren_getElem?]
  simp only [Nat.zero_add]

theorem build_version (W C h lo : Nat) : (Tree.build W C h lo).version = 0 := by
  cases h <;> rfl

theorem build_finished (W C h lo : Nat) : (Tree.build W C h lo).finished = 0 := by
  cases h <;> rfl

/-! ## Digits and paths -/

/-- The number whose base-`C` digits (most significant first) are `q`. -/
def digits (C : Nat) (q : List Nat) : Nat := q.foldl (fun acc k => acc * C + k) 0

theorem digits_append (C : Nat) (q : List Nat) (k : Nat) :
    digits C (q ++ [k]) = digits C q * C + k := by
  simp [digits, List.foldl_append]

private theorem pathAt_digits_rev (C : Nat) (hC : 0 < C) :
    ∀ (q : List Nat), (∀ k ∈ q, k < C) → pathAt C q.reverse.length (digits C q.reverse) = q.reverse
  | [], _ => by simp [pathAt, digits]
  | k :: q, hq => by
    have hk : k < C := hq k (by simp)
    have hq' : ∀ j ∈ q, j < C := fun j hj => hq j (by simp [hj])
    rw [List.reverse_cons, digits_append, List.length_append, List.length_singleton]
    simp only [pathAt]
    have h1 : (digits C q.reverse * C + k) / C = digits C q.reverse := by
      rw [Nat.mul_comm, Nat.mul_add_div hC, Nat.div_eq_of_lt hk, Nat.add_zero]
    have h2 : (digits C q.reverse * C + k) % C = k := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hk]
    rw [h1, h2, pathAt_digits_rev C hC q hq']

theorem pathAt_digits (C : Nat) (hC : 0 < C) (q : List Nat) (hq : ∀ k ∈ q, k < C) :
    pathAt C q.length (digits C q) = q := by
  have := pathAt_digits_rev C hC q.reverse (by simpa using hq)
  simpa using this

/-- `(j / C) * (w * C) + (j % C) * w = j * w` -/
theorem div_mod_mul (j C w : Nat) : j / C * (w * C) + j % C * w = j * w := by
  have h : j / C * (w * C) = j / C * C * w := by
    rw [Nat.mul_assoc, Nat.mul_comm w C]
  rw [h, ← Nat.add_mul]
  congr 1
  have := Nat.div_add_mod j C
  rw [Nat.mul_comm] at this
  omega

/-! ## Every node of a built tree -/

/-- The node at path `q` of `build H 0`, for `C ^ (H + 1) ≥ W`. -/
theorem get_build_char (W C H : Nat) (hpow : W ≤ C ^ (H + 1)) (hC : 0 < C) :
    ∀ q n, (Tree.build W C H 0).get q = some n →
      q.length ≤ H ∧ (∀ k ∈ q, k < C) ∧
        n = Tree.build W C (H - q.length) (digits C q * C ^ (H - q.length + 1)) := by
  suffices h : ∀ (q : List Nat) (n : Tree), (Tree.build W C H 0).get q.reverse = some n →
      q.reverse.length ≤ H ∧ (∀ k ∈ q.reverse, k < C) ∧
        n = Tree.build W C (H - q.reverse.length) (digits C q.reverse * C ^ (H - q.reverse.length + 1)) by
    intro q n hq
    have := h q.reverse n (by simpa using hq)
    simpa using this
  intro q
  induction q with
  | nil =>
    intro n hn
    simp [Tree.get] at hn
    simp [digits, ← hn]
  | cons k q ih =>
    intro n hn
    rw [List.reverse_cons, Tree.get_append_singleton] at hn
    cases hm : (Tree.build W C H 0).get q.reverse with
    | none => simp [hm] at hn
    | some m =>
      rw [hm, Option.bind_some] at hn
      obtain ⟨hlen, hdig, rfl⟩ := ih m hm
      rw [← Tree.get_singleton] at hn
      cases hHq : H - q.reverse.length with
      | zero =>
        rw [hHq] at hn
        simp [Tree.build, Tree.get] at hn
      | succ h =>
        rw [hHq] at hn
        rw [build_get_child] at hn
        split at hn
        · rename_i hcond
          obtain ⟨hk, hlt⟩ := hcond
          simp only [Option.some.injEq] at hn
          subst hn
          rw [List.reverse_cons, List.length_append, List.length_singleton, digits_append]
          refine ⟨by omega, ?_, ?_⟩
          · intro j hj
            simp at hj
            rcases hj with hj | rfl
            · exact hdig j (List.mem_reverse.mpr hj)
            · exact hk
          · have e1 : H - (q.reverse.length + 1) = h := by omega
            have e2 : H - q.reverse.length + 1 = h + 1 + 1 := by omega
            simp only [e1, e2]
            congr 1
            rw [Nat.add_mul]
            congr 1
            rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm (C ^ (h + 1)) C]
        · simp at hn

/-! ## The consumer's leaf -/

theorem Cursor.start_path (cfg : Config) (id : Nat) :
    (Cursor.start cfg id).path = pathAt cfg.cluster (rootHeight cfg) (id / cfg.cluster) := rfl

/-- Walking down the digits of `j` from the root reaches `build (H - d)` at
`j * C ^ (H - d + 1)`. -/
theorem get_pathAt (W C H : Nat) (hpow : W ≤ C ^ (H + 1)) (hC : 0 < C) :
    ∀ d j, d ≤ H → j * C ^ (H - d + 1) < W →
      (Tree.build W C H 0).get (pathAt C d j) = some (Tree.build W C (H - d) (j * C ^ (H - d + 1)))
  | 0, j, _, hj => by
    have hj0 : j = 0 := by
      by_cases h : j = 0
      · exact h
      · exfalso
        have : 1 * C ^ (H - 0 + 1) ≤ j * C ^ (H - 0 + 1) := Nat.mul_le_mul_right _ (by omega)
        simp only [Nat.sub_zero, Nat.one_mul] at this hj
        omega
    subst hj0
    simp [pathAt, Tree.get]
  | d + 1, j, hd, hj => by
    simp only [pathAt]
    rw [Tree.get_append_singleton]
    have e : H - d = H - (d + 1) + 1 := by omega
    have hj' : j / C * C ^ (H - d + 1) < W := by
      have hw : C ^ (H - d + 1) = C ^ (H - (d + 1) + 1) * C := by rw [e, Nat.pow_succ]
      rw [hw, Nat.mul_comm (C ^ (H - (d + 1) + 1)) C, ← Nat.mul_assoc]
      have h2 : j / C * C * C ^ (H - (d + 1) + 1) ≤ j * C ^ (H - (d + 1) + 1) :=
        Nat.mul_le_mul_right _ (Nat.div_mul_le_self j C)
      omega
    rw [get_pathAt W C H hpow hC d (j / C) (by omega) hj', Option.bind_some, ← Tree.get_singleton, e,
      build_get_child]
    have key := div_mod_mul j C (C ^ (H - (d + 1) + 1))
    rw [Nat.pow_succ]
    rw [if_pos ⟨Nat.mod_lt _ hC, by rw [key]; exact hj⟩, key]

theorem init_leaves (cfg : Config) (hC : 2 ≤ cfg.cluster) :
    ∀ id, id < cfg.workers → ∃ leaf, (Tree.init cfg).get (Cursor.start cfg id).path = some leaf ∧
      leaf.children = [] ∧ leaf.lo ≤ id ∧ id < leaf.hi := by
  intro id hid
  have hpow := rootHeight_pow cfg hC
  have hle : id / cfg.cluster * cfg.cluster ≤ id := Nat.div_mul_le_self _ _
  have := get_pathAt cfg.workers cfg.cluster (rootHeight cfg) hpow (by omega) (rootHeight cfg)
    (id / cfg.cluster) (Nat.le_refl _) (by simp only [Nat.sub_self, Nat.zero_add, Nat.pow_one]; omega)
  simp only [Nat.sub_self, Nat.zero_add, Nat.pow_one] at this
  refine ⟨_, this, rfl, ?_, ?_⟩
  · simp only [Tree.build, Tree.lo_mk]; exact hle
  · simp only [Tree.build, Tree.hi_mk]
    have h1 := Nat.div_add_mod id cfg.cluster
    have h2 := Nat.mod_lt id (show 0 < cfg.cluster by omega)
    rw [Nat.mul_comm] at h1
    omega

theorem init_leaf_unique (cfg : Config) (hC : 2 ≤ cfg.cluster) :
    ∀ q leaf, (Tree.init cfg).get q = some leaf → leaf.children = [] →
      ∀ id, leaf.lo ≤ id → id < leaf.hi → q = (Cursor.start cfg id).path := by
  intro q leaf hq hnil id hlo hhi
  have hpow := rootHeight_pow cfg hC
  obtain ⟨hlen, hdig, rfl⟩ := get_build_char cfg.workers cfg.cluster (rootHeight cfg) hpow (by omega) q leaf hq
  have hhiW := build_hi cfg.workers cfg.cluster (rootHeight cfg - q.length)
    (digits cfg.cluster q * cfg.cluster ^ (rootHeight cfg - q.length + 1))
  have hloq := build_lo cfg.workers cfg.cluster (rootHeight cfg - q.length)
    (digits cfg.cluster q * cfg.cluster ^ (rootHeight cfg - q.length + 1))
  -- a leaf: its height is 0, so the path has length `H`
  have h0 : rootHeight cfg - q.length = 0 := by
    cases hH : rootHeight cfg - q.length with
    | zero => rfl
    | succ h =>
      exfalso
      rw [hH] at hnil hloq hhiW hlo hhi
      rw [build_children] at hnil
      have hlt : digits cfg.cluster q * cfg.cluster ^ (h + 1 + 1) < cfg.workers := by
        rw [hloq] at hlo
        rw [hhiW] at hhi
        omega
      exact buildChildren_ne_nil _ _ _ _ _ _ (by omega) (by simpa using hlt) hnil
  rw [h0] at hlo hhi hloq hhiW
  simp only [Nat.zero_add, Nat.pow_one] at hlo hhi hloq hhiW
  have hlenH : q.length = rootHeight cfg := by omega
  rw [hloq] at hlo
  rw [hhiW] at hhi
  have hdiv : id / cfg.cluster = digits cfg.cluster q := by
    apply Nat.div_eq_of_lt_le
    · exact hlo
    · rw [Nat.add_mul, Nat.one_mul]; omega
  rw [Cursor.start_path, hdiv, ← hlenH, pathAt_digits cfg.cluster (by omega) q hdig]

/-! ## The invariant at the start -/

theorem init_treeInv (cfg : Config) (hW : 1 ≤ cfg.workers) (hC : 2 ≤ cfg.cluster) :
    TreeInv cfg 0 (fun _ => .start) (Tree.init cfg) := by
  have hpow := rootHeight_pow cfg hC
  have hwf := init_wf cfg hW hC
  have hchar := get_build_char cfg.workers cfg.cluster (rootHeight cfg) hpow (by omega)
  have hver : ∀ q n, (Tree.init cfg).get q = some n → n.version = 0 ∧ n.finished = 0 := by
    intro q n hq
    obtain ⟨-, -, rfl⟩ := hchar q n hq
    exact ⟨build_version _ _ _ _, build_finished _ _ _ _⟩
  have hcarried : ∀ q, carriedTo cfg.workers q (fun _ => .start) = 0 := by
    intro q
    unfold carriedTo
    exact sum_map_eq_zero _ _ fun _ _ => rfl
  refine ⟨?_, ?_, ?_, init_leaves cfg hC, init_leaf_unique cfg hC⟩
  · intro q n hq
    obtain ⟨hv, hf⟩ := hver q n hq
    have hwfn := Wf.get q hwf hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ _ h; simp at h
    · rw [hf]; exact hwfn.size_pos
    · omega
    · intro _; omega
    · intro _
      refine ⟨?_, ?_, ?_⟩
      · intro _ _ _; simp [leafDone, hv]
      · rw [hf, hv]
        symm
        apply sum_map_eq_zero
        intro _ _
        simp [pastLeaf, leafDone]
      · intro _ _ _ _ h; simp at h
    · intro hne _
      refine ⟨?_, ?_⟩
      · intro k hk
        obtain ⟨c, hc⟩ : ∃ c, (Tree.init cfg).get (q ++ [k]) = some c := by
          rw [get_child hq]
          exact ⟨_, List.getElem?_eq_getElem hk⟩
        obtain ⟨hcv, -⟩ := hver _ c hc
        exact ⟨c, hc, by omega, by omega⟩
      · rw [hf, hcarried]
        symm
        unfold filledBelow
        rw [hv]
        apply sum_map_eq_zero
        intro k hk
        cases hc : (Tree.init cfg).get (q ++ [k]) with
        | none => rfl
        | some c =>
          obtain ⟨hcv, -⟩ := hver _ c hc
          simp [filledOf, hcv]
    · intro _
      exact ⟨hv, hf, hcarried q⟩
  · intro _ _ _ _ h; simp at h
  · intro _ _ _ _ h; simp at h

end RearmBarrier
