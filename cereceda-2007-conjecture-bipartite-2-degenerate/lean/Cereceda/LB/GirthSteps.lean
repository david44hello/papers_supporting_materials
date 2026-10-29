/-
Cereceda/LB/GirthSteps.lean — Section 4 steps: winding well defined, Remark 4.5 colouring, the cycles of `J_n` (short v3.90 l. 595-679).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.LowerBound
import Cereceda.LB.GirthJ

namespace Cereceda

open SimpleGraph

namespace GirthSteps

/-! ### (A) Two height functions of the same colouring have the same steps -/

/-- Both steps are `±1` and agree mod `3`, so they are equal. -/
lemma step_eq {n k : ℕ} {c : Fin n ⊕ Fin k → Fin 4} {h h' : ℕ → ℤ} (hh : IsPathHeight c h)
    (hh' : IsPathHeight c h') (i : ℕ) (hi : i + 1 < n) : h (i + 1) - h i = h' (i + 1) - h' i := by
  obtain ⟨hs, hm⟩ := hh i hi
  obtain ⟨hs', hm'⟩ := hh' i hi
  rw [← hm'] at hm
  rcases hs with e | e <;> rcases hs' with e' | e' <;> rw [e, e'] at hm ⊢ <;> push_cast at hm <;>
    revert hm <;> decide

/-- `h - h'` is constant on `0, …, n-1`. -/
lemma diff_const {n k : ℕ} {c : Fin n ⊕ Fin k → Fin 4} {h h' : ℕ → ℤ} (hh : IsPathHeight c h)
    (hh' : IsPathHeight c h') : ∀ i, i < n → h i - h' i = h 0 - h' 0
  | 0, _ => rfl
  | i + 1, hi => by
    have hstep := step_eq hh hh' i hi
    have hprev := diff_const hh hh' i (by omega)
    linarith

/-! ### (B) A plain proper colouring of `H_n` using `0, 1, 2` on the path, where `a` can move to `2` -/

/-- The path gets `0, 2, 1, 2, 1, …` (0-based index `0 ↦ 0`, odd `↦ 2`, even `≥ 2 ↦ 1`); both apices get `3`. -/
def remCol (n : ℕ) : Fin n ⊕ Fin 2 → Fin 4 :=
  Sum.elim (fun i => if i.val = 0 then 0 else if i.val % 2 = 1 then 2 else 1) (fun _ => 3)

lemma remCol_proper (n : ℕ) : IsProperFn (Hgraph n) (remCol n) := by
  rintro (i | i) (j | j) hij
  · change i.val + 1 = j.val ∨ j.val + 1 = i.val at hij
    simp only [remCol, Sum.elim_inl]
    split_ifs <;> first | decide | omega
  · simp only [remCol, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> decide
  · simp only [remCol, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> decide
  · exact (hij : False).elim

lemma remCol_plain (n : ℕ) : IsPlain (remCol n) := fun _ => rfl

lemma remCol_range (n : ℕ) (hn : 3 ≤ n) :
    ({0, 1, 2} : Set (Fin 4)) ⊆ Set.range (fun i => remCol n (Sum.inl i)) := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact ⟨⟨0, by omega⟩, by simp [remCol]⟩
  · exact ⟨⟨2, by omega⟩, by simp [remCol]⟩
  · exact ⟨⟨1, by omega⟩, by simp [remCol]⟩

/-- Every neighbour of `a = Sum.inr 0` is a path vertex with even 0-based index, coloured `0` or `1`, never `2`. -/
lemma remCol_apex (n : ℕ) : ∀ w, (Hgraph n).Adj (Sum.inr 0) w → remCol n w ≠ 2 := by
  rintro (i | i) hw
  · change (⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 0 at hw
    have hi : i.val % 2 = 0 := Fin.ext_iff.mp hw
    simp only [remCol, Sum.elim_inl]
    split_ifs <;> first | decide | omega
  · exact (hw : False).elim

/-! ### (C) Every cycle of `J_n` meets an apex -/

/-- The index of a path vertex (apices get `0`; only used on path vertices). -/
def idx {n : ℕ} : Fin n ⊕ Fin 4 → ℕ := Sum.elim (fun i => i.val) (fun _ => 0)

/-- A cycle that starts at a path vertex of largest index and uses only path vertices is impossible: its second and
its second-to-last vertex are both the path vertex just below the start. -/
lemma not_cycle_at_max {n : ℕ} {v : Fin n ⊕ Fin 4} (c : (Jgraph n).Walk v v) (hc : c.IsCycle)
    (hS : ∀ x ∈ c.support, ∃ i, x = Sum.inl i ∧ idx x ≤ idx v) : False := by
  obtain ⟨a, rfl, -⟩ := hS _ c.start_mem_support
  have h3 := hc.three_le_length
  have hadj1 : (Jgraph n).Adj (Sum.inl a) (c.getVert 1) := by
    simpa using c.adj_getVert_succ (i := 0) (by omega)
  have hadj2 : (Jgraph n).Adj (c.getVert (c.length - 1)) (Sum.inl a) := by
    have := c.adj_getVert_succ (i := c.length - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega), Walk.getVert_length] at this
  have heq : c.getVert 1 = c.getVert (c.length - 1) := by
    obtain ⟨b1, hb1, hb1le⟩ := hS _ (c.getVert_mem_support 1)
    obtain ⟨b2, hb2, hb2le⟩ := hS _ (c.getVert_mem_support (c.length - 1))
    rw [hb1] at hadj1 hb1le ⊢
    rw [hb2] at hadj2 hb2le ⊢
    simp only [idx, Sum.elim_inl] at hb1le hb2le
    rw [GirthAux.Jgraph_adj_inl_inl] at hadj1 hadj2
    congr 1
    ext
    omega
  have := hc.getVert_injOn (by simp; omega) (by simp; omega) heq
  omega

/-! ### (C) A cycle through exactly one apex -/

/-- Along a walk whose vertices `1, …, length - 1` are path vertices, the index moves by `1` per step, so vertex `k`
is within `k - 1` of vertex `1`. -/
lemma idx_close {n : ℕ} {v : Fin n ⊕ Fin 4} (c : (Jgraph n).Walk v v)
    (hin : ∀ k, 1 ≤ k → k < c.length → ∃ i, c.getVert k = Sum.inl i) :
    ∀ k, 1 ≤ k → k < c.length →
      idx (c.getVert k) ≤ idx (c.getVert 1) + (k - 1) ∧ idx (c.getVert 1) ≤ idx (c.getVert k) + (k - 1)
  | 0, h1, _ => absurd h1 (by omega)
  | k + 1, _, hk => by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp
    · have ih := idx_close c hin k hpos (by omega)
      have hadj := c.adj_getVert_succ (i := k) (by omega)
      obtain ⟨a, ha⟩ := hin k hpos (by omega)
      obtain ⟨b, hb⟩ := hin (k + 1) (by omega) hk
      rw [ha, hb, GirthAux.Jgraph_adj_inl_inl] at hadj
      rw [ha] at ih
      rw [hb]
      simp only [idx, Sum.elim_inl] at ih ⊢
      omega

/-- A cycle at `a_j` meeting no other apex: its vertices `1` and `length - 1` are path vertices `v_p ≠ v_q`, both
joined to `a_j`, so `p ≡ q (mod 4)` and `|p - q| ≥ 4`; the path vertices between them give `|p - q| ≤ length - 2`. -/
lemma one_apex_at {n : ℕ} {j : Fin 4} (c : (Jgraph n).Walk (Sum.inr j) (Sum.inr j)) (hc : c.IsCycle)
    (hone : ∀ j' : Fin 4, Sum.inr j' ∈ c.support → j' = j) : 6 ≤ c.length := by
  have h3 := hc.three_le_length
  have hin : ∀ k, 1 ≤ k → k < c.length → ∃ i, c.getVert k = Sum.inl i := by
    intro k hk1 hk2
    rcases hv : c.getVert k with i | j'
    · exact ⟨i, rfl⟩
    · have hmem : Sum.inr j' ∈ c.support := by
        rw [← hv]
        exact c.getVert_mem_support k
      rw [hone j' hmem] at hv
      have := (hc.getVert_endpoint_iff (by omega)).mp hv
      omega
  obtain ⟨p, hp⟩ := hin 1 le_rfl (by omega)
  obtain ⟨q, hq⟩ := hin (c.length - 1) (by omega) (by omega)
  have hpq : p.val ≠ q.val := by
    intro hpq
    have h1 : c.getVert 1 = c.getVert (c.length - 1) := by rw [hp, hq, Fin.ext hpq]
    have := hc.getVert_injOn (by simp; omega) (by simp; omega) h1
    omega
  have hadjp := c.adj_getVert_succ (i := 0) (by omega)
  rw [Walk.getVert_zero, zero_add, hp, GirthAux.Jgraph_adj_inr_inl] at hadjp
  have hadjq := c.adj_getVert_succ (i := c.length - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega), Walk.getVert_length, hq, GirthAux.Jgraph_adj_inl_inr] at hadjq
  have hcl := idx_close c hin (c.length - 1) (by omega) (by omega)
  rw [hp, hq] at hcl
  simp only [idx, Sum.elim_inl] at hcl
  omega

/-! ### (C) A cycle through two apices -/

/-- Two vertices two steps apart on a walk in `J_n` cannot be different apices: the vertex between them is a path
vertex, and a path vertex is joined to exactly one apex. -/
lemma apex_gap {n : ℕ} {x y : Fin n ⊕ Fin 4} (c : (Jgraph n).Walk x y) {k : ℕ} (hk : k + 2 ≤ c.length)
    {j j' : Fin 4} (h0 : c.getVert k = Sum.inr j) (h2 : c.getVert (k + 2) = Sum.inr j') : j = j' := by
  have ha := c.adj_getVert_succ (i := k) (by omega)
  have hb : (Jgraph n).Adj (c.getVert (k + 1)) (c.getVert (k + 2)) := c.adj_getVert_succ (by omega)
  rw [h0] at ha
  rw [h2] at hb
  obtain ⟨i, hi⟩ : ∃ i, c.getVert (k + 1) = Sum.inl i := by
    rcases hv : c.getVert (k + 1) with i | i
    · exact ⟨i, rfl⟩
    · rw [hv] at ha
      exact absurd ha (GirthAux.Jgraph_not_adj_inr_inr _ _)
  rw [hi, GirthAux.Jgraph_adj_inr_inl] at ha
  rw [hi, GirthAux.Jgraph_adj_inl_inr] at hb
  exact Fin.ext (by omega)

/-- A cycle at `a_j` through another apex `a_{j'}` at position `m`: `m ∉ {0, 1, 2}` and `m ∉ {L-2, L-1, L}`
(`L` = length) by `apex_gap` and the non-adjacency of apices, so `3 ≤ m ≤ L - 3`. -/
lemma two_apex_at {n : ℕ} {j j' : Fin 4} (hjj : j ≠ j') (c : (Jgraph n).Walk (Sum.inr j) (Sum.inr j))
    (hc : c.IsCycle) (hj' : Sum.inr j' ∈ c.support) : 6 ≤ c.length := by
  have h3 := hc.three_le_length
  obtain ⟨m, hm, hmL⟩ := Walk.mem_support_iff_exists_getVert.mp hj'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Walk.getVert_zero] at hm
    exact hjj (Sum.inr_injective hm)
  have hm1 : m ≠ 1 := by
    rintro rfl
    have hadj := c.adj_getVert_succ (i := 0) (by omega)
    rw [Walk.getVert_zero, zero_add, hm] at hadj
    exact GirthAux.Jgraph_not_adj_inr_inr _ _ hadj
  have hm2 : m ≠ 2 := by
    rintro rfl
    exact hjj (apex_gap c (k := 0) (by omega) (Walk.getVert_zero c) hm)
  have hmL0 : m ≠ c.length := by
    rintro rfl
    rw [Walk.getVert_length] at hm
    exact hjj (Sum.inr_injective hm)
  have hmL1 : m ≠ c.length - 1 := by
    intro hmeq
    have hadj := c.adj_getVert_succ (i := c.length - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega), Walk.getVert_length, ← hmeq, hm] at hadj
    exact GirthAux.Jgraph_not_adj_inr_inr _ _ hadj
  have hmL2 : m ≠ c.length - 2 := by
    intro hmeq
    have h2 : c.getVert (c.length - 2 + 2) = Sum.inr j := by
      rw [Nat.sub_add_cancel (by omega), Walk.getVert_length]
    have h0 : c.getVert (c.length - 2) = Sum.inr j' := by rw [← hmeq, hm]
    exact hjj (apex_gap c (by omega) h0 h2).symm
  omega

end GirthSteps

open GirthSteps

/-- Short v3.90 l. 595: "The *winding* of `c` is `W = h(ℓ) - h(1)`. It does not depend on the choice of `h`".
Any two height functions differ by a constant on the path, so all their differences agree. -/
theorem sec4_winding_well_defined_proved {n k : ℕ} (c : Fin n ⊕ Fin k → Fin 4) (h h' : ℕ → ℤ) (hh : IsPathHeight c h)
    (hh' : IsPathHeight c h') (i j : ℕ) (hi : i < n) (hj : j < n) : h i - h j = h' i - h' j := by
  have hci := diff_const hh hh' i hi
  have hcj := diff_const hh hh' j hj
  linarith

/-- Short v3.90 l. 667-668 (Remark 4.5): "here `a` and `b` can move when the path still uses three [colours]".
For `n ≥ 3` the plain proper colouring `0, 2, 1, 2, 1, …` of the path uses `0, 1, 2`, and `a` can move to `2`. -/
theorem rem_4_5_three_colours_move_proved (n : ℕ) (hn : 3 ≤ n) :
    ∃ c : Fin n ⊕ Fin 2 → Fin 4, IsProperFn (Hgraph n) c ∧ IsPlain c ∧
      ({0, 1, 2} : Set (Fin 4)) ⊆ Set.range (fun i => c (Sum.inl i)) ∧
      ∃ (j : Fin 2) (y : Fin 4), y ≠ 3 ∧ ∀ w, (Hgraph n).Adj (Sum.inr j) w → c w ≠ y :=
  ⟨remCol n, remCol_proper n, remCol_plain n, remCol_range n hn, 0, 2, by decide, remCol_apex n⟩

/-- Short v3.90 l. 675: "Since the path is acyclic, every cycle passes through some `a_j`".
Proof: rotate the cycle to start at its path vertex of largest index; see `GirthSteps.not_cycle_at_max`. -/
theorem sec4_J_cycle_meets_apex_proved (n : ℕ) {u : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk u u) (hw : w.IsCycle) :
    ∃ j : Fin 4, Sum.inr j ∈ w.support := by
  by_contra hno
  have hS : ∀ x ∈ w.support, ∃ i, x = Sum.inl i := by
    rintro (i | j) hx
    · exact ⟨i, rfl⟩
    · exact absurd ⟨j, hx⟩ hno
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image w.support.toFinset idx ⟨u, by simp⟩
  rw [List.mem_toFinset] at hv
  refine not_cycle_at_max (w.rotate v hv) (hw.rotate hv) fun x hx => ?_
  rw [Walk.mem_support_rotate_iff] at hx
  obtain ⟨i, rfl⟩ := hS x hx
  exact ⟨i, rfl, hmax _ (List.mem_toFinset.mpr hx)⟩

/-- Short v3.90 l. 675: "the `a_j` are pairwise non-adjacent". -/
theorem sec4_J_apices_nonadj_proved (n : ℕ) (j j' : Fin 4) : ¬ (Jgraph n).Adj (Sum.inr j) (Sum.inr j') :=
  GirthAux.Jgraph_not_adj_inr_inr j j'

/-- Short v3.90 l. 675-677: "A cycle through exactly one `a_j` is `a_j v_i ⋯ v_{i'} a_j` with `i < i'` and
`i ≡ i' ≡ j (mod 4)`, so `i' - i ≥ 4`, and its length is at least `6`".
Proof: rotate the cycle to start at `a_j`; see `GirthSteps.one_apex_at`. -/
theorem sec4_J_one_apex_cycle_proved (n : ℕ) {u : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk u u) (hw : w.IsCycle)
    (j : Fin 4) (hj : Sum.inr j ∈ w.support) (hone : ∀ j' : Fin 4, Sum.inr j' ∈ w.support → j' = j) :
    6 ≤ w.length := by
  have := one_apex_at (w.rotate _ hj) (hw.rotate hj)
    (fun j' hj' => hone j' ((Walk.mem_support_rotate_iff _ _ _).mp hj'))
  rwa [Walk.length_rotate] at this

/-- Short v3.90 l. 677-679: "A cycle through two or more of the `a_j` has at least two path vertices between any two
of the `a_j` that are consecutive on it (each path vertex is joined to exactly one `a_j`), so it has at least three
vertices for each `a_j` on it, and length at least `6`".
Proof: rotate the cycle to start at `a_j`; see `GirthSteps.two_apex_at`. -/
theorem sec4_J_two_apex_cycle_proved (n : ℕ) {u : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk u u) (hw : w.IsCycle)
    (j j' : Fin 4) (hjj : j ≠ j') (hj : Sum.inr j ∈ w.support) (hj' : Sum.inr j' ∈ w.support) :
    6 ≤ w.length := by
  have := two_apex_at hjj (w.rotate _ hj) (hw.rotate hj) ((Walk.mem_support_rotate_iff _ _ _).mpr hj')
  rwa [Walk.length_rotate] at this

end Cereceda
