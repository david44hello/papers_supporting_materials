/-
LeeDiam/Sec4/Tame.lean — Section 4 helpers: merging two walks along a schedule, and the tame walks of Lemmas 4.8-4.10
(sec_chain.tex v1.50 l. 77-129).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Comb

namespace LeeDiam.S4

open Finset Band

section Merge2

variable {P : Type}

/-- The states of two walks merged along the schedule `(w t, v t)`, `t = 0, …, M`: the union of the state of `W`
reached after `w t` moves and the state of `V` reached after `v t` moves. -/
def merge2 (W V : List (Set P)) (w v : ℕ → ℕ) (M : ℕ) : List (Set P) :=
  (List.range (M + 1)).map (fun t => W.getD (w t) ∅ ∪ V.getD (v t) ∅)

theorem merge2_length (W V : List (Set P)) (w v : ℕ → ℕ) (M : ℕ) : (merge2 W V w v M).length = M + 1 := by
  simp [merge2]

/-- A schedule moves by `0` or `1`, so it is monotone. -/
theorem sched_le {f : ℕ → ℕ} {M : ℕ} (hf : ∀ t < M, f (t + 1) = f t ∨ f (t + 1) = f t + 1) {t : ℕ}
    (ht : t ≤ M) : f t ≤ f M := by
  have key : ∀ d, t + d ≤ M → f t ≤ f (t + d) := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hd
      have h1 := ih (by omega)
      have h2 := hf (t + d) (by omega)
      show f t ≤ f (t + d + 1)
      omega
  have := key (M - t) (by omega)
  rwa [Nat.add_sub_cancel' ht] at this

theorem getD_mem_of_le {W : List (Set P)} (hW : W ≠ []) {m : ℕ} (hm : m ≤ W.length - 1) : W.getD m ∅ ∈ W := by
  have := List.length_pos_of_ne_nil hW
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact List.getElem_mem _

theorem mem_of_mem_getD {W : List (Set P)} {i : ℕ} {x : P} (hx : x ∈ W.getD i ∅) : ∃ X ∈ W, x ∈ X := by
  rw [List.getD_eq_getElem?_getD] at hx
  cases h : W[i]? with
  | none => simp [h] at hx
  | some X =>
    rw [h] at hx
    exact ⟨X, List.mem_of_getElem? h, hx⟩

variable [PartialOrder P]

theorem walk_move_conn {W : List (Set P)} (hW : IsWalk W) {m : ℕ} (hm : m + 1 < W.length) :
    IsConnSet (symmDiff (W.getD m ∅) (W.getD (m + 1) ∅)) := by
  have hc := hW.2.2
  rw [List.isChain_iff_getElem] at hc
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem hm]
  exact hc m hm

omit [PartialOrder P] in
theorem symmDiff_union_union {X X' Y Y' : Set P} (h1 : Disjoint X Y) (h2 : Disjoint X Y') (h3 : Disjoint X' Y)
    (h4 : Disjoint X' Y') : symmDiff (X ∪ Y) (X' ∪ Y') = symmDiff X X' ∪ symmDiff Y Y' := by
  ext z
  have e1 : z ∈ X → z ∉ Y := fun hz => Set.disjoint_left.1 h1 hz
  have e2 : z ∈ X → z ∉ Y' := fun hz => Set.disjoint_left.1 h2 hz
  have e3 : z ∈ X' → z ∉ Y := fun hz => Set.disjoint_left.1 h3 hz
  have e4 : z ∈ X' → z ∉ Y' := fun hz => Set.disjoint_left.1 h4 hz
  simp only [Set.mem_symmDiff, Set.mem_union]
  tauto

omit [PartialOrder P] in
theorem headD_of_head? {W : List (Set P)} {A : Set P} (h : W.head? = some A) : W.getD 0 ∅ = A := by
  rw [getD_zero_eq_headD, List.headD_eq_head?_getD, h]
  rfl

omit [PartialOrder P] in
theorem lastD_of_getLast? {W : List (Set P)} {B : Set P} (h : W.getLast? = some B) :
    W.getD (W.length - 1) ∅ = B := by
  rw [getD_last_eq_getLastD, List.getLastD_eq_getLast?, h]
  rfl

/-- Two walks with disjoint states, merged along a schedule in which every step moves at least one of them, form a
walk, provided the merged states are antichains and every step that moves both has a comparable pair across. -/
theorem merge2_walk {W V : List (Set P)} {A B A' B' : Set P} (hW : IsWalkFromTo W A B) (hV : IsWalkFromTo V A' B')
    {w v : ℕ → ℕ} {M : ℕ} (hw0 : w 0 = 0) (hv0 : v 0 = 0) (hwM : w M = W.length - 1) (hvM : v M = V.length - 1)
    (hws : ∀ t < M, w (t + 1) = w t ∨ w (t + 1) = w t + 1) (hvs : ∀ t < M, v (t + 1) = v t ∨ v (t + 1) = v t + 1)
    (hmove : ∀ t < M, w (t + 1) = w t + 1 ∨ v (t + 1) = v t + 1)
    (hdisj : ∀ X ∈ W, ∀ Y ∈ V, Disjoint X Y)
    (hanti : ∀ t ≤ M, ∀ x ∈ W.getD (w t) ∅, ∀ y ∈ V.getD (v t) ∅, ¬ Comp x y)
    (hboth : ∀ t < M, w (t + 1) = w t + 1 → v (t + 1) = v t + 1 →
      ∃ x ∈ symmDiff (W.getD (w t) ∅) (W.getD (w t + 1) ∅),
        ∃ y ∈ symmDiff (V.getD (v t) ∅) (V.getD (v t + 1) ∅), Comp x y) :
    IsWalkFromTo (merge2 W V w v M) (A ∪ A') (B ∪ B') := by
  obtain ⟨hWw, hWh, hWl⟩ := hW
  obtain ⟨hVw, hVh, hVl⟩ := hV
  have hWm : ∀ t ≤ M, W.getD (w t) ∅ ∈ W := fun t ht => getD_mem_of_le hWw.1 (hwM ▸ sched_le hws ht)
  have hVm : ∀ t ≤ M, V.getD (v t) ∅ ∈ V := fun t ht => getD_mem_of_le hVw.1 (hvM ▸ sched_le hvs ht)
  have hWlen := List.length_pos_of_ne_nil hWw.1
  have hVlen := List.length_pos_of_ne_nil hVw.1
  refine ⟨⟨by simp [merge2], ?_, ?_⟩, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hZ
    have ht' := List.mem_range.1 ht
    exact isAntichainSet_union (hWw.2.1 _ (hWm t (by omega))) (hVw.2.1 _ (hVm t (by omega)))
      (hanti t (by omega))
  · rw [List.isChain_iff_getElem]
    intro t ht
    simp only [merge2, List.length_map, List.length_range] at ht
    simp only [merge2, List.getElem_map, List.getElem_range]
    have hWt := hWm t (by omega)
    have hWt1 := hWm (t + 1) (by omega)
    have hVt := hVm t (by omega)
    have hVt1 := hVm (t + 1) (by omega)
    have hwle := sched_le hws (t := t + 1) (by omega)
    have hvle := sched_le hvs (t := t + 1) (by omega)
    rw [symmDiff_union_union (hdisj _ hWt _ hVt) (hdisj _ hWt _ hVt1) (hdisj _ hWt1 _ hVt) (hdisj _ hWt1 _ hVt1)]
    rcases hws t (by omega) with hw | hw <;> rcases hvs t (by omega) with hv | hv
    · exact absurd (hmove t (by omega)) (by omega)
    · rw [hw, symmDiff_self, Set.bot_eq_empty, Set.empty_union, hv]
      exact walk_move_conn hVw (by omega)
    · rw [hv, symmDiff_self, Set.bot_eq_empty, Set.union_empty, hw]
      exact walk_move_conn hWw (by omega)
    · obtain ⟨x, hx, y, hy, hxy⟩ := hboth t (by omega) hw hv
      rw [hw, hv]
      exact isConnSet_union (walk_move_conn hWw (by omega)) (walk_move_conn hVw (by omega)) hx hy hxy
  · simp only [merge2, List.range_succ_eq_map, List.map_cons, List.head?_cons, hw0, hv0, headD_of_head? hWh,
      headD_of_head? hVh]
  · simp only [merge2, List.getLast?_map, List.getLast?_range, Nat.add_one_ne_zero, ↓reduceIte, Option.map_some,
      Nat.add_sub_cancel, hwM, hvM, lastD_of_getLast? hWl, lastD_of_getLast? hVl]

end Merge2

section Merge2Trace

variable {k : ℕ}

theorem outerAt_union_left {X Y : Set (Band k)} {e : Fin k} (hX : ∀ x ∈ X, x.1 ≠ e) :
    outerAt (X ∪ Y) e = outerAt Y e := by
  have ha : a e ∉ X := fun h => hX _ h rfl
  have hc : c e ∉ X := fun h => hX _ h rfl
  by_cases h1 : a e ∈ Y
  · rw [outerAt_of_a_mem (Or.inr h1), outerAt_of_a_mem h1]
  · by_cases h2 : c e ∈ Y
    · rw [outerAt_of_c_mem (by simp [ha, h1]) (Or.inr h2), outerAt_of_c_mem h1 h2]
    · rw [outerAt_none (by simp [ha, h1]) (by simp [hc, h2]), outerAt_none h1 h2]

theorem outerAt_union_right {X Y : Set (Band k)} {e : Fin k} (hY : ∀ y ∈ Y, y.1 ≠ e) :
    outerAt (X ∪ Y) e = outerAt X e := by
  rw [Set.union_comm]
  exact outerAt_union_left hY

theorem map_outerAt_eq_range (V : List (Set (Band k))) (hV : V ≠ []) (e : Fin k) :
    V.map (outerAt · e) = (List.range (V.length - 1 + 1)).map (fun i => outerAt (V.getD i ∅) e) := by
  have hlen : V.length = V.length - 1 + 1 := by
    have := List.length_pos_of_ne_nil hV
    omega
  conv_lhs => rw [← map_range_getD V ∅, List.map_map]
  rw [← hlen]
  rfl

/-- At a column where `W` has no element, the merged walk has the outer trace of `V`. -/
theorem merge2_trace_right {W V : List (Set (Band k))} (hV : V ≠ []) {w v : ℕ → ℕ} {M : ℕ} (hv0 : v 0 = 0)
    (hvM : v M = V.length - 1) (hvs : ∀ t < M, v (t + 1) = v t ∨ v (t + 1) = v t + 1) {e : Fin k}
    (hWe : ∀ X ∈ W, ∀ x ∈ X, x.1 ≠ e) : outerTrace (merge2 W V w v M) e = outerTrace V e := by
  have hst := stretch_of_pos M (fun i => outerAt (V.getD i ∅) e) v (V.length - 1) hv0 hvM hvs
  unfold outerTrace merge2
  rw [List.map_map, map_outerAt_eq_range V hV e]
  have h1 : (List.range (M + 1)).map ((outerAt · e) ∘ fun t => W.getD (w t) ∅ ∪ V.getD (v t) ∅) =
      (List.range (M + 1)).map (fun t => (fun i => outerAt (V.getD i ∅) e) (v t)) := by
    refine List.map_congr_left fun t _ => ?_
    refine outerAt_union_left fun x hx => ?_
    obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hx
    exact hWe X hX x hxX
  rw [h1]
  exact stretch_destutter hst

/-- At a column where `V` has no element, the merged walk has the outer trace of `W`. -/
theorem merge2_trace_left {W V : List (Set (Band k))} (hW : W ≠ []) {w v : ℕ → ℕ} {M : ℕ} (hw0 : w 0 = 0)
    (hwM : w M = W.length - 1) (hws : ∀ t < M, w (t + 1) = w t ∨ w (t + 1) = w t + 1) {e : Fin k}
    (hVe : ∀ Y ∈ V, ∀ y ∈ Y, y.1 ≠ e) : outerTrace (merge2 W V w v M) e = outerTrace W e := by
  have hst := stretch_of_pos M (fun i => outerAt (W.getD i ∅) e) w (W.length - 1) hw0 hwM hws
  unfold outerTrace merge2
  rw [List.map_map, map_outerAt_eq_range W hW e]
  have h1 : (List.range (M + 1)).map ((outerAt · e) ∘ fun t => W.getD (w t) ∅ ∪ V.getD (v t) ∅) =
      (List.range (M + 1)).map (fun t => (fun i => outerAt (W.getD i ∅) e) (w t)) := by
    refine List.map_congr_left fun t _ => ?_
    refine outerAt_union_right fun y hy => ?_
    obtain ⟨Y, hY, hyY⟩ := mem_of_mem_getD hy
    exact hVe Y hY y hyY
  rw [h1]
  exact stretch_destutter hst

end Merge2Trace

section Bases

variable {k : ℕ}

theorem a_val2 (i : Fin k) : (a i).2.val = 0 := rfl
theorem b_val2 (i : Fin k) : (b i).2.val = 1 := rfl
theorem c_val2 (i : Fin k) : (c i).2.val = 2 := rfl

/-- Comparabilities used by the tame walks, for columns `i` and `j = i + 1`. -/
theorem comp_ab_same (i : Fin k) : Comp (a i) (b i) := by
  rw [comp_iff_val, a_val2, b_val2, a_fst, b_fst]
  omega
theorem comp_ac_same (i : Fin k) : Comp (a i) (c i) := by
  rw [comp_iff_val, a_val2, c_val2, a_fst, c_fst]
  omega
theorem comp_bc_same (i : Fin k) : Comp (b i) (c i) := by
  rw [comp_iff_val, b_val2, c_val2, b_fst, c_fst]
  omega
theorem comp_ac_next {i j : Fin k} (h : j.val = i.val + 1) : Comp (a i) (c j) := by
  rw [comp_iff_val, a_val2, c_val2, a_fst, c_fst]
  omega
theorem comp_ca_next {i j : Fin k} (h : j.val = i.val + 1) : Comp (c i) (a j) := by
  rw [comp_iff_val, c_val2, a_val2, c_fst, a_fst]
  omega
theorem comp_bc_prev {i j : Fin k} (h : j.val = i.val + 1) : Comp (b j) (c i) := by
  rw [comp_iff_val, b_val2, c_val2, b_fst, c_fst]
  omega
theorem comp_ba_prev {i j : Fin k} (h : j.val = i.val + 1) : Comp (b j) (a i) := by
  rw [comp_iff_val, b_val2, a_val2, b_fst, a_fst]
  omega

theorem ne_of_val {x y : Band k} (h : x.1.val ≠ y.1.val ∨ x.2.val ≠ y.2.val) : x ≠ y := by
  rintro rfl
  omega

/-- A set in which every element is comparable to one element `x₀` of it is connected. -/
theorem isConnSet_star {P : Type} [PartialOrder P] {D : Set P} {x₀ : P} (hx₀ : x₀ ∈ D)
    (h : ∀ y ∈ D, y = x₀ ∨ Comp x₀ y) : IsConnSet D := by
  refine isConnSet_of_rtg hx₀ fun y hy => ?_
  rcases h y hy with rfl | hc
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hx₀, hy, hc⟩

theorem isAntichainSet_singleton' (x : Band k) : IsAntichainSet ({x} : Set (Band k)) :=
  isAntichainSet_row x.2 _ fun y hy => by rw [Set.mem_singleton_iff.1 hy]

theorem isAntichainSet_pair_row {x y : Band k} (h : x.2 = y.2) : IsAntichainSet ({x, y} : Set (Band k)) :=
  isAntichainSet_row x.2 _ fun z hz => by
    rcases hz with rfl | hz
    · rfl
    · rw [Set.mem_singleton_iff.1 hz, h]

/-- The tame base on one column: `b → c → -` (line 1 of Table 1), tame at that column with outer element `c`. -/
theorem base_one_walk (e : Fin k) :
    IsWalkFromTo [{b e}, {c e}, ∅] {b e} ∅ ∧ IsTameAt [{b e}, {c e}, ∅] e (c e) := by
  have hbc : b e ≠ c e := b_ne_c e e
  refine ⟨⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩, ?_, rfl, by show (2 : Fin 3) ≠ 1; decide, ?_⟩
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl
    · exact isAntichainSet_singleton' _
    · exact isAntichainSet_singleton' _
    · exact isAntichainSet_row 0 _ (by simp)
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    refine ⟨?_, ?_⟩
    · have : symmDiff ({b e} : Set (Band k)) {c e} = {b e, c e} := by
        ext z
        simp only [Set.mem_symmDiff, Set.mem_singleton_iff, Set.mem_insert_iff]
        constructor
        · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩) <;> simp
        · rintro (rfl | rfl)
          · exact Or.inl ⟨rfl, hbc⟩
          · exact Or.inr ⟨rfl, hbc.symm⟩
      rw [this]
      exact isConnSet_pair (comp_bc_same e)
    · rw [← Set.bot_eq_empty, symmDiff_bot]
      exact isConnSet_singleton _
  · intro X hX x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_rfl
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_rfl
    · exact absurd hx (Set.notMem_empty x)
  · unfold outerTrace
    simp only [List.map_cons, List.map_nil]
    have h1 : outerAt ({b e} : Set (Band k)) e = none :=
      outerAt_none (by simpa using a_ne_b e e) (by simpa using (b_ne_c e e).symm)
    have h2 : outerAt ({c e} : Set (Band k)) e = some (c e) :=
      outerAt_of_c_mem (by simpa using a_ne_c e e) (Set.mem_singleton _)
    have h4 : outerAt (∅ : Set (Band k)) e = none := outerAt_none (by simp) (by simp)
    rw [h1, h2, h4]
    exact List.destutter_of_isChain _ _ (by simp)

theorem symmDiff_of_disjoint {P : Type} [PartialOrder P] {X Y : Set P} (h : Disjoint X Y) :
    symmDiff X Y = X ∪ Y :=
  (symmDiff_eq_sup X Y).2 h

theorem disjoint_of_rows {X Y : Set (Band k)} {r r' : Fin 3} (hX : ∀ x ∈ X, x.2 = r) (hY : ∀ y ∈ Y, y.2 = r')
    (h : r ≠ r') : Disjoint X Y :=
  Set.disjoint_left.2 fun x hx hy => h ((hX x hx).symm.trans (hY x hy))

theorem rows1 (x : Band k) (r : Fin 3) (h : x.2 = r) : ∀ y ∈ ({x} : Set (Band k)), y.2 = r := fun y hy => by
  rw [Set.mem_singleton_iff.1 hy, h]

theorem rows2 (x y : Band k) (r : Fin 3) (hx : x.2 = r) (hy : y.2 = r) : ∀ z ∈ ({x, y} : Set (Band k)), z.2 = r :=
  fun z hz => by
    rcases hz with rfl | hz
    · exact hx
    · rw [Set.mem_singleton_iff.1 hz, hy]

theorem col_ne {x y : Band k} (h : x.1.val ≠ y.1.val) : x ≠ y := fun hxy => h (by rw [hxy])

theorem walk_four {X0 X1 X2 X3 : Set (Band k)} (h0 : IsAntichainSet X0) (h1 : IsAntichainSet X1)
    (h2 : IsAntichainSet X2) (h3 : IsAntichainSet X3) (c01 : IsConnSet (symmDiff X0 X1))
    (c12 : IsConnSet (symmDiff X1 X2)) (c23 : IsConnSet (symmDiff X2 X3)) :
    IsWalkFromTo [X0, X1, X2, X3] X0 X3 := by
  refine ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩
  · intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> assumption
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨c01, c12, c23⟩

/-- Line 2 of Table 1 on the columns `i`, `j = i + 1`: `-- → a- → cc → bb`, tame at `j` with outer element `c_j`. -/
theorem line2_walk {i j : Fin k} (hij : j.val = i.val + 1) :
    IsWalkFromTo [∅, {a i}, {c i, c j}, {b i, b j}] ∅ {b i, b j} ∧
      IsTameAt [∅, {a i}, {c i, c j}, {b i, b j}] j (c j) := by
  have hji : j ≠ i := fun h => by rw [h] at hij; omega
  have hcc : c j ≠ c i := fun h => hji (c_injective h)
  have haa : a j ≠ a i := fun h => hji (congrArg Prod.fst h)
  refine ⟨walk_four (isAntichainSet_row 0 _ (by simp)) (isAntichainSet_singleton' _)
    (isAntichainSet_pair_row rfl) (isAntichainSet_pair_row rfl) ?_ ?_ ?_, ?_, rfl,
    by show (2 : Fin 3) ≠ 1; decide, ?_⟩
  · rw [← Set.bot_eq_empty, bot_symmDiff]
    exact isConnSet_singleton _
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows1 (a i) 0 rfl) (rows2 (c i) (c j) 2 rfl rfl) (by decide))]
    refine isConnSet_star (x₀ := a i) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (comp_ac_same i)
    · exact Or.inr (comp_ac_next hij)
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows2 (c i) (c j) 2 rfl rfl) (rows2 (b i) (b j) 1 rfl rfl) (by decide))]
    refine isConnSet_of_rtg (x0 := b j) (by simp) fun y hy => ?_
    have hm : ∀ z, z = c i ∨ z = c j ∨ z = b i ∨ z = b j → z ∈ ({c i, c j} ∪ {b i, b j} : Set (Band k)) := by
      rintro z (rfl | rfl | rfl | rfl) <;> simp
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (rfl | rfl) | (rfl | rfl)
    · exact Relation.ReflTransGen.single ⟨hm _ (by simp), hm _ (by simp), comp_bc_prev hij⟩
    · exact Relation.ReflTransGen.single ⟨hm _ (by simp), hm _ (by simp), comp_bc_same j⟩
    · exact (Relation.ReflTransGen.single ⟨hm _ (by simp), hm _ (by simp), comp_bc_prev hij⟩).tail
        ⟨hm _ (by simp), hm _ (by simp), comp_symm (comp_bc_same i)⟩
    · exact Relation.ReflTransGen.refl
  · have hle : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    intro X hX x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact absurd hx (Set.notMem_empty x)
    · rw [Set.mem_singleton_iff.1 hx]
      exact hle
    · rcases hx with rfl | hx
      · exact hle
      · rw [Set.mem_singleton_iff.1 hx]
        exact le_rfl
    · rcases hx with rfl | hx
      · exact hle
      · rw [Set.mem_singleton_iff.1 hx]
        exact le_rfl
  · unfold outerTrace
    simp only [List.map_cons, List.map_nil]
    have e0 : outerAt (∅ : Set (Band k)) j = none := outerAt_none (by simp) (by simp)
    have e1 : outerAt ({a i} : Set (Band k)) j = none :=
      outerAt_none (by simp [haa]) (by simp [(a_ne_c i j).symm])
    have e2 : outerAt ({c i, c j} : Set (Band k)) j = some (c j) :=
      outerAt_of_c_mem (by simp [a_ne_c]) (by simp)
    have e3 : outerAt ({b i, b j} : Set (Band k)) j = none :=
      outerAt_none (by simp [a_ne_b]) (by simp [(b_ne_c _ _).symm])
    rw [e0, e1, e2, e3]
    exact (destutter_eq_three_iff (by simp) (by simp) _).2 ⟨2, 1, 1, by omega, le_rfl, le_rfl, rfl⟩

/-- Line 3 of Table 1 on the columns `i`, `j = i + 1`: `b- → a- → cc → -b`, tame at `j` with outer element `c_j`. -/
theorem line3_walk {i j : Fin k} (hij : j.val = i.val + 1) :
    IsWalkFromTo [{b i}, {a i}, {c i, c j}, {b j}] {b i} {b j} ∧
      IsTameAt [{b i}, {a i}, {c i, c j}, {b j}] j (c j) := by
  have hji : j ≠ i := fun h => by rw [h] at hij; omega
  have haa : a j ≠ a i := fun h => hji (congrArg Prod.fst h)
  have hbb : b j ≠ b i := fun h => hji (congrArg Prod.fst h)
  refine ⟨walk_four (isAntichainSet_singleton' _) (isAntichainSet_singleton' _)
    (isAntichainSet_pair_row rfl) (isAntichainSet_singleton' _) ?_ ?_ ?_, ?_, rfl,
    by show (2 : Fin 3) ≠ 1; decide, ?_⟩
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows1 (b i) 1 rfl) (rows1 (a i) 0 rfl) (by decide))]
    refine isConnSet_star (x₀ := a i) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Or.inr (comp_ab_same i)
    · exact Or.inl rfl
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows1 (a i) 0 rfl) (rows2 (c i) (c j) 2 rfl rfl) (by decide))]
    refine isConnSet_star (x₀ := a i) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (comp_ac_same i)
    · exact Or.inr (comp_ac_next hij)
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows2 (c i) (c j) 2 rfl rfl) (rows1 (b j) 1 rfl) (by decide))]
    refine isConnSet_star (x₀ := b j) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (rfl | rfl) | rfl
    · exact Or.inr (comp_bc_prev hij)
    · exact Or.inr (comp_bc_same j)
    · exact Or.inl rfl
  · have hle : i ≤ j := Fin.le_iff_val_le_val.2 (by omega)
    intro X hX x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · rw [Set.mem_singleton_iff.1 hx]
      exact hle
    · rw [Set.mem_singleton_iff.1 hx]
      exact hle
    · rcases hx with rfl | hx
      · exact hle
      · rw [Set.mem_singleton_iff.1 hx]
        exact le_rfl
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_rfl
  · unfold outerTrace
    simp only [List.map_cons, List.map_nil]
    have e0 : outerAt ({b i} : Set (Band k)) j = none :=
      outerAt_none (by simp [a_ne_b]) (by simp [(b_ne_c _ _).symm])
    have e1 : outerAt ({a i} : Set (Band k)) j = none :=
      outerAt_none (by simp [haa]) (by simp [(a_ne_c i j).symm])
    have e2 : outerAt ({c i, c j} : Set (Band k)) j = some (c j) :=
      outerAt_of_c_mem (by simp [a_ne_c]) (by simp)
    have e3 : outerAt ({b j} : Set (Band k)) j = none :=
      outerAt_none (by simp [a_ne_b]) (by simp [(b_ne_c _ _).symm])
    rw [e0, e1, e2, e3]
    exact (destutter_eq_three_iff (by simp) (by simp) _).2 ⟨2, 1, 1, by omega, le_rfl, le_rfl, rfl⟩

/-- The walk `-b → aa → c- → b-` on the columns `q`, `r = q + 1` (proof of Lemma 4.9, `b_{i+2}` initial), tame at
`r` with outer element `a_r`. -/
theorem line4_walk {q r : Fin k} (hqr : r.val = q.val + 1) :
    IsWalkFromTo [{b r}, {a q, a r}, {c q}, {b q}] {b r} {b q} ∧
      IsTameAt [{b r}, {a q, a r}, {c q}, {b q}] r (a r) := by
  have hrq : r ≠ q := fun h => by rw [h] at hqr; omega
  have hcc : c r ≠ c q := fun h => hrq (c_injective h)
  refine ⟨walk_four (isAntichainSet_singleton' _) (isAntichainSet_pair_row rfl) (isAntichainSet_singleton' _)
    (isAntichainSet_singleton' _) ?_ ?_ ?_, ?_, rfl, by show (0 : Fin 3) ≠ 1; decide, ?_⟩
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows1 (b r) 1 rfl) (rows2 (a q) (a r) 0 rfl rfl) (by decide))]
    refine isConnSet_star (x₀ := b r) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (comp_ba_prev hqr)
    · exact Or.inr (comp_symm (comp_ab_same r))
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows2 (a q) (a r) 0 rfl rfl) (rows1 (c q) 2 rfl) (by decide))]
    refine isConnSet_star (x₀ := c q) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with (rfl | rfl) | rfl
    · exact Or.inr (comp_symm (comp_ac_same q))
    · exact Or.inr (comp_ca_next hqr)
    · exact Or.inl rfl
  · rw [symmDiff_of_disjoint (disjoint_of_rows (rows1 (c q) 2 rfl) (rows1 (b q) 1 rfl) (by decide))]
    refine isConnSet_star (x₀ := c q) (by simp) fun y hy => ?_
    simp only [Set.mem_union, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (comp_symm (comp_bc_same q))
  · have hle : q ≤ r := Fin.le_iff_val_le_val.2 (by omega)
    intro X hX x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_rfl
    · rcases hx with rfl | hx
      · exact hle
      · rw [Set.mem_singleton_iff.1 hx]
        exact le_rfl
    · rw [Set.mem_singleton_iff.1 hx]
      exact hle
    · rw [Set.mem_singleton_iff.1 hx]
      exact hle
  · unfold outerTrace
    simp only [List.map_cons, List.map_nil]
    have e0 : outerAt ({b r} : Set (Band k)) r = none :=
      outerAt_none (by simp [a_ne_b]) (by simp [(b_ne_c _ _).symm])
    have e1 : outerAt ({a q, a r} : Set (Band k)) r = some (a r) := outerAt_of_a_mem (by simp)
    have e2 : outerAt ({c q} : Set (Band k)) r = none := outerAt_none (by simp [a_ne_c]) (by simp [hcc])
    have e3 : outerAt ({b q} : Set (Band k)) r = none :=
      outerAt_none (by simp [a_ne_b]) (by simp [(b_ne_c _ _).symm])
    rw [e0, e1, e2, e3]
    exact (destutter_eq_three_iff (by simp) (by simp) _).2 ⟨1, 1, 2, le_rfl, le_rfl, by omega, rfl⟩

end Bases

section Splits

variable {P : Type} [PartialOrder P]

theorem split_singleton {A B : Set P} {x : P} (h : IsSplit A B {x}) : (A = {x} ∧ B = ∅) ∨ (A = ∅ ∧ B = {x}) := by
  obtain ⟨hdis, hU, -⟩ := h
  have hmem : ∀ z, z ∈ A ∨ z ∈ B ↔ z = x := fun z => by rw [← Set.mem_union, hU, Set.mem_singleton_iff]
  have hnot : ∀ z, z ∈ A → z ∉ B := fun z hA hB => Set.disjoint_left.1 hdis hA hB
  rcases (hmem x).2 rfl with hxA | hxB
  · left
    refine ⟨Set.ext fun z => ⟨fun hz => (hmem z).1 (Or.inl hz), fun hz => (Set.mem_singleton_iff.1 hz) ▸ hxA⟩,
      Set.ext fun z => ⟨fun hz => ?_, fun hz => absurd hz (Set.notMem_empty z)⟩⟩
    have := (hmem z).1 (Or.inr hz)
    subst this
    exact absurd hz (hnot _ hxA)
  · right
    refine ⟨Set.ext fun z => ⟨fun hz => ?_, fun hz => absurd hz (Set.notMem_empty z)⟩,
      Set.ext fun z => ⟨fun hz => (hmem z).1 (Or.inr hz), fun hz => (Set.mem_singleton_iff.1 hz) ▸ hxB⟩⟩
    have := (hmem z).1 (Or.inl hz)
    subst this
    exact absurd hxB (hnot _ hz)

theorem split_pair {A B : Set P} {x y : P} (hxy : x ≠ y) (h : IsSplit A B {x, y}) :
    (A = ∅ ∧ B = {x, y}) ∨ (A = {x} ∧ B = {y}) ∨ (A = {y} ∧ B = {x}) ∨ (A = {x, y} ∧ B = ∅) := by
  obtain ⟨hdis, hU, -⟩ := h
  have hmem : ∀ z, z ∈ A ∨ z ∈ B ↔ z = x ∨ z = y := fun z => by
    rw [← Set.mem_union, hU, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hnot : ∀ z, z ∈ A → z ∉ B := fun z hA hB => Set.disjoint_left.1 hdis hA hB
  have hA : ∀ z, z ∈ A ↔ (z = x ∧ x ∈ A) ∨ (z = y ∧ y ∈ A) := by
    intro z
    constructor
    · intro hz
      rcases (hmem z).1 (Or.inl hz) with rfl | rfl
      · exact Or.inl ⟨rfl, hz⟩
      · exact Or.inr ⟨rfl, hz⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> exact h
  have hB : ∀ z, z ∈ B ↔ (z = x ∧ x ∉ A) ∨ (z = y ∧ y ∉ A) := by
    intro z
    constructor
    · intro hz
      rcases (hmem z).1 (Or.inr hz) with rfl | rfl
      · exact Or.inl ⟨rfl, fun h => hnot _ h hz⟩
      · exact Or.inr ⟨rfl, fun h => hnot _ h hz⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact ((hmem z).2 (Or.inl rfl)).resolve_left h
      · exact ((hmem z).2 (Or.inr rfl)).resolve_left h
  by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
  · right; right; right
    exact ⟨Set.ext fun z => by rw [hA z]; simp [hxA, hyA], Set.ext fun z => by rw [hB z]; simp [hxA, hyA]⟩
  · right; left
    exact ⟨Set.ext fun z => by rw [hA z]; simp [hxA, hyA], Set.ext fun z => by rw [hB z]; simp [hxA, hyA]⟩
  · right; right; left
    exact ⟨Set.ext fun z => by rw [hA z]; simp [hxA, hyA], Set.ext fun z => by rw [hB z]; simp [hxA, hyA]⟩
  · left
    exact ⟨Set.ext fun z => by rw [hA z]; simp [hxA, hyA], Set.ext fun z => by rw [hB z]; simp [hxA, hyA]⟩

end Splits

section TameBases

variable {k : ℕ}

theorem tame_cols_le {W : List (Set (Band k))} {i : Fin k} {h : Band k} (hT : IsTameAt W i h) :
    ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ i.val := fun X hX x hx => Fin.le_iff_val_le_val.1 (hT.1 X hX x hx)

/-- Lemma 4.8, one column. -/
theorem tame_base_one (hk : 1 ≤ k) (A B : Set (Band k)) (hAB : IsSplit A B {b ⟨0, hk⟩}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = 2 ∧ IsTameAt W ⟨0, hk⟩ h ∧ ∀ X ∈ W, ∀ x ∈ X, x.1.val = 0 := by
  obtain ⟨hW, hT⟩ := base_one_walk (k := k) ⟨0, hk⟩
  rcases split_singleton hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, hW, rfl, hT, fun X hX x hx => Nat.le_zero.1 (tame_cols_le hT X hX x hx)⟩
  · exact ⟨_, _, isWalkFromTo_reverse hW, rfl, tame_reverse hT,
      fun X hX x hx => Nat.le_zero.1 (tame_cols_le (tame_reverse hT) X hX x hx)⟩

/-- Lemma 4.8, two columns. -/
theorem tame_base_two (hk : 2 ≤ k) (A B : Set (Band k)) (hAB : IsSplit A B {b ⟨0, by omega⟩, b ⟨1, hk⟩}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = 3 ∧ IsTameAt W ⟨1, hk⟩ h ∧ ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ 1 := by
  have hij : (⟨1, hk⟩ : Fin k).val = (⟨0, by omega⟩ : Fin k).val + 1 := rfl
  obtain ⟨hW2, hT2⟩ := line2_walk hij
  obtain ⟨hW3, hT3⟩ := line3_walk hij
  have hcols : ∀ {W : List (Set (Band k))} {h : Band k}, IsTameAt W ⟨1, hk⟩ h → ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ 1 :=
    fun hT X hX x hx => tame_cols_le hT X hX x hx
  have hne : b (⟨0, by omega⟩ : Fin k) ≠ b ⟨1, hk⟩ := col_ne (by simp)
  rcases split_pair hne hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨_, _, hW2, rfl, hT2, hcols hT2⟩
  · exact ⟨_, _, hW3, rfl, hT3, hcols hT3⟩
  · exact ⟨_, _, isWalkFromTo_reverse hW3, by simp, tame_reverse hT3, hcols (tame_reverse hT3)⟩
  · exact ⟨_, _, isWalkFromTo_reverse hW2, by simp, tame_reverse hT2, hcols (tame_reverse hT2)⟩

end TameBases

section TameExt

variable {k : ℕ}

/-- The schedule of `W` in the tame extension: `W` waits one step, just before its arrival move `μ`. -/
def tsW (μ t : ℕ) : ℕ := if t < μ then t else t - 1

/-- The schedule of `V`: move 1 alone just before move `μ` of `W`, move 2 with move `μ`, move 3 with move `ν`. -/
def tsV (μ ν t : ℕ) : ℕ := if t < μ then 0 else if t = μ then 1 else if t ≤ ν then 2 else 3

theorem tame_outer {W : List (Set (Band k))} {i : Fin k} {h : Band k} (hT : IsTameAt W i h) {X : Set (Band k)}
    (hX : X ∈ W) : outerAt X i = none ∨ outerAt X i = some h := by
  obtain ⟨p, q, r, -, -, -, hL⟩ := tame_trace hT
  have hmem : outerAt X i ∈ W.map (outerAt · i) := List.mem_map.2 ⟨X, hX, rfl⟩
  rw [hL] at hmem
  simp only [List.mem_append, List.mem_replicate] at hmem
  rcases hmem with (⟨-, h1⟩ | ⟨-, h1⟩) | ⟨-, h1⟩
  · exact Or.inl h1
  · exact Or.inr h1
  · exact Or.inl h1

/-- In a walk tame at column `i` with outer element `c_i`, no state contains `a_i`. -/
theorem tame_no_a {W : List (Set (Band k))} {i : Fin k} (hT : IsTameAt W i (c i)) {X : Set (Band k)} (hX : X ∈ W) :
    a i ∉ X := by
  intro ha
  rcases tame_outer hT hX with h1 | h1 <;> rw [outerAt_of_a_mem ha] at h1
  · exact absurd h1 (by simp)
  · exact a_ne_c i i (Option.some_inj.1 h1)

/-- The tame extension (Lemma 4.9), merge part: `W` tame at `p` with outer element `c_p`, and a 3-move walk `V` on
the columns `q = p + 1`, `r = q + 1` that removes `a_q` with its move 2, whose state 2 lies in row `c`, and that adds
`b_q` with its move 3. -/
theorem tame_ext_merge {p q r : Fin k} (hpq : q.val = p.val + 1) (hqr : r.val = q.val + 1)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} (hW : IsWalkFromTo W A' B') (hT : IsTameAt W p (c p))
    {V : List (Set (Band k))} {A'' B'' : Set (Band k)} (hV : IsWalkFromTo V A'' B'') (hVlen : V.length = 4)
    (hVcols : ∀ Y ∈ V, ∀ y ∈ Y, q.val ≤ y.1.val)
    (haq1 : a q ∈ V.getD 1 ∅) (hrow2 : ∀ y ∈ V.getD 2 ∅, y.2 = 2) (hbq3 : b q ∈ V.getD 3 ∅)
    {h' : Band k} (hVT : IsTameAt V r h') :
    ∃ W' h'', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + 1 ∧ IsTameAt W' r h'' := by
  obtain ⟨μ, ν, hμ1, hμν, hνn, hmem⟩ := tame_arrive_depart W p (c p) hT
  have hWlen := List.length_pos_of_ne_nil hW.1.1
  have hcolW : ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ p.val := tame_cols_le hT
  have hw0 : tsW μ 0 = 0 := by unfold tsW; split_ifs <;> omega
  have hv0 : tsV μ ν 0 = 0 := by unfold tsV; split_ifs <;> omega
  have hwM : tsW μ (W.length - 1 + 1) = W.length - 1 := by unfold tsW; split_ifs <;> omega
  have hvM : tsV μ ν (W.length - 1 + 1) = V.length - 1 := by rw [hVlen]; unfold tsV; split_ifs <;> omega
  have hws : ∀ t < W.length - 1 + 1, tsW μ (t + 1) = tsW μ t ∨ tsW μ (t + 1) = tsW μ t + 1 := by
    intro t ht; unfold tsW; split_ifs <;> omega
  have hvs : ∀ t < W.length - 1 + 1, tsV μ ν (t + 1) = tsV μ ν t ∨ tsV μ ν (t + 1) = tsV μ ν t + 1 := by
    intro t ht; unfold tsV; split_ifs <;> omega
  have hmove : ∀ t < W.length - 1 + 1, tsW μ (t + 1) = tsW μ t + 1 ∨ tsV μ ν (t + 1) = tsV μ ν t + 1 := by
    intro t ht; unfold tsW tsV; split_ifs <;> omega
  have hdisj : ∀ X ∈ W, ∀ Y ∈ V, Disjoint X Y := fun X hX Y hY =>
    Set.disjoint_left.2 fun x hxX hxY => by
      have := hcolW X hX x hxX
      have := hVcols Y hY x hxY
      omega
  have hanti : ∀ t ≤ W.length - 1 + 1, ∀ x ∈ W.getD (tsW μ t) ∅, ∀ y ∈ V.getD (tsV μ ν t) ∅, ¬ Comp x y := by
    intro t ht x hx y hy hxy
    obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hx
    obtain ⟨Y, hY, hyY⟩ := mem_of_mem_getD hy
    have hxc := hcolW X hX x hxX
    have hyc := hVcols Y hY y hyY
    rw [comp_iff_val] at hxy
    have hx2 := x.2.isLt
    have hy2 := y.2.isLt
    have key : x.1.val = p.val ∧ (x.2.val = 0 ∨ (x.2.val = 2 ∧ y.2.val ≠ 2)) := by omega
    rcases key with ⟨hxp, h0 | ⟨h2, hy2'⟩⟩
    · have : x = a p := Prod.ext (Fin.ext hxp) (Fin.ext h0)
      subst this
      exact tame_no_a hT hX hxX
    · have : x = c p := Prod.ext (Fin.ext hxp) (Fin.ext h2)
      subst this
      have hlt : tsW μ t < W.length := by unfold tsW; split_ifs <;> omega
      have hm := (hmem _ hlt).1 hx
      have hv2 : tsV μ ν t = 2 := by
        unfold tsW at hm
        unfold tsV
        split_ifs at hm ⊢ <;> omega
      rw [hv2] at hy
      exact hy2' (by rw [hrow2 y hy]; rfl)
  have hboth : ∀ t < W.length - 1 + 1, tsW μ (t + 1) = tsW μ t + 1 → tsV μ ν (t + 1) = tsV μ ν t + 1 →
      ∃ x ∈ symmDiff (W.getD (tsW μ t) ∅) (W.getD (tsW μ t + 1) ∅),
        ∃ y ∈ symmDiff (V.getD (tsV μ ν t) ∅) (V.getD (tsV μ ν t + 1) ∅), Comp x y := by
    intro t ht hw hv
    have ht' : t = μ ∨ t = ν := by
      unfold tsW at hw
      unfold tsV at hv
      split_ifs at hw hv <;> omega
    rcases ht' with rfl | rfl
    · have e1 : tsW t t = t - 1 := by unfold tsW; simp
      have e2 : tsV t ν t = 1 := by unfold tsV; simp
      rw [e1, e2, Nat.sub_add_cancel hμ1]
      refine ⟨c p, Set.mem_symmDiff.2 (Or.inr ⟨(hmem t (by omega)).2 ⟨le_rfl, hμν⟩, fun h => ?_⟩), a q,
        Set.mem_symmDiff.2 (Or.inl ⟨haq1, fun h => ?_⟩), comp_ca_next hpq⟩
      · have := ((hmem (t - 1) (by omega)).1 h).1
        omega
      · have := hrow2 _ h
        exact absurd this (by show ¬ ((0 : Fin 3) = 2); decide)
    · have e1 : tsW μ t = t - 1 := by unfold tsW; split_ifs <;> omega
      have e2 : tsV μ t t = 2 := by unfold tsV; split_ifs <;> omega
      rw [e1, e2, Nat.sub_add_cancel (by omega : 1 ≤ t)]
      refine ⟨c p, Set.mem_symmDiff.2 (Or.inl ⟨(hmem (t - 1) (by omega)).2 ⟨by omega, by omega⟩, fun h => ?_⟩),
        b q, Set.mem_symmDiff.2 (Or.inr ⟨hbq3, fun h => ?_⟩), comp_symm (comp_bc_prev hpq)⟩
      · have := ((hmem t (by omega)).1 h).2
        omega
      · have := hrow2 _ h
        exact absurd this (by show ¬ ((1 : Fin 3) = 2); decide)
  refine ⟨merge2 W V (tsW μ) (tsV μ ν) (W.length - 1 + 1), h',
    merge2_walk hW hV hw0 hv0 hwM hvM hws hvs hmove hdisj hanti hboth, by rw [merge2_length]; omega,
    ?_, hVT.2.1, hVT.2.2.1, ?_⟩
  · intro X hX x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
    rcases hx with hx | hx
    · obtain ⟨X', hX', hx'⟩ := mem_of_mem_getD hx
      have := hcolW X' hX' x hx'
      exact Fin.le_iff_val_le_val.2 (by omega)
    · obtain ⟨Y, hY, hy⟩ := mem_of_mem_getD hx
      exact hVT.1 Y hY x hy
  · rw [merge2_trace_right hV.1.1 hv0 hvM hvs fun X hX x hx hxr => by
      have := hcolW X hX x hx
      rw [hxr] at this
      omega]
    exact hVT.2.2.2

theorem cols_line2 {q r : Fin k} (hqr : r.val = q.val + 1) :
    ∀ Y ∈ ([∅, {a q}, {c q, c r}, {b q, b r}] : List (Set (Band k))), ∀ y ∈ Y, q.val ≤ y.1.val := by
  intro Y hY y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false] at hy
  · rw [hy, a_fst]
  · rcases hy with rfl | rfl <;> simp only [c_fst] <;> omega
  · rcases hy with rfl | rfl <;> simp only [b_fst] <;> omega

theorem cols_line4 {q r : Fin k} (hqr : r.val = q.val + 1) :
    ∀ Y ∈ ([{b r}, {a q, a r}, {c q}, {b q}] : List (Set (Band k))), ∀ y ∈ Y, q.val ≤ y.1.val := by
  intro Y hY y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hY
  rcases hY with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  · rw [hy, b_fst]
    omega
  · rcases hy with rfl | rfl <;> simp only [a_fst] <;> omega
  · rw [hy, c_fst]
  · rw [hy, b_fst]

/-- Lemma 4.9 when the outer element of column `p` is `c_p`: all four splits of `{b_q, b_r}`. -/
theorem tame_ext_c {p q r : Fin k} (hpq : q.val = p.val + 1) (hqr : r.val = q.val + 1)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} (hW : IsWalkFromTo W A' B') (hT : IsTameAt W p (c p))
    {A'' B'' : Set (Band k)} (hAB : IsSplit A'' B'' {b q, b r}) :
    ∃ W' h'', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + 1 ∧ IsTameAt W' r h'' := by
  have hne : b q ≠ b r := col_ne (by simp only [b_fst]; omega)
  obtain ⟨hV2, hT2⟩ := line2_walk hqr
  obtain ⟨hV4, hT4⟩ := line4_walk hqr
  have case2 : ∀ {W : List (Set (Band k))} {A' B' : Set (Band k)}, IsWalkFromTo W A' B' → IsTameAt W p (c p) →
      ∃ W' h'', IsWalkFromTo W' (A' ∪ ∅) (B' ∪ {b q, b r}) ∧ W'.length - 1 = (W.length - 1) + 1 ∧
        IsTameAt W' r h'' := fun hW hT =>
    tame_ext_merge hpq hqr hW hT hV2 rfl (cols_line2 hqr) (Set.mem_singleton _) (rows2 _ _ 2 rfl rfl) (by simp) hT2
  have case4 : ∀ {W : List (Set (Band k))} {A' B' : Set (Band k)}, IsWalkFromTo W A' B' → IsTameAt W p (c p) →
      ∃ W' h'', IsWalkFromTo W' (A' ∪ {b r}) (B' ∪ {b q}) ∧ W'.length - 1 = (W.length - 1) + 1 ∧
        IsTameAt W' r h'' := fun hW hT =>
    tame_ext_merge hpq hqr hW hT hV4 rfl (cols_line4 hqr) (by simp) (rows1 _ 2 rfl) (Set.mem_singleton _) hT4
  rcases split_pair hne hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact case2 hW hT
  · obtain ⟨W', h'', h1, h2, h3⟩ := case4 (isWalkFromTo_reverse hW) (tame_reverse hT)
    exact ⟨W'.reverse, h'', isWalkFromTo_reverse h1, by rw [List.length_reverse, h2, List.length_reverse],
      tame_reverse h3⟩
  · exact case4 hW hT
  · obtain ⟨W', h'', h1, h2, h3⟩ := case2 (isWalkFromTo_reverse hW) (tame_reverse hT)
    exact ⟨W'.reverse, h'', isWalkFromTo_reverse h1, by rw [List.length_reverse, h2, List.length_reverse],
      tame_reverse h3⟩

/-- Lemma 4.9 (tame extension), in the statement form of Sec4/Chain.lean `lem_4_9`. -/
theorem tame_ext (i : ℕ) (hi : i + 2 < k) (W : List (Set (Band k))) (A' B' : Set (Band k)) (h : Band k)
    (hW : IsWalkFromTo W A' B') (hT : IsTameAt W ⟨i, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' {b ⟨i + 1, by omega⟩, b ⟨i + 2, hi⟩}) :
    ∃ W' h', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + 1 ∧
      IsTameAt W' ⟨i + 2, hi⟩ h' := by
  have hpq : (⟨i + 1, by omega⟩ : Fin k).val = (⟨i, by omega⟩ : Fin k).val + 1 := rfl
  have hqr : (⟨i + 2, hi⟩ : Fin k).val = (⟨i + 1, by omega⟩ : Fin k).val + 1 := rfl
  have hh : h = c ⟨i, by omega⟩ ∨ h = a ⟨i, by omega⟩ := by
    have h1 := hT.2.1
    have h2 : h.2.val ≠ 1 := fun hv => hT.2.2.1 (Fin.ext hv)
    have hlt := h.2.isLt
    rcases (by omega : h.2.val = 2 ∨ h.2.val = 0) with hv | hv
    · exact Or.inl (Prod.ext h1 (Fin.ext hv))
    · exact Or.inr (Prod.ext h1 (Fin.ext hv))
  rcases hh with rfl | rfl
  · exact tame_ext_c hpq hqr hW hT hAB
  · obtain ⟨-, hTs, hWs⟩ := tame_symm W hW.1 _ _ hT
    rw [sigma_a] at hTs
    obtain ⟨W', h', h1, h2, h3⟩ := tame_ext_c hpq hqr (hWs A' B' hW hmid) hTs hAB
    exact ⟨W', h', h1, by rw [h2, List.length_map], h3⟩

end TameExt

section TameCor

variable {k : ℕ}

theorem mids_split_lower {i : ℕ} {A B : Set (Band k)} (hAB : IsSplit A B {x | x.2 = 1 ∧ x.1.val < i}) (j : ℕ)
    (hj : j ≤ i) :
    IsSplit (A ∩ {x | x.2 = 1 ∧ x.1.val < j}) (B ∩ {x | x.2 = 1 ∧ x.1.val < j}) {x | x.2 = 1 ∧ x.1.val < j} := by
  obtain ⟨hdis, hU, -⟩ := hAB
  refine ⟨hdis.mono Set.inter_subset_left Set.inter_subset_left, ?_, isAntichainSet_row 1 _ fun x hx => hx.1⟩
  rw [← Set.union_inter_distrib_right, hU]
  ext x
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, by omega⟩, h1, h2⟩

theorem mids_split_upper {i : ℕ} (hi : 3 ≤ i) (hik : i ≤ k) {A B : Set (Band k)}
    (hAB : IsSplit A B {x | x.2 = 1 ∧ x.1.val < i}) :
    IsSplit (A \ {x | x.2 = 1 ∧ x.1.val < i - 2}) (B \ {x | x.2 = 1 ∧ x.1.val < i - 2})
      {b ⟨i - 3 + 1, by omega⟩, b ⟨i - 3 + 2, by omega⟩} := by
  obtain ⟨hdis, hU, -⟩ := hAB
  refine ⟨hdis.mono Set.sdiff_subset Set.sdiff_subset, ?_, isAntichainSet_pair_row rfl⟩
  rw [← Set.union_sdiff_distrib, hU]
  ext x
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h4 : ¬ x.1.val < i - 2 := fun h => h3 ⟨h1, h⟩
    rcases (by omega : x.1.val = i - 3 + 1 ∨ x.1.val = i - 3 + 2) with hv | hv
    · exact Or.inl (Prod.ext (Fin.ext hv) h1)
    · exact Or.inr (Set.mem_singleton_iff.2 (Prod.ext (Fin.ext hv) h1))
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨⟨rfl, by show i - 3 + 1 < i; omega⟩, fun h => by have := h.2; change i - 3 + 1 < i - 2 at this; omega⟩
    · rw [Set.mem_singleton_iff.1 hx]
      exact ⟨⟨rfl, by show i - 3 + 2 < i; omega⟩, fun h => by have := h.2; change i - 3 + 2 < i - 2 at this; omega⟩

/-- Corollary 4.10 without the row: a walk of length `⌊i/2⌋ + 2` tame at column `i` (0-based `i - 1`). -/
theorem tame_any : ∀ i : ℕ, ∀ (hi : 1 ≤ i) (hik : i ≤ k) (A B : Set (Band k)),
    IsSplit A B {x | x.2 = 1 ∧ x.1.val < i} →
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = i / 2 + 2 ∧ IsTameAt W ⟨i - 1, by omega⟩ h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hik A B hAB
    rcases (by omega : i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | h3
    · have hset : ({x | x.2 = 1 ∧ x.1.val < 1} : Set (Band k)) = {b ⟨0, by omega⟩} := by
        ext x
        constructor
        · rintro ⟨h1, h2⟩
          exact Prod.ext (Fin.ext (by show x.1.val = 0; omega)) h1
        · intro hx
          rw [Set.mem_singleton_iff.1 hx]
          exact ⟨rfl, by show 0 < 1; omega⟩
      rw [hset] at hAB
      obtain ⟨W, h, hW, hlen, hT, -⟩ := tame_base_one hik A B hAB
      exact ⟨W, h, hW, by omega, hT⟩
    · have hset : ({x | x.2 = 1 ∧ x.1.val < 2} : Set (Band k)) = {b ⟨0, by omega⟩, b ⟨1, hik⟩} := by
        ext x
        constructor
        · rintro ⟨h1, h2⟩
          rcases (by omega : x.1.val = 0 ∨ x.1.val = 1) with hv | hv
          · exact Or.inl (Prod.ext (Fin.ext hv) h1)
          · exact Or.inr (Set.mem_singleton_iff.2 (Prod.ext (Fin.ext hv) h1))
        · intro hx
          rcases hx with rfl | hx
          · exact ⟨rfl, by show 0 < 2; omega⟩
          · rw [Set.mem_singleton_iff.1 hx]
            exact ⟨rfl, by show 1 < 2; omega⟩
      rw [hset] at hAB
      obtain ⟨W, h, hW, hlen, hT, -⟩ := tame_base_two hik A B hAB
      exact ⟨W, h, hW, by omega, hT⟩
    · obtain ⟨W₀, h₀, hW₀, hlen₀, hT₀⟩ :=
        ih (i - 2) (by omega) (by omega) (by omega) _ _ (mids_split_lower hAB (i - 2) (by omega))
      have e₀ : (⟨i - 2 - 1, by omega⟩ : Fin k) = ⟨i - 3, by omega⟩ := Fin.ext (by show i - 2 - 1 = i - 3; omega)
      rw [e₀] at hT₀
      have hmid : ∀ x ∈ (A ∩ {x | x.2 = 1 ∧ x.1.val < i - 2}) ∪ (B ∩ {x | x.2 = 1 ∧ x.1.val < i - 2}),
          x.2 = 1 := by
        rintro x (⟨-, h1, -⟩ | ⟨-, h1, -⟩) <;> exact h1
      obtain ⟨W', h', hW', hlen', hT'⟩ :=
        tame_ext (i - 3) (by omega) W₀ _ _ h₀ hW₀ hT₀ hmid _ _ (mids_split_upper h3 hik hAB)
      rw [Set.inter_union_sdiff, Set.inter_union_sdiff] at hW'
      have e' : (⟨i - 3 + 2, by omega⟩ : Fin k) = ⟨i - 1, by omega⟩ := Fin.ext (by show i - 3 + 2 = i - 1; omega)
      rw [e'] at hT'
      exact ⟨W', h', hW', by omega, hT'⟩

/-- Corollary 4.10, in the statement form of Sec4/Chain.lean `cor_4_10`. -/
theorem tame_cor (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (A B : Set (Band k)) (hAB : IsSplit A B {x | x.2 = 1 ∧ x.1.val < i}) :
    ∃ W h, IsWalkFromTo W A B ∧ W.length - 1 = i / 2 + 2 ∧ IsTameAt W ⟨i - 1, by omega⟩ h ∧ h.2 = r ∧
      ∀ X ∈ W, ∀ x ∈ X, x.1.val < i := by
  obtain ⟨W, h, hW, hlen, hT⟩ := tame_any i hi hik A B hAB
  have hcols : ∀ {W : List (Set (Band k))} {h : Band k}, IsTameAt W ⟨i - 1, by omega⟩ h →
      ∀ X ∈ W, ∀ x ∈ X, x.1.val < i := fun hT X hX x hx => by
    have := tame_cols_le hT X hX x hx
    change x.1.val ≤ i - 1 at this
    omega
  by_cases hrow : h.2 = r
  · exact ⟨W, h, hW, hlen, hT, hrow, hcols hT⟩
  · have hmid : ∀ x ∈ A ∪ B, x.2 = 1 := fun x hx => by
      rw [hAB.2.1] at hx
      exact hx.1
    obtain ⟨-, hTs, hWs⟩ := tame_symm W hW.1 _ _ hT
    refine ⟨_, _, hWs A B hW hmid, by rw [List.length_map]; exact hlen, hTs, ?_, hcols hTs⟩
    have h2 : h.2.val ≠ 1 := fun hv => hT.2.2.1 (Fin.ext hv)
    have hr2 : r.val ≠ 1 := fun hv => hr (Fin.ext hv)
    have hne : h.2.val ≠ r.val := fun hv => hrow (Fin.ext hv)
    have := h.2.isLt
    have := r.isLt
    exact Fin.ext (by rw [sigma_snd_val]; omega)

end TameCor

end LeeDiam.S4

