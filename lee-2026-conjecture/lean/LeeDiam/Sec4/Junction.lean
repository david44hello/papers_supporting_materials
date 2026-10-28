/-
LeeDiam/Sec4/Junction.lean — Section 4 helper: the junction (Lemma 4.11, sec_chain.tex v1.50 l. 129-136).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Proof: let `Q` be any walk of Corollary 4.6 for the split of `{x_i, …, x_{i+j-1}}` (row `r`), and `κ` the last state of
`Q` that contains `x_i`. Merge: the moves of `Q` before `κ`, then the moves of `W`, where the move of `W` at which the
outer element `y_{i-1}` of the other row first appears is performed together with move `κ` of `Q` (which removes
`x_i`), then the rest of `Q`. The only comparable pair across the two walks is `y_{i-1}, x_i`.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Tame

namespace LeeDiam.S4

open Finset Band

section Junction

variable {k : ℕ}

/-- The schedule of `W` in the junction: `W` waits during the first `κ` moves of `Q`. -/
def jW (κ n t : ℕ) : ℕ := if t ≤ κ then 0 else if t ≤ κ + n then t - κ else n

/-- The schedule of `Q`: moves `0, …, κ - 1` first, move `κ` together with move `μ - 1` of `W`, the rest after `W`. -/
def jV (κ μ n t : ℕ) : ℕ :=
  if t ≤ κ then t else if t < κ + μ then κ else if t ≤ κ + n then κ + 1 else κ + 1 + (t - κ - n)

theorem getD_of_mem {W : List (Set (Band k))} {X : Set (Band k)} (hX : X ∈ W) : ∃ t, W.getD t ∅ = X := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hX
  exact ⟨t, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl⟩

theorem getD_eq_empty {W : List (Set (Band k))} {t : ℕ} (ht : W.length ≤ t) : W.getD t ∅ = ∅ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none ht]
  rfl

/-- Lemma 4.11 when `x_i` is initial. -/
theorem junction_core {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) {r : Fin 3} (hr : r ≠ 1)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} (hW : IsWalkFromTo W A' B') (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (hcols : ∀ X ∈ W, ∀ x ∈ X, x.1.val < i)
    (hc : ∃ X ∈ W, ((⟨i - 1, by omega⟩ : Fin k), Fin.rev r) ∈ X)
    {A'' B'' : Set (Band k)} (hAB : IsSplit A'' B'' (rowSeg r i (i + j - 1)))
    (hfirst : ((⟨i, by omega⟩ : Fin k), r) ∈ A'') :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + j / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  classical
  obtain ⟨Q, hQ, hQlen, hQrow, hQs⟩ := comb_cor r hr i (i + j - 1) (by omega) (by omega) A'' B'' hAB
  set cc : Band k := ((⟨i - 1, by omega⟩ : Fin k), Fin.rev r) with hcc
  set aa : Band k := ((⟨i, by omega⟩ : Fin k), r) with haa
  have hWlen := List.length_pos_of_ne_nil hW.1.1
  have hQlen0 := List.length_pos_of_ne_nil hQ.1.1
  have hrv : r.val ≠ 1 := fun h => hr (Fin.ext h)
  have hrlt := r.isLt
  -- μ: the first state of `W` that contains `cc`
  have hex : ∃ t, cc ∈ W.getD t ∅ := by
    obtain ⟨X, hX, hcX⟩ := hc
    obtain ⟨t, ht⟩ := getD_of_mem hX
    exact ⟨t, ht ▸ hcX⟩
  have hμ : cc ∈ W.getD (Nat.find hex) ∅ := Nat.find_spec hex
  have hμmin : ∀ t < Nat.find hex, cc ∉ W.getD t ∅ := fun t ht => Nat.find_min hex ht
  have hμ1 : 1 ≤ Nat.find hex := by
    by_contra h0
    have h0' : Nat.find hex = 0 := by omega
    rw [h0', headD_of_head? hW.2.1] at hμ
    have := hmid cc (Or.inl hμ)
    rw [hcc] at this
    apply hrv
    have h2 := congrArg Fin.val this
    simp only [Fin.val_rev] at h2
    show r.val = 1
    omega
  have hμn : Nat.find hex ≤ W.length - 1 := by
    by_contra h0
    rw [getD_eq_empty (by omega)] at hμ
    exact hμ
  -- κ: the last state of `Q` that contains `aa`
  have hQ0 : aa ∈ Q.getD 0 ∅ := by rw [headD_of_head? hQ.2.1]; exact hfirst
  have hκ : aa ∈ Q.getD (Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1)) ∅ :=
    Nat.findGreatest_spec (P := fun t => aa ∈ Q.getD t ∅) (Nat.zero_le _) hQ0
  have hκmax : ∀ t, Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1) < t → aa ∉ Q.getD t ∅ := by
    intro t ht hmem
    by_cases htl : t ≤ Q.length - 1
    · exact Nat.findGreatest_is_greatest ht htl hmem
    · rw [getD_eq_empty (by omega)] at hmem
      exact hmem
  have hκle : Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1) ≤ Q.length - 1 :=
    Nat.findGreatest_le _
  have hκlt : Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1) < Q.length - 1 := by
    rcases Nat.lt_or_ge (Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1)) (Q.length - 1) with h | h
    · exact h
    · have he : Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1) = Q.length - 1 := le_antisymm hκle h
      rw [he, lastD_of_getLast? hQ.2.2] at hκ
      exact absurd hAB.1 (Set.not_disjoint_iff.2 ⟨aa, hfirst, hκ⟩)
  set μ := Nat.find hex with hμdef
  set κ := Nat.findGreatest (fun t => aa ∈ Q.getD t ∅) (Q.length - 1) with hκdef
  set n := W.length - 1 with hn
  set ℓ := Q.length - 1 with hℓ
  -- the schedule
  have hw0 : jW κ n 0 = 0 := by unfold jW; split_ifs <;> omega
  have hv0 : jV κ μ n 0 = 0 := by unfold jV; split_ifs <;> omega
  have hwM : jW κ n (n + ℓ - 1) = W.length - 1 := by unfold jW; split_ifs <;> omega
  have hvM : jV κ μ n (n + ℓ - 1) = Q.length - 1 := by unfold jV; split_ifs <;> omega
  have hws : ∀ t < n + ℓ - 1, jW κ n (t + 1) = jW κ n t ∨ jW κ n (t + 1) = jW κ n t + 1 := by
    intro t ht; unfold jW; split_ifs <;> omega
  have hvs : ∀ t < n + ℓ - 1, jV κ μ n (t + 1) = jV κ μ n t ∨ jV κ μ n (t + 1) = jV κ μ n t + 1 := by
    intro t ht; unfold jV; split_ifs <;> omega
  have hmove : ∀ t < n + ℓ - 1, jW κ n (t + 1) = jW κ n t + 1 ∨ jV κ μ n (t + 1) = jV κ μ n t + 1 := by
    intro t ht; unfold jW jV; split_ifs <;> omega
  have hQc : ∀ Y ∈ Q, ∀ y ∈ Y, i ≤ y.1.val := fun Y hY y hy => (hQrow Y hY y hy).2.1
  have hdisj : ∀ X ∈ W, ∀ Y ∈ Q, Disjoint X Y := fun X hX Y hY =>
    Set.disjoint_left.2 fun x hxX hxY => by
      have := hcols X hX x hxX
      have := hQc Y hY x hxY
      omega
  -- the only comparable pair across is `cc`, `aa`
  have hpair : ∀ X ∈ W, ∀ x ∈ X, ∀ Y ∈ Q, ∀ y ∈ Y, Comp x y → x = cc ∧ y = aa := by
    intro X hX x hx Y hY y hy hxy
    have hxc := hcols X hX x hx
    have hyc := hQc Y hY y hy
    have hcolsxy := comp_cols hxy
    have hy1 : y.1.val = i := by omega
    have hx1 : x.1.val = i - 1 := by omega
    have hy2 := hQs Y hY y hy hy1
    rw [comp_iff_val] at hxy
    have hx2 := x.2.isLt
    have hy2v : y.2.val = r.val := by rw [hy2]
    have hx2v : x.2.val = 2 - r.val := by omega
    refine ⟨Prod.ext (Fin.ext hx1) (Fin.ext ?_), Prod.ext (Fin.ext hy1) hy2⟩
    rw [hx2v]
    simp [hcc, Fin.val_rev]
  have hanti : ∀ t ≤ n + ℓ - 1, ∀ x ∈ W.getD (jW κ n t) ∅, ∀ y ∈ Q.getD (jV κ μ n t) ∅, ¬ Comp x y := by
    intro t ht x hx y hy hxy
    obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hx
    obtain ⟨Y, hY, hyY⟩ := mem_of_mem_getD hy
    obtain ⟨rfl, rfl⟩ := hpair X hX x hxX Y hY y hyY hxy
    have hw : μ ≤ jW κ n t := by
      by_contra h
      exact hμmin _ (by omega) hx
    have hv : jV κ μ n t ≤ κ := by
      by_contra h
      exact hκmax _ (by omega) hy
    unfold jW at hw
    unfold jV at hv
    split_ifs at hw hv <;> omega
  have hboth : ∀ t < n + ℓ - 1, jW κ n (t + 1) = jW κ n t + 1 → jV κ μ n (t + 1) = jV κ μ n t + 1 →
      ∃ x ∈ symmDiff (W.getD (jW κ n t) ∅) (W.getD (jW κ n t + 1) ∅),
        ∃ y ∈ symmDiff (Q.getD (jV κ μ n t) ∅) (Q.getD (jV κ μ n t + 1) ∅), Comp x y := by
    intro t ht hw hv
    have htv : t = κ + μ - 1 := by
      unfold jW at hw
      unfold jV at hv
      split_ifs at hw hv <;> omega
    have e1 : jW κ n t = μ - 1 := by unfold jW; split_ifs <;> omega
    have e2 : jV κ μ n t = κ := by unfold jV; split_ifs <;> omega
    rw [e1, e2, Nat.sub_add_cancel hμ1]
    refine ⟨cc, Set.mem_symmDiff.2 (Or.inr ⟨hμ, hμmin _ (by omega)⟩), aa,
      Set.mem_symmDiff.2 (Or.inl ⟨hκ, hκmax _ (by omega)⟩), ?_⟩
    rw [comp_iff_val]
    simp only [hcc, haa, Fin.val_rev]
    omega
  refine ⟨merge2 W Q (jW κ n) (jV κ μ n) (n + ℓ - 1),
    merge2_walk hW hQ hw0 hv0 hwM hvM hws hvs hmove hdisj hanti hboth, ?_, ?_⟩
  · rw [merge2_length]
    omega
  · intro X hX x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
    rcases hx with hx | hx
    · obtain ⟨X', hX', hx'⟩ := mem_of_mem_getD hx
      have := hcols X' hX' x hx'
      omega
    · obtain ⟨Y, hY, hy⟩ := mem_of_mem_getD hx
      have := (hQrow Y hY x hy).2.2
      omega

/-- Lemma 4.11 (junction), in the statement form of Sec4/Chain.lean `lem_4_11`. -/
theorem junction (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (W : List (Set (Band k))) (A' B' : Set (Band k)) (hW : IsWalkFromTo W A' B') (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (hcols : ∀ X ∈ W, ∀ x ∈ X, x.1.val < i)
    (hc : ∃ X ∈ W, ((⟨i - 1, by omega⟩ : Fin k), Fin.rev r) ∈ X)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (rowSeg r i (i + j - 1))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + j / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  have hmem : ((⟨i, by omega⟩ : Fin k), r) ∈ A'' ∪ B'' := by
    rw [hAB.2.1]
    exact ⟨rfl, le_rfl, by show i ≤ i + j - 1; omega⟩
  rcases hmem with hA | hB
  · exact junction_core hi hj hL hr hW hmid hcols hc hAB hA
  · have hmid' : ∀ x ∈ B' ∪ A', x.2 = 1 := fun x hx => hmid x (Set.union_comm B' A' ▸ hx)
    have hAB' : IsSplit B'' A'' (rowSeg r i (i + j - 1)) :=
      ⟨hAB.1.symm, by rw [Set.union_comm]; exact hAB.2.1, hAB.2.2⟩
    obtain ⟨W', h1, h2, h3⟩ := junction_core hi hj hL hr (isWalkFromTo_reverse hW) hmid'
      (fun X hX => hcols X (List.mem_reverse.1 hX))
      (by obtain ⟨X, hX, hcX⟩ := hc; exact ⟨X, List.mem_reverse.2 hX, hcX⟩) hAB' hB
    exact ⟨W'.reverse, isWalkFromTo_reverse h1, by rw [List.length_reverse, h2, List.length_reverse],
      fun X hX => h3 X (List.mem_reverse.1 hX)⟩

end Junction

end LeeDiam.S4

