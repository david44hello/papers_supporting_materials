/- NagataHigman/Proofs/Shapes.lean — partition combinatorics of shapes in the n × n box (paper Sections 2-4).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.Young
import NagataHigman.Defs.GroupAlgebra

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

/-! ## Counting parts in the box -/

/-- Every part of a shape in the box is at most `n`. -/
theorem le_of_mem_parts_inBox {N n : ℕ} {lam : Shape N} (h : lam.InBox n) {p : ℕ} (hp : p ∈ lam.parts) :
    p ≤ n :=
  Multiset.sup_le.1 h.2 p hp

/-- Split the parts into the parts equal to `n` and the others. -/
theorem parts_split (s : Multiset ℕ) (n : ℕ) :
    s = Multiset.replicate (s.count n) n + s.filter (· ≠ n) := by
  rw [← Multiset.filter_eq' s n]
  exact (Multiset.filter_add_not (· = n) s).symm

/-- The counting data of a shape in the box: `a` parts equal to `n`, the other parts are at most `n - 1`. -/
theorem box_count {N n : ℕ} {lam : Shape N} (h : lam.InBox n) :
    lam.parts.count n * n + (lam.parts.filter (· ≠ n)).sum = N ∧
    (lam.parts.filter (· ≠ n)).sum ≤ Multiset.card (lam.parts.filter (· ≠ n)) * (n - 1) ∧
    lam.parts.count n + Multiset.card (lam.parts.filter (· ≠ n)) ≤ n := by
  have hsplit := parts_split lam.parts n
  refine ⟨?_, ?_, ?_⟩
  · conv_rhs => rw [← lam.parts_sum, hsplit]
    simp
  · have := Multiset.sum_le_card_nsmul (lam.parts.filter (· ≠ n)) (n - 1) (fun p hp => by
      rw [Multiset.mem_filter] at hp
      have := le_of_mem_parts_inBox h hp.1
      omega)
    simpa using this
  · have hcard : Multiset.card lam.parts ≤ n := h.1
    conv_lhs => rw [show lam.parts.count n = Multiset.card (Multiset.replicate (lam.parts.count n) n) by simp]
    rw [← Multiset.card_add, ← hsplit]
    exact hcard

/-! ## Lemma 3.1, Section 4.1, Remark 2.3 -/

theorem lem_3_1_square_proved (n : ℕ) (lam : Shape (n ^ 2)) (h : lam.InBox n) :
    lam.parts = Multiset.replicate n n := by
  obtain ⟨hsum, hle, hcard⟩ := box_count h
  set a := lam.parts.count n
  set b := Multiset.card (lam.parts.filter (· ≠ n))
  set s := (lam.parts.filter (· ≠ n)).sum
  have hb : b = 0 := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · exact hb
    · exfalso
      have h1 : b * (n - 1) + b ≤ b * n := by
        rcases n with _ | n
        · simp at hcard; omega
        · simp; ring_nf; omega
      nlinarith
  have hrest : lam.parts.filter (· ≠ n) = 0 := Multiset.card_eq_zero.1 hb
  have ha : a = n := by
    rw [hb] at hcard
    have hs : s = 0 := by rw [show s = (lam.parts.filter (· ≠ n)).sum from rfl, hrest]; simp
    rw [hs] at hsum
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · nlinarith
  rw [parts_split lam.parts n, hrest, add_zero]
  exact congrArg (Multiset.replicate · n) ha

theorem sec_4_1_nu_proved (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (h : lam.InBox n) :
    lam.parts = Multiset.replicate (n - 1) n + {n - 1} := by
  obtain ⟨hsum, hle, hcard⟩ := box_count h
  have hsplit := parts_split lam.parts n
  set a := lam.parts.count n
  set rest := lam.parts.filter (· ≠ n) with hrest
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hsq : (k + 2) ^ 2 - 1 = k * k + 4 * k + 3 := by
    have : (k + 2) ^ 2 = k * k + 4 * k + 4 := by ring
    omega
  rw [hsq] at hsum
  rw [show k + 2 - 1 = k + 1 by omega] at hle
  have hmul := Nat.mul_le_mul_right (k + 2) hcard
  have hb : Multiset.card rest ≤ 1 := by nlinarith
  rcases Nat.lt_or_ge (Multiset.card rest) 1 with hb0 | hb1
  · exfalso
    have hr : rest = 0 := Multiset.card_eq_zero.1 (by omega)
    rw [hr] at hsum
    simp only [Multiset.sum_zero, add_zero] at hsum
    rcases Nat.lt_or_ge a (k + 2) with ha | ha
    · have : a * (k + 2) ≤ (k + 1) * (k + 2) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    · have : a = k + 2 := by rw [hr] at hcard; simp at hcard; omega
      rw [this] at hsum
      nlinarith
  · obtain ⟨r, hr⟩ := Multiset.card_eq_one.1 (le_antisymm hb hb1)
    have hrmem : r ∈ rest := by rw [hr]; exact Multiset.mem_singleton_self r
    rw [hrest, Multiset.mem_filter] at hrmem
    have hrle := le_of_mem_parts_inBox h hrmem.1
    have hrne := hrmem.2
    rw [hr] at hsum hcard
    simp only [Multiset.sum_singleton, Multiset.card_singleton] at hsum hcard
    have ha : a = k + 1 := by
      rcases Nat.lt_or_ge a (k + 1) with ha | ha
      · have : a * (k + 2) ≤ k * (k + 2) := Nat.mul_le_mul_right _ (by omega)
        nlinarith
      · omega
    have hrv : r = k + 1 := by rw [ha] at hsum; nlinarith
    rw [hsplit, hr, ha, hrv]
    simp

theorem box_empty_proved (n N : ℕ) (h : n ^ 2 < N) (lam : Shape N) : ¬ lam.InBox n := by
  intro hbox
  have hsum := Multiset.sum_le_card_nsmul lam.parts n (fun p hp => le_of_mem_parts_inBox hbox hp)
  rw [lam.parts_sum, smul_eq_mul] at hsum
  have hcard : Multiset.card lam.parts ≤ n := hbox.1
  have : Multiset.card lam.parts * n ≤ n * n := Nat.mul_le_mul_right n hcard
  nlinarith

/-! ## Cells of a diagram from its sorted row list -/

/-- The cells of `diagram λ`, read off a list `w` equal to the decreasingly sorted parts. -/
theorem mem_diagram_iff {N : ℕ} (lam : Shape N) (w : List ℕ) (hw : lam.parts.sort (· ≥ ·) = w)
    (c : ℕ × ℕ) : c ∈ lam.diagram ↔ ∃ h : c.1 < w.length, c.2 < w[c.1] := by
  subst hw
  exact YoungDiagram.mem_ofRowLens (hw := (Multiset.pairwise_sort lam.parts (· ≥ ·)).sortedGE)

/-- Sorting `a^k` followed by one smaller part. -/
theorem sort_replicate_add (k a m : ℕ) (hm : m ≤ a) :
    (Multiset.replicate k a + {m}).sort (· ≥ ·) = List.replicate k a ++ [m] := by
  induction k with
  | zero => simp [Multiset.sort_singleton]
  | succ k ih =>
    rw [Multiset.replicate_succ, Multiset.cons_add, Multiset.sort_cons, ih]
    · rfl
    · intro b hb
      rw [Multiset.mem_add, Multiset.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact (Multiset.eq_of_mem_replicate hb).le
      · exact hm

/-- Sorting a rectangle. -/
theorem sort_replicate (k a : ℕ) : (Multiset.replicate k a).sort (· ≥ ·) = List.replicate k a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Multiset.replicate_succ, Multiset.sort_cons, ih]
    · rfl
    · intro b hb
      exact (Multiset.eq_of_mem_replicate hb).le

/-- A row of length `k` in a Young diagram. -/
theorem rowLen_eq_of_mem_iff {μ : YoungDiagram} {i k : ℕ} (h : ∀ j, (i, j) ∈ μ ↔ j < k) : μ.rowLen i = k :=
  eq_of_forall_lt_iff fun j => YoungDiagram.mem_iff_lt_rowLen.symm.trans (h j)

/-- A column of length `k` in a Young diagram. -/
theorem colLen_eq_of_mem_iff {μ : YoungDiagram} {j k : ℕ} (h : ∀ i, (i, j) ∈ μ ↔ i < k) : μ.colLen j = k :=
  eq_of_forall_lt_iff fun i => YoungDiagram.mem_iff_lt_colLen.symm.trans (h i)

/-- The conjugate's parts are the rows of the transposed diagram. -/
theorem conjugate_parts {N : ℕ} (lam : Shape N) :
    lam.conjugate.parts = ((lam.diagram.transpose.rowLens : List ℕ) : Multiset ℕ) := rfl

/-- A shape whose diagram is symmetric is self-conjugate. -/
theorem conjugate_eq_self_of_transpose {N : ℕ} (lam : Shape N) (h : lam.diagram.transpose = lam.diagram) :
    lam.conjugate = lam := by
  ext1
  rw [conjugate_parts, h]
  change ((YoungDiagram.ofPartition lam).rowLens : Multiset ℕ) = lam.parts
  rw [YoungDiagram.rowLens_ofPartition_eq_sort_parts, Multiset.sort_eq]

/-! ## The shape `ν = (n^{n-1}, n-1)`: cells, self-conjugacy, diagonal hooks -/

theorem getElem_nu (n i : ℕ) (h : i < (List.replicate (n - 1) n ++ [n - 1]).length) :
    (List.replicate (n - 1) n ++ [n - 1])[i] = if i < n - 1 then n else n - 1 := by
  rw [List.getElem_append]
  split_ifs with h1 h2 h2
  · simp
  · simp at h1; omega
  · simp at h1; omega
  · simp

/-- The cells of `ν`: the `n × n` box minus its corner `(n-1, n-1)`. -/
theorem mem_nu_iff (n : ℕ) (hn : 1 ≤ n) {N : ℕ} (lam : Shape N)
    (hparts : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) (i j : ℕ) :
    (i, j) ∈ lam.diagram ↔ i < n ∧ j < n ∧ (i < n - 1 ∨ j < n - 1) := by
  have hw : lam.parts.sort (· ≥ ·) = List.replicate (n - 1) n ++ [n - 1] := by
    rw [hparts]; exact sort_replicate_add _ _ _ (by omega)
  rw [mem_diagram_iff lam _ hw]
  simp only [List.length_append, List.length_replicate, List.length_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [getElem_nu] at h2
    split_ifs at h2 <;> omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, ?_⟩
    rw [getElem_nu]
    split_ifs <;> omega

theorem nu_transpose (n : ℕ) (hn : 1 ≤ n) {N : ℕ} (lam : Shape N)
    (hparts : lam.parts = Multiset.replicate (n - 1) n + {n - 1}) : lam.diagram.transpose = lam.diagram := by
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    mem_nu_iff n hn lam hparts, mem_nu_iff n hn lam hparts]
  omega

theorem thm_4_4_selfconj_proved (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (h : lam.InBox n) :
    lam.conjugate = lam :=
  conjugate_eq_self_of_transpose lam (nu_transpose n (by omega) lam (sec_4_1_nu_proved n hn lam h))

/-- Reflecting `range m`. -/
theorem map_range_reflect (m : ℕ) (f : ℕ → ℕ) :
    (Multiset.range m).map (fun i => f (m - 1 - i)) = (Multiset.range m).map f := by
  have h : (Multiset.range m).map (fun i => m - 1 - i) = Multiset.range m := by
    rw [Multiset.Nodup.ext ((Multiset.nodup_range m).map_on ?_) (Multiset.nodup_range m)]
    · intro a
      simp only [Multiset.mem_map, Multiset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; omega
      · intro ha; exact ⟨m - 1 - a, by omega, by omega⟩
    · intro x hx y hy hxy
      rw [Multiset.mem_range] at hx hy
      omega
  conv_rhs => rw [← h]
  rw [Multiset.map_map]
  rfl

theorem thm_4_4_hooks_proved (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (h : lam.InBox n) :
    lam.diagonalHooks = (Multiset.range (n - 1)).map (fun i => 2 * i + 3) := by
  have hparts := sec_4_1_nu_proved n hn lam h
  have hmem := mem_nu_iff n (by omega) lam hparts
  have hsq : n ≤ n ^ 2 := Nat.le_self_pow two_ne_zero n
  have hfilter : (Finset.range (n ^ 2 - 1)).filter (fun i => (i, i) ∈ lam.diagram.cells) =
      Finset.range (n - 1) := by
    ext i
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range, YoungDiagram.mem_cells, hmem]
    omega
  have hrow : ∀ i < n - 1, lam.diagram.rowLen i = n := fun i hi =>
    rowLen_eq_of_mem_iff fun j => by rw [hmem]; omega
  have hcol : ∀ i < n - 1, lam.diagram.colLen i = n := fun i hi =>
    colLen_eq_of_mem_iff fun j => by rw [hmem]; omega
  unfold Shape.diagonalHooks
  rw [hfilter, Finset.range_val, ← map_range_reflect (n - 1) (fun i => 2 * i + 3)]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  rw [hrow i hi, hcol i hi]
  omega

/-! ## Rectangles -/

theorem rect_transpose {N : ℕ} (lam : Shape N) (r c : ℕ) (h : lam.parts = Multiset.replicate r c) :
    lam.diagram.transpose =
      YoungDiagram.ofRowLens (List.replicate c r)
        (List.Pairwise.sortedGE (List.pairwise_replicate.2 (Or.inr (le_refl r)) :
          List.Pairwise (· ≥ ·) (List.replicate c r))) := by
  have hw : lam.parts.sort (· ≥ ·) = List.replicate r c := by rw [h]; exact sort_replicate r c
  ext ⟨i, j⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    mem_diagram_iff lam _ hw, YoungDiagram.mem_ofRowLens]
  simp [and_comm]

theorem conjugate_rectangle_proved (N r c : ℕ) (hr : 1 ≤ r) (lam : Shape N)
    (h : lam.parts = Multiset.replicate r c) : lam.conjugate.parts = Multiset.replicate c r := by
  rw [conjugate_parts, rect_transpose lam r c h, YoungDiagram.rowLens_ofRowLens_eq_self, Multiset.coe_replicate]
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  omega

/-- A partition of `0` has no parts. -/
theorem parts_eq_zero_of_eq_zero {N : ℕ} (p : Nat.Partition N) (hN : N = 0) : p.parts = 0 := by
  subst hN
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  have hpos := p.parts_pos hx
  have hle := Multiset.le_sum_of_mem hx
  rw [p.parts_sum] at hle
  omega

theorem conjugate_square_proved (n : ℕ) (lam : Shape (n ^ 2)) (h : lam.InBox n) : lam.conjugate = lam := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext1
    rw [parts_eq_zero_of_eq_zero lam.conjugate (by simp), parts_eq_zero_of_eq_zero lam (by simp)]
  · ext1
    rw [conjugate_rectangle_proved _ n n hn lam (lem_3_1_square_proved n lam h), lem_3_1_square_proved n lam h]

/-! ## Permutations whose cycle type is `h(ν) = (3, 5, …, 2n-1)` -/

theorem sum_map_range_odd (k : ℕ) : ((Multiset.range k).map (fun i => 2 * i + 3)).sum = k * (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.sum_cons, ih]
    ring

/-- `3 + 5 + ⋯ + (2n-1) = n² - 1`. -/
theorem hooks_sum (n : ℕ) (hn : 1 ≤ n) :
    ((Multiset.range (n - 1)).map (fun i => 2 * i + 3)).sum = n ^ 2 - 1 := by
  rw [sum_map_range_odd]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
  have h2 : k * (k + 2) = k * k + 2 * k := by ring
  rw [h1, Nat.add_sub_cancel, h2]
  omega

theorem two_le_of_mem_hooks {n a : ℕ} (ha : a ∈ (Multiset.range (n - 1)).map (fun i => 2 * i + 3)) : 2 ≤ a := by
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 ha
  omega

/-- `n² - 1 + (n - 1)` is even. -/
theorem even_hooks_exponent (n : ℕ) (hn : 1 ≤ n) : Even (n ^ 2 - 1 + (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h1 : (k + 1) ^ 2 = k * k + 2 * k + 1 := by ring
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · refine ⟨m * (2 * m + 3), ?_⟩
    have h2 : (m + m) * (m + m) = 4 * (m * m) := by ring
    have h3 : m * (2 * m + 3) = 2 * (m * m) + 3 * m := by ring
    rw [h1, h2, h3]
    omega
  · refine ⟨(2 * m + 1) * (m + 2), ?_⟩
    have h2 : (2 * m + 1) * (2 * m + 1) = 4 * (m * m) + 4 * m + 1 := by ring
    have h3 : (2 * m + 1) * (m + 2) = 2 * (m * m) + 5 * m + 2 := by ring
    rw [h1, h2, h3]
    omega

theorem perm_hooks_exists_proved (n : ℕ) (hn : 3 ≤ n) :
    ∃ σ : Equiv.Perm (Fin (n ^ 2 - 1)), σ.partition.parts = (Multiset.range (n - 1)).map (fun i => 2 * i + 3) := by
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (Fin (n ^ 2 - 1))).2
    ⟨by rw [hooks_sum n (by omega), Fintype.card_fin], fun a ha => two_le_of_mem_hooks ha⟩
  refine ⟨σ, ?_⟩
  rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ, hooks_sum n (by omega), Fintype.card_fin,
    Nat.sub_self, Multiset.replicate_zero, add_zero]

theorem perm_hooks_sign_proved (n : ℕ) (hn : 3 ≤ n) (σ : Equiv.Perm (Fin (n ^ 2 - 1)))
    (hσ : σ.partition.parts = (Multiset.range (n - 1)).map (fun i => 2 * i + 3)) :
    Equiv.Perm.sign σ = 1 ∧ ¬ IsFullCycle σ := by
  have hct : σ.cycleType = (Multiset.range (n - 1)).map (fun i => 2 * i + 3) := by
    rw [← Equiv.Perm.filter_parts_partition_eq_cycleType, hσ, Multiset.filter_eq_self]
    exact fun a ha => two_le_of_mem_hooks ha
  have hcard : Multiset.card σ.cycleType = n - 1 := by rw [hct]; simp
  refine ⟨?_, ?_⟩
  · rw [Equiv.Perm.sign_of_cycleType, hcard, hct, hooks_sum n (by omega)]
    exact (even_hooks_exponent n (by omega)).neg_one_pow
  · rintro ⟨hcyc, -⟩
    have := Equiv.Perm.card_cycleType_eq_one.2 hcyc
    omega

end NagataHigman.Proofs

end
