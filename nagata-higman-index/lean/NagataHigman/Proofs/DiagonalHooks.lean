/-
NagataHigman/Proofs/DiagonalHooks.lean — fact (T3), l. 429-430: the diagonal hooks of a self-conjugate shape are
distinct odd numbers with sum N, so h(λ) is a cycle type of S_N (the sum holds for every shape).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.Young
import NagataHigman.Proofs.Shapes

noncomputable section

namespace NagataHigman.Proofs.DiagonalHooks

open NagataHigman

/-! ## Symmetric diagrams -/

/-- A self-conjugate shape has a symmetric diagram. -/
theorem diagram_transpose_eq {N : ℕ} (lam : Shape N) (h : lam.conjugate = lam) :
    lam.diagram.transpose = lam.diagram := by
  have h2 : YoungDiagram.ofPartition lam.conjugate = (YoungDiagram.ofPartition lam).transpose :=
    YoungDiagram.ofPartition_toPartition _
  rw [h] at h2
  exact h2.symm

/-- In a symmetric diagram, column `i` is as long as row `i`. -/
theorem colLen_eq_rowLen {N : ℕ} (lam : Shape N) (h : lam.conjugate = lam) (i : ℕ) :
    lam.diagram.colLen i = lam.diagram.rowLen i := by
  rw [← YoungDiagram.rowLen_transpose, diagram_transpose_eq lam h]

/-- Membership in the index set of `diagonalHooks`. -/
theorem mem_diag_index {N : ℕ} {lam : Shape N} {i : ℕ}
    (hi : i ∈ ((Finset.range N).filter (fun i => (i, i) ∈ lam.diagram.cells)).val) :
    (i, i) ∈ lam.diagram := by
  have h1 := Finset.mem_filter.1 (Finset.mem_def.2 hi)
  exact (YoungDiagram.mem_cells _).1 h1.2

/-! ## Odd and distinct -/

theorem diagonalHooks_odd {N : ℕ} (lam : Shape N) (h : lam.conjugate = lam) :
    ∀ x ∈ lam.diagonalHooks, Odd x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
  have hlt := YoungDiagram.mem_iff_lt_rowLen.1 (mem_diag_index hi)
  rw [colLen_eq_rowLen lam h]
  exact ⟨lam.diagram.rowLen i - i - 1, by omega⟩

theorem diagonalHooks_nodup {N : ℕ} (lam : Shape N) (h : lam.conjugate = lam) :
    lam.diagonalHooks.Nodup := by
  refine Multiset.Nodup.map_on ?_ (Finset.nodup _)
  intro i hi j hj hij
  have hi' := YoungDiagram.mem_iff_lt_rowLen.1 (mem_diag_index hi)
  have hj' := YoungDiagram.mem_iff_lt_rowLen.1 (mem_diag_index hj)
  simp only [colLen_eq_rowLen lam h] at hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have := lam.diagram.rowLen_anti i j hlt.le
    omega
  · exact heq
  · have := lam.diagram.rowLen_anti j i hgt.le
    omega

/-! ## Sum: every cell lies in exactly one diagonal hook -/

/-- The cells `(a, b)` with `min a b = i` form the hook of `(i, i)`: its arm row and its leg column. -/
theorem fiber_eq (μ : YoungDiagram) (i : ℕ) :
    μ.cells.filter (fun c => min c.1 c.2 = i) =
      ({i} ×ˢ Finset.Ico i (μ.rowLen i)) ∪ (Finset.Ioo i (μ.colLen i) ×ˢ {i}) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico, Finset.mem_Ioo]
  constructor
  · rintro ⟨hc, hm⟩
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab] at hm
      subst hm
      exact Or.inl ⟨rfl, hab, YoungDiagram.mem_iff_lt_rowLen.1 hc⟩
    · rw [min_eq_right hab] at hm
      subst hm
      rcases eq_or_lt_of_le hab with heq | hlt
      · subst heq
        exact Or.inl ⟨rfl, le_rfl, YoungDiagram.mem_iff_lt_rowLen.1 hc⟩
      · exact Or.inr ⟨⟨hlt, YoungDiagram.mem_iff_lt_colLen.1 hc⟩, rfl⟩
  · rintro (⟨rfl, h1, h2⟩ | ⟨⟨h1, h2⟩, rfl⟩)
    · exact ⟨YoungDiagram.mem_iff_lt_rowLen.2 h2, min_eq_left h1⟩
    · exact ⟨YoungDiagram.mem_iff_lt_colLen.2 h2, min_eq_right h1.le⟩

/-- The hook of a diagonal cell `(i, i)` has `rowLen i + colLen i - 2 i - 1` cells. -/
theorem fiber_card (μ : YoungDiagram) (i : ℕ) (hi : (i, i) ∈ μ) :
    (μ.cells.filter (fun c => min c.1 c.2 = i)).card = μ.rowLen i + μ.colLen i - 2 * i - 1 := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.1 hi
  have hc := YoungDiagram.mem_iff_lt_colLen.1 hi
  have hdisj : Disjoint ({i} ×ˢ Finset.Ico i (μ.rowLen i)) (Finset.Ioo i (μ.colLen i) ×ˢ {i}) := by
    refine Finset.disjoint_left.2 fun c hc1 hc2 => ?_
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico, Finset.mem_Ioo] at hc1 hc2
    omega
  rw [fiber_eq, Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_singleton, Nat.card_Ico, Nat.card_Ioo]
  omega

/-- Summing the diagonal hook lengths counts every cell once (for any Young diagram). -/
theorem sum_hooks_eq_card (μ : YoungDiagram) (D : Finset ℕ) (hD : ∀ i, i ∈ D ↔ (i, i) ∈ μ) :
    ∑ i ∈ D, (μ.rowLen i + μ.colLen i - 2 * i - 1) = μ.cells.card := by
  rw [Finset.card_eq_sum_card_fiberwise (s := μ.cells) (t := D) (f := fun c : ℕ × ℕ => min c.1 c.2)]
  · exact Finset.sum_congr rfl fun i hi => (fiber_card μ i ((hD i).1 hi)).symm
  · intro c hc
    rw [Finset.mem_coe] at hc
    show min c.1 c.2 ∈ D
    rw [hD]
    exact μ.up_left_mem (min_le_left _ _) (min_le_right _ _) ((YoungDiagram.mem_cells c).1 hc)

/-- A diagonal cell `(i, i)` of `λ ⊢ N` has `i < N`. -/
theorem diag_lt {N : ℕ} (lam : Shape N) {i : ℕ} (hi : (i, i) ∈ lam.diagram) : i < N := by
  have h1 := YoungDiagram.mem_iff_lt_rowLen.1 hi
  have h2 : (lam.diagram.row i).card ≤ lam.diagram.cells.card := Finset.card_filter_le _ _
  have h3 : lam.diagram.cells.card = N := YoungDiagram.card_ofPartition lam
  rw [YoungDiagram.rowLen_eq_card] at h1
  omega

/-- The diagonal hooks of any shape sum to `N` (self-conjugacy is not needed). -/
theorem diagonalHooks_sum_general {N : ℕ} (lam : Shape N) : lam.diagonalHooks.sum = N := by
  have hD : ∀ i, i ∈ (Finset.range N).filter (fun i => (i, i) ∈ lam.diagram.cells) ↔ (i, i) ∈ lam.diagram :=
    fun i => by
      rw [Finset.mem_filter, Finset.mem_range, YoungDiagram.mem_cells]
      exact ⟨fun hh => hh.2, fun hh => ⟨diag_lt lam hh, hh⟩⟩
  unfold Shape.diagonalHooks
  rw [← Finset.sum_eq_multiset_sum, sum_hooks_eq_card _ _ hD]
  exact YoungDiagram.card_ofPartition lam

theorem diagonalHooks_sum {N : ℕ} (lam : Shape N) (_h : lam.conjugate = lam) :
    lam.diagonalHooks.sum = N :=
  diagonalHooks_sum_general lam

/-! ## A cycle type of `S_N` -/

/-- A multiset of positive integers summing to `N` is the cycle partition of some permutation of `Fin N`. -/
theorem exists_perm_parts_eq {N : ℕ} (H : Multiset ℕ) (hpos : ∀ x ∈ H, 1 ≤ x) (hsum : H.sum = N) :
    ∃ σ : Equiv.Perm (Fin N), σ.partition.parts = H := by
  have hones : H.filter (fun x => ¬ 2 ≤ x) = Multiset.replicate (H.count 1) 1 := by
    rw [← Multiset.filter_eq' H 1]
    exact Multiset.filter_congr fun x hx => by have := hpos x hx; omega
  have hsplit : H.filter (2 ≤ ·) + Multiset.replicate (H.count 1) 1 = H := by
    rw [← hones]
    exact Multiset.filter_add_not _ H
  have hsum2 : (H.filter (2 ≤ ·)).sum + H.count 1 = N := by
    have := congrArg Multiset.sum hsplit
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one] at this
    rw [this, hsum]
  have hex : ∃ σ : Equiv.Perm (Fin N), σ.cycleType = H.filter (2 ≤ ·) :=
    (Equiv.Perm.exists_with_cycleType_iff (Fin N)).2
      ⟨by rw [Fintype.card_fin]; omega, fun a ha => (Multiset.mem_filter.1 ha).2⟩
  obtain ⟨σ, hσ⟩ := hex
  have hcount : N - (H.filter (2 ≤ ·)).sum = H.count 1 := by omega
  refine ⟨σ, ?_⟩
  rw [Equiv.Perm.parts_partition, ← Equiv.Perm.sum_cycleType, hσ, Fintype.card_fin, hcount]
  exact hsplit

theorem diagonalHooks_cycleType {N : ℕ} (lam : Shape N) (h : lam.conjugate = lam) :
    ∃ σ : Equiv.Perm (Fin N), σ.partition.parts = lam.diagonalHooks :=
  exists_perm_parts_eq _ (fun x hx => (diagonalHooks_odd lam h x hx).pos) (diagonalHooks_sum lam h)

/-! ## The hook formula -/

/-- For `λ = λ'`, the hook length of the diagonal cell `(i, i)` (0-indexed; row `i` has length `λ_{i+1}`) is
`2 (λ_{i+1} - (i+1)) + 1`, the paper's `h_{ii} = 2(λ_i - i) + 1` in 1-indexed rows. -/
theorem diagonalHooks_eq_formula {N : ℕ} (lam : Shape N) (h : lam.conjugate = lam) :
    lam.diagonalHooks = ((Finset.range N).filter (fun i => (i, i) ∈ lam.diagram.cells)).val.map
      (fun i => 2 * (lam.diagram.rowLen i - (i + 1)) + 1) := by
  classical
  unfold Shape.diagonalHooks
  refine Multiset.map_congr (by congr) (fun i hi => ?_)
  have hlt := YoungDiagram.mem_iff_lt_rowLen.1 (mem_diag_index hi)
  rw [colLen_eq_rowLen lam h]
  omega

end NagataHigman.Proofs.DiagonalHooks

end
