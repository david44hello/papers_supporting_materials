/-
NagataHigman/Proofs/RectangleCommutant.lean — v1.02 Remark 4.3 (cut in v1.03), the "fails for rectangles" half, in its true form: for a
rectangle with at least two rows and two columns, some non-scalar operator commutes with every star `Y_j`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: every `Y_j` is one scalar `cc • 1` (Section4Remarks.rhoAlg_starElem_rectangle), so EVERY matrix commutes with
the stars; and `f^λ ≥ 2` because the column-reading and the row-reading tableaux differ (entry 1 sits at `(1,0)` in one
and at `(0,1)` in the other), so the matrix unit `diag(1, 0, …)` is not a scalar. For one row or one column `f^λ = 1`
and the commutant IS the scalars, so the hypotheses `2 ≤ r`, `2 ≤ c` are needed.
-/
import NagataHigman.Proofs.Section4Remarks

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] {N : ℕ}

/-- A rectangle with at least two rows and two columns has two different standard tableaux. -/
theorem exists_syt_ne_of_rectangle (lam : Shape N) (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c)
    (hrect : lam.parts = Multiset.replicate r c) : ∃ T T' : SYT lam, T ≠ T' := by
  have hrows : 1 + 1 ≤ lam.numRows := lt_numRows_of_mem ((rect_mem hrect 1 0).2 ⟨by omega, by omega⟩)
  have hcols : 1 + 1 ≤ lam.firstRow := lt_firstRow_of_mem ((rect_mem hrect 0 1).2 ⟨by omega, by omega⟩)
  have hN : 2 ≤ N := by
    have := lam.parts_sum
    rw [hrect, Multiset.sum_replicate, smul_eq_mul] at this
    nlinarith
  obtain ⟨T, hT⟩ := exists_col_tableau lam 1 hrows
  obtain ⟨T', hT'⟩ := exists_row_tableau lam 1 hcols
  refine ⟨T, T', fun h => ?_⟩
  have h1 := hT ⟨1, by omega⟩ le_rfl
  rw [h, hT' ⟨1, by omega⟩ le_rfl] at h1
  simp at h1

namespace YoungSystem

variable (Y : YoungSystem F N)

/-- A rectangle with at least two rows and two columns has `f^λ ≥ 2`. -/
theorem two_le_dim_of_rectangle (lam : Shape N) (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c)
    (hrect : lam.parts = Multiset.replicate r c) : 2 ≤ Y.dim lam := by
  obtain ⟨b, -⟩ := Y.youngBasis lam
  have := FiniteDimensional.fintypeBasisIndex b
  have h := Module.finrank_eq_card_basis b
  rw [Module.finrank_fin_fun] at h
  rw [h]
  exact Fintype.one_lt_card_iff.2 (exists_syt_ne_of_rectangle lam r c hr hc hrect)

/-- **v1.02 Remark 4.3 (cut in v1.03)** ("Lemma 4.2 fails for rectangles", v1.02 tex 446), true form: for a rectangle with at least two rows and
two columns, some operator commutes with every star `Y_j` but is not a scalar. -/
theorem rem_4_3_rectangle_fails (lam : Shape N) (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c)
    (hrect : lam.parts = Multiset.replicate r c) :
    ∃ Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
      (∀ j : Fin N, Z * Y.rhoAlg lam (starElem F j) = Y.rhoAlg lam (starElem F j) * Z) ∧
        ¬ ∃ cc : F, Z = cc • 1 := by
  have hd := two_le_dim_of_rectangle Y lam r c hr hc hrect
  let i0 : Fin (Y.dim lam) := ⟨0, by omega⟩
  let i1 : Fin (Y.dim lam) := ⟨1, by omega⟩
  obtain ⟨cc, hcc⟩ := rhoAlg_starElem_rectangle Y lam r c hrect
  refine ⟨Matrix.diagonal fun i => if i = i0 then 1 else 0, fun j => ?_, ?_⟩
  · rw [hcc j, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  · rintro ⟨cc', hcc'⟩
    have h0 := congrFun (congrFun hcc' i0) i0
    have h1 := congrFun (congrFun hcc' i1) i1
    have hne : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hne,
      ↓reduceIte] at h0 h1
    rw [← h0] at h1
    exact one_ne_zero h1.symm

end YoungSystem

end NagataHigman.Proofs

end
