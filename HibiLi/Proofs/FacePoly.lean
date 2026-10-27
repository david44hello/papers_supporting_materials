/-
HibiLi/Proofs/FacePoly.lean — coefficients of face polynomials and of the gap polynomial.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi.Proofs

open HibiLi Polynomial

variable {ι : Type*} [Fintype ι]

/-- Every set in `ι → ℝ` has affine dimension at most `card ι`. -/
lemma adim_le_card (F : Set (ι → ℝ)) : adim F ≤ Fintype.card ι := by
  unfold adim
  calc Module.finrank ℝ (vectorSpan ℝ F) ≤ Module.finrank ℝ (ι → ℝ) := Submodule.finrank_le _
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℝ

/-- No face has dimension above the ambient dimension, so `f_k = 0` for `k > card ι`. -/
lemma fNum_eq_zero_of_card_lt (Q : Set (ι → ℝ)) {k : ℕ} (hk : Fintype.card ι < k) : fNum Q k = 0 := by
  have hempty : faces Q k = ∅ := by
    ext F
    simp only [faces, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hF
    exact absurd (hF ▸ adim_le_card F) (not_le.mpr hk)
  simp [fNum, hempty]

/-- The `k`-th coefficient of the face polynomial is `f_k`. -/
lemma facePoly_coeff (Q : Set (ι → ℝ)) (k : ℕ) : (facePoly Q).coeff k = (fNum Q k : ℤ) := by
  unfold facePoly facePolyUpTo
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hk : k ≤ Fintype.card ι
  · rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_of_le hk]
  · rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff, hk, ite_false]
    rw [fNum_eq_zero_of_card_lt Q (not_le.mp hk)]
    simp

/-- Coefficients of `t^2 (1+t)^{n-3}`: `C(n−3, k−2)` for `k ≥ 2`, and `0` for `k < 2`. -/
lemma gapPoly_coeff (n k : ℕ) :
    (gapPoly n).coeff k = if 2 ≤ k then (Nat.choose (n - 3) (k - 2) : ℤ) else 0 := by
  unfold gapPoly
  rw [coeff_X_pow_mul', coeff_one_add_X_pow]

end HibiLi.Proofs
