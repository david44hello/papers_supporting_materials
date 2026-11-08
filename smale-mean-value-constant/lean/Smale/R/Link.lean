/-
Smale/R/Link.lean — From the invertibility of the Schur-Cohn matrix on [0, 1] to fact (R), the nonvanishing resultant.
-/
import Smale.Defs.Conditions
import Smale.Proofs.Parity
import Smale.Proofs.DataPoly
import Smale.R.Schur

namespace Smale.RCheck

open Polynomial Complex ComplexConjugate Finset

/-- The coefficients of `P_c` for our data. -/
noncomputable def pData (c : ℝ) (l : ℕ) : ℂ :=
  Hdata.coeff (l + 1) * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)

theorem eval_P (c : ℝ) (w : ℂ) :
    (dieudonne Hdata 18 c).eval w = ∑ l ∈ range 18, pData c l * w ^ l := by
  simp [dieudonne, pData, eval_finsetSum]

theorem eval_Pstar (c : ℝ) (w : ℂ) :
    (dieudonneStar Hdata 18 c).eval w = ∑ l ∈ range 18, conj (pData c l) * w ^ (17 - l) := by
  simp only [dieudonneStar, pData, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_mul, Complex.conj_ofReal]

theorem no_common_zero (c : ℝ) (hdet : (schurB 17 (pData c)).det ≠ 0) (w : ℂ)
    (h1 : (dieudonne Hdata 18 c).eval w = 0) (h2 : (dieudonneStar Hdata 18 c).eval w = 0) : False := by
  rw [eval_P] at h1
  rw [eval_Pstar] at h2
  exact hdet (schurB_det_eq_zero_of_common_zero 17 (by norm_num) _ w h1 h2)

theorem pData_neg (c : ℝ) (l : ℕ) : pData (-c) l = (-1) ^ l * pData c l := by
  simp only [pData]
  rw [U_eval_neg_real]
  push_cast
  ring

/-- A common zero for `-c` at `w` is a common zero for `c` at `-w`. -/
theorem no_common_zero_neg (c : ℝ) (hdet : (schurB 17 (pData c)).det ≠ 0) (w : ℂ)
    (h1 : (dieudonne Hdata 18 (-c)).eval w = 0) (h2 : (dieudonneStar Hdata 18 (-c)).eval w = 0) : False := by
  rw [eval_P] at h1
  rw [eval_Pstar] at h2
  refine no_common_zero c hdet (-w) ?_ ?_
  · rw [eval_P, ← h1]
    refine sum_congr rfl fun l _ => ?_
    rw [pData_neg, neg_pow w l]
    ring
  · rw [eval_Pstar]
    have hflip : ∑ l ∈ range 18, conj (pData c l) * (-w) ^ (17 - l) =
        -∑ l ∈ range 18, conj (pData (-c) l) * w ^ (17 - l) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l hl => ?_
      have hsign : (-1 : ℂ) ^ (17 - l) = -(-1) ^ l := by
        have hl' := mem_range.1 hl
        interval_cases l <;> norm_num
      rw [pData_neg, neg_pow w, hsign, map_mul, map_pow, map_neg, map_one]
      ring
    rw [hflip, h2, neg_zero]

theorem Hdata_coeff_one_ne : Hdata.coeff 1 ≠ 0 := by
  rw [Exact.Hdata_eq, Exact.coeff_toPoly]
  intro h
  rw [Exact.GQ.toC_eq_zero_iff] at h
  revert h
  decide +kernel

theorem Pstar_coeff17 (c : ℝ) : (dieudonneStar Hdata 18 c).coeff 17 = conj (Hdata.coeff 1) := by
  rw [dieudonneStar, finsetSum_coeff, sum_eq_single 0]
  · simp
  · intro b hb hb0
    have hb' := mem_range.1 hb
    rw [coeff_C_mul_X_pow, ite_eq_right_iff]
    intro hcontra
    omega
  · intro h
    exact absurd (mem_range.2 (by norm_num)) h

theorem P_natDegree_le (c : ℝ) : (dieudonne Hdata 18 c).natDegree ≤ 17 := by
  refine natDegree_sum_le_of_forall_le _ _ fun l hl => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (mem_range.1 hl))

theorem Pstar_natDegree (c : ℝ) : (dieudonneStar Hdata 18 c).natDegree = 17 := by
  apply le_antisymm
  · refine natDegree_sum_le_of_forall_le _ _ fun l _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · apply le_natDegree_of_ne_zero
    rw [Pstar_coeff17]
    exact (_root_.map_ne_zero (starRingEnd ℂ)).2 Hdata_coeff_one_ne

/-- No common zero means a nonzero resultant, at the formal degrees `(17, 17)`. -/
theorem res_ne_of_no_common_zero (c : ℝ)
    (hno : ∀ w : ℂ, (dieudonne Hdata 18 c).eval w = 0 → (dieudonneStar Hdata 18 c).eval w = 0 → False) :
    resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) 17 17 ≠ 0 := by
  have hPdeg := P_natDegree_le c
  have hQdeg := Pstar_natDegree c
  have hQc : (dieudonneStar Hdata 18 c).coeff 17 ≠ 0 := by
    rw [Pstar_coeff17]
    exact (_root_.map_ne_zero (starRingEnd ℂ)).2 Hdata_coeff_one_ne
  intro hres
  obtain ⟨k, hk⟩ : ∃ k, 17 = (dieudonne Hdata 18 c).natDegree + k :=
    ⟨17 - (dieudonne Hdata 18 c).natDegree, by omega⟩
  have hstep := resultant_add_left_deg (f := dieudonne Hdata 18 c) (g := dieudonneStar Hdata 18 c)
    (m := (dieudonne Hdata 18 c).natDegree) (n := 17) (k := k) le_rfl
  rw [← hk, hres] at hstep
  have hne : (-1 : ℂ) ^ (17 * k) * (dieudonneStar Hdata 18 c).coeff 17 ^ k ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hQc)
  have hres' : resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) = 0 := by
    rw [hQdeg]
    exact (mul_eq_zero.1 hstep.symm).resolve_left hne
  obtain ⟨-, hnc⟩ := resultant_eq_zero_iff.1 hres'
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ] at hnc
  obtain ⟨a, ha⟩ := not_forall.1 hnc
  rw [not_or, not_not, not_not] at ha
  exact hno a (by simpa using ha.1) (by simpa using ha.2)

/-- Fact (R), from the invertibility of `schurB` on `[0, 1]`. -/
theorem condR_of_det (hdet : ∀ c : ℝ, c ∈ Set.Icc (0 : ℝ) 1 → (schurB 17 (pData c)).det ≠ 0) : CondRdata := by
  intro c hc
  apply res_ne_of_no_common_zero
  intro w h1 h2
  rcases le_total 0 c with h0 | h0
  · exact no_common_zero c (hdet c ⟨h0, hc.2⟩) w h1 h2
  · have hneg : -(-c) = c := neg_neg c
    rw [← hneg] at h1 h2
    exact no_common_zero_neg (-c) (hdet (-c) ⟨by linarith, by linarith [hc.1]⟩) w h1 h2

end Smale.RCheck
