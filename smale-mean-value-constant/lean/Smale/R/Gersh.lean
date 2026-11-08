/-
Smale/R/Gersh.lean — Strict row dominance after a congruence gives an invertible matrix; the bound |U_l(c)| <= l + 1.
-/
import Mathlib

namespace Smale.RCheck

open Matrix Finset Polynomial

/-- If `A M A*` is strictly row dominant, then `M` is invertible. `A` needs no hypothesis. -/
theorem det_ne_zero_of_congr_dominant {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ j, ∑ t ∈ univ.erase j, ‖(A * M * Aᴴ) j t‖ < ‖(A * M * Aᴴ) j j‖) : M.det ≠ 0 := by
  have hd := det_ne_zero_of_sum_row_lt_diag h
  intro h0
  apply hd
  rw [det_mul, det_mul, h0]
  simp

/-- A matrix with a dominant real diagonal stays strictly row dominant under a small perturbation. -/
theorem dominant_of_perturbation {n : ℕ} (G0 R : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ j, ∑ t ∈ univ.erase j, ‖G0 j t‖ + ∑ t, ‖R j t‖ < (G0 j j).re) :
    ∀ j, ∑ t ∈ univ.erase j, ‖(G0 + R) j t‖ < ‖(G0 + R) j j‖ := by
  intro j
  have h1 : ∑ t ∈ univ.erase j, ‖(G0 + R) j t‖ ≤
      ∑ t ∈ univ.erase j, ‖G0 j t‖ + ∑ t ∈ univ.erase j, ‖R j t‖ := by
    rw [← sum_add_distrib]
    exact sum_le_sum fun t _ => norm_add_le _ _
  have h2 : ∑ t ∈ univ.erase j, ‖R j t‖ + ‖R j j‖ = ∑ t, ‖R j t‖ :=
    sum_erase_add _ _ (mem_univ j)
  have h3 : ((G0 + R) j j).re ≤ ‖(G0 + R) j j‖ := Complex.re_le_norm _
  have h4 : -‖R j j‖ ≤ (R j j).re := (abs_le.1 (Complex.abs_re_le_norm (R j j))).1
  have h5 : ((G0 + R) j j).re = (G0 j j).re + (R j j).re := by simp
  linarith [h j]

theorem abs_sin_nat_mul_le (n : ℕ) (θ : ℝ) : |Real.sin (n * θ)| ≤ n * |Real.sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : ((n + 1 : ℕ) : ℝ) * θ = n * θ + θ := by
      push_cast
      ring
    rw [hsplit, Real.sin_add]
    have h1 : |Real.sin (n * θ) * Real.cos θ + Real.cos (n * θ) * Real.sin θ| ≤
        |Real.sin (n * θ)| * |Real.cos θ| + |Real.cos (n * θ)| * |Real.sin θ| := by
      rw [← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    have h2 : |Real.sin (n * θ)| * |Real.cos θ| ≤ |Real.sin (n * θ)| * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg _)
    have h3 : |Real.cos (n * θ)| * |Real.sin θ| ≤ 1 * |Real.sin θ| :=
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)
    push_cast
    linarith

/-- `|U_l(c)| ≤ l + 1` on `[-1, 1]`. -/
theorem abs_U_le (l : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    |(Chebyshev.U ℝ (l : ℤ)).eval c| ≤ l + 1 := by
  have hcos : Real.cos (Real.arccos c) = c := Real.cos_arccos hc.1 hc.2
  set θ := Real.arccos c with hθ
  by_cases hs : Real.sin θ = 0
  · have hsq : c ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [hs, hcos] at this
      linarith
    have hone : (Chebyshev.U ℝ (l : ℤ)).eval 1 = l + 1 := by
      rw [Chebyshev.U_eval_one]
      simp
    have habs : |((l : ℝ) + 1)| = l + 1 := abs_of_nonneg (by positivity)
    have hcases : c = 1 ∨ c = -1 := by
      have hprod : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 hprod with h | h
      · left; linarith
      · right; linarith
    rcases hcases with h1 | h1
    · rw [h1, hone, habs]
    · rw [h1, Chebyshev.U_eval_neg_one, Int.cast_negOnePow_natCast, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul]
      simpa using habs.le
  · have hmul : (Chebyshev.U ℝ (l : ℤ)).eval c * Real.sin θ = Real.sin ((l + 1) * θ) := by
      have := Chebyshev.U_real_cos θ (l : ℤ)
      rw [hcos] at this
      simpa using this
    have hbound := abs_sin_nat_mul_le (l + 1) θ
    have hpos : 0 < |Real.sin θ| := abs_pos.2 hs
    have hle : |(Chebyshev.U ℝ (l : ℤ)).eval c| * |Real.sin θ| ≤ ((l : ℝ) + 1) * |Real.sin θ| := by
      rw [← abs_mul, hmul]
      simpa using hbound
    exact le_of_mul_le_mul_right hle hpos

end Smale.RCheck
