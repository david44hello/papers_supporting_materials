/-
Smale/Proofs/ResScaling.lean — `thm_5_1_R_scaling` (tex l.402-404): multiplying `H` by a positive integer `L`
multiplies `Res_w(P_c, P_c*)` (formal degrees `n-1, n-1`) by `L^(2(n-1)) > 0`.
-/
import Smale.Defs.Basic

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

theorem dieudonne_C_mul (H : ℂ[X]) (n : ℕ) (L : ℝ) (c : ℝ) :
    dieudonne (C (L : ℂ) * H) n c = C (L : ℂ) * dieudonne H n c := by
  rw [dieudonne, dieudonne, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [coeff_C_mul, mul_assoc, C_mul, mul_assoc]

theorem dieudonneStar_C_mul (H : ℂ[X]) (n : ℕ) (L : ℝ) (c : ℝ) :
    dieudonneStar (C (L : ℂ) * H) n c = C (L : ℂ) * dieudonneStar H n c := by
  rw [dieudonneStar, dieudonneStar, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [coeff_C_mul, map_mul, Complex.conj_ofReal]
  ring

/-- `thm_5_1_R_scaling`, proved (any real `L > 0`, in particular a positive integer). -/
theorem thm_5_1_R_scaling_proved :
    ∀ (H : ℂ[X]) (n : ℕ) (L : ℕ), 0 < L → ∃ κ : ℝ, 0 < κ ∧ ∀ c : ℝ,
      resultant (dieudonne (C (L : ℂ) * H) n c) (dieudonneStar (C (L : ℂ) * H) n c) (n - 1) (n - 1) =
        κ * resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) := by
  intro H n L hL
  refine ⟨(L : ℝ) ^ (2 * (n - 1)), pow_pos (by exact_mod_cast hL) _, fun c => ?_⟩
  have e : (L : ℂ) = ((L : ℝ) : ℂ) := by push_cast; rfl
  rw [e, dieudonne_C_mul, dieudonneStar_C_mul, resultant_C_mul_left, resultant_C_mul_right]
  push_cast
  ring

end Smale.Exact
