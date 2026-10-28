/-
Smale/Proofs/Dieudonne.lean — the identities of the Dieudonné polynomials `P_c` (tex l.228-235, l.435):
`H(ze^{iθ}) - H(ze^{-iθ}) = 2i sin θ · z P_{cos θ}(z)`, `P₁ = H'`, `P_c(0) = h₁`, `P_{-1}(w) = H'(-w)`.
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial Complex

/-- The coefficients of `P_c`: `h_{m+1} U_m(c)` for `m < n`, and `0` above. -/
theorem coeff_dieudonne (H : ℂ[X]) (n : ℕ) (c : ℝ) (m : ℕ) :
    (dieudonne H n c).coeff m =
      if m < n then H.coeff (m + 1) * (((Chebyshev.U ℝ (m : ℤ)).eval c : ℝ) : ℂ) else 0 := by
  simp only [dieudonne, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]

/-- The value of `P_c` at `w`, as a sum. -/
theorem eval_dieudonne (H : ℂ[X]) (n : ℕ) (c : ℝ) (w : ℂ) :
    (dieudonne H n c).eval w =
      ∑ l ∈ Finset.range n, H.coeff (l + 1) * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ) * w ^ l := by
  simp only [dieudonne, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- `P₁ = H'` (tex l.231-232: `U_{ℓ-1}(1) = ℓ`), for every formal degree `n ≥ deg H`. -/
theorem dieudonne_one (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) : dieudonne H n 1 = H.derivative := by
  ext m
  rw [coeff_dieudonne, coeff_derivative]
  split_ifs with hm
  · simp [Chebyshev.U_eval_one]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- `P_c(0) = h₁` (tex l.232). -/
theorem dieudonne_eval_zero (H : ℂ[X]) (n : ℕ) (hn1 : 1 ≤ n) (c : ℝ) : (dieudonne H n c).eval 0 = H.coeff 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_dieudonne]
  simp [show 0 < n by omega]

/-- tex l.231-232, exactly the Statements type: `P₁ = H'` and `P_c(0) = h₁`. -/
theorem sec4_P_one_proved (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (hn1 : 1 ≤ n) :
    dieudonne H n 1 = H.derivative ∧ ∀ c : ℝ, (dieudonne H n c).eval 0 = H.coeff 1 :=
  ⟨dieudonne_one H n hn, dieudonne_eval_zero H n hn1⟩

/-- `e^{ix} - e^{-ix} = 2i sin x`, for `x = m θ`. -/
theorem exp_sub_exp_neg (m : ℕ) (θ : ℝ) :
    exp ((m : ℂ) * (θ * I)) - exp ((m : ℂ) * -(θ * I)) = 2 * I * Complex.sin (m * θ) := by
  rw [Complex.sin, show (m : ℂ) * -(θ * I) = -(m * θ) * I by ring, show (m : ℂ) * (θ * I) = (m * θ) * I by ring]
  linear_combination (exp (↑m * ↑θ * I) - exp (-(↑m * ↑θ) * I)) * I_sq

/-- `U_l(cos θ) sin θ = sin((l + 1)θ)`, in `ℂ`. -/
theorem U_cos_mul_sin (l : ℕ) (θ : ℝ) :
    (((Chebyshev.U ℝ (l : ℤ)).eval (Real.cos θ) : ℝ) : ℂ) * (Real.sin θ : ℂ) =
      Complex.sin (((l + 1 : ℕ) : ℂ) * θ) := by
  rw [← Complex.ofReal_mul, Chebyshev.U_real_cos, Complex.ofReal_sin]
  congr 1
  push_cast
  ring

/-- tex l.231, exactly the Statements type: `H(ze^{iθ}) - H(ze^{-iθ}) = 2i sin θ · z P_c(z)`, `c = cos θ`. -/
theorem sec4_dieudonne_identity_proved (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (θ : ℝ) (z : ℂ) :
    H.eval (z * exp (θ * I)) - H.eval (z * exp (-(θ * I))) =
      2 * I * Real.sin θ * z * (dieudonne H n (Real.cos θ)).eval z := by
  have hlt : H.natDegree < n + 1 := Nat.lt_succ_of_le hn
  rw [eval_eq_sum_range' hlt, eval_eq_sum_range' hlt, ← Finset.sum_sub_distrib, Finset.sum_range_succ',
    eval_dieudonne, Finset.mul_sum]
  simp only [pow_zero, mul_one, sub_self, add_zero]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have key := exp_sub_exp_neg (l + 1) θ
  have hU := U_cos_mul_sin l θ
  linear_combination (H.coeff (l + 1) * z ^ (l + 1)) * key + (-(2 * I * H.coeff (l + 1) * z ^ (l + 1))) * hU

/-- `U_l(-1) = (-1)^l U_l(1)`. -/
theorem U_eval_neg_one' (l : ℕ) :
    (Chebyshev.U ℝ (l : ℤ)).eval (-1) = (-1) ^ l * (Chebyshev.U ℝ (l : ℤ)).eval 1 := by
  rw [Chebyshev.U_eval_neg, Int.cast_negOnePow_natCast]

/-- Remark 5.2 (tex l.435), exactly the Statements type: `P_{±1}(w) = H'(±w)`. -/
theorem rem_5_2_P_pm_one_proved (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (w : ℂ) :
    (dieudonne H n 1).eval w = H.derivative.eval w ∧ (dieudonne H n (-1)).eval w = H.derivative.eval (-w) := by
  refine ⟨by rw [dieudonne_one H n hn], ?_⟩
  rw [← dieudonne_one H n hn, eval_dieudonne, eval_dieudonne]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [U_eval_neg_one' l, neg_pow]
  push_cast
  ring

end Smale
