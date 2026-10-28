/-
Smale/Proofs/Sec1Exact.lean — two claims of Section 1: `sec1_example` (`p = z - z^d/d` lies in `𝓟_d` and has
`m(p) = (d-1)/d`, so `K(d) ≥ (d-1)/d`) and `intro_improves_JN` (for `d ≥ 452`, `4 - 0.00597/(d log d)` is below
`4 - 529(log 2)²/(576d²)`; uses `log x / x` decreasing on `[e, ∞)`, Mathlib's bounds for `log 2`, and the series of
`log(1 - x)` at `x = 15/128` for `log 452 = 9 log 2 + log(113/128)`).
-/
import Smale.Defs.Basic

namespace Smale.Exact

open Polynomial Complex

/-- `p = z - z^d/d`. -/
noncomputable def pEx (d : ℕ) : ℂ[X] := X - C (1 / (d : ℂ)) * X ^ d

theorem pEx_derivative (d : ℕ) (hd : 2 ≤ d) : (pEx d).derivative = 1 - X ^ (d - 1) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [pEx, derivative_sub, derivative_X, derivative_C_mul_X_pow,
    show (1 / (d : ℂ)) * (d : ℂ) = 1 by field_simp, map_one, one_mul]

theorem pEx_isPd (d : ℕ) (hd : 2 ≤ d) : IsPd d (pEx d) := by
  have hc : (1 / (d : ℂ)) ≠ 0 := one_div_ne_zero (by exact_mod_cast (show d ≠ 0 by omega))
  have hq : (C (1 / (d : ℂ)) * X ^ d).natDegree = d := natDegree_C_mul_X_pow d _ hc
  have hlt : (X : ℂ[X]).natDegree < (C (1 / (d : ℂ)) * X ^ d).natDegree := by rw [hq, natDegree_X]; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [pEx, natDegree_sub_eq_right_of_natDegree_lt hlt, hq]
  · simp [pEx, zero_pow (show d ≠ 0 by omega)]
  · rw [pEx_derivative d hd]; simp [zero_pow (show d - 1 ≠ 0 by omega)]

/-- At a critical point `β` (`β^{d-1} = 1`), `|p(β)|/|β| = (d-1)/d`. -/
theorem pEx_ratio (d : ℕ) (hd : 2 ≤ d) (β : ℂ) (hβ : β ^ (d - 1) = 1) :
    ‖(pEx d).eval β‖ / ‖β‖ = ((d : ℝ) - 1) / d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow (show d - 1 ≠ 0 by omega)] at hβ
    exact zero_ne_one hβ
  have hpow : β ^ d = β * β ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  have he : (pEx d).eval β = β * (((1 - 1 / (d : ℝ) : ℝ)) : ℂ) := by
    simp only [pEx, eval_sub, eval_X, eval_mul, eval_C, eval_pow, hpow, hβ]
    push_cast; ring
  have hnn : (0 : ℝ) ≤ 1 - 1 / (d : ℝ) := by
    rw [sub_nonneg, div_le_one hdpos]; exact_mod_cast (show 1 ≤ d by omega)
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn,
    mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hβ0)]
  field_simp

theorem pEx_critRatios (d : ℕ) (hd : 2 ≤ d) : critRatios (pEx d) = {((d : ℝ) - 1) / d} := by
  ext r
  rw [critRatios, Set.mem_ofPred_eq, Set.mem_singleton_iff, pEx_derivative d hd]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    simp only [eval_sub, eval_one, eval_pow, eval_X, sub_eq_zero] at hβ
    exact pEx_ratio d hd β hβ.symm
  · rintro rfl
    exact ⟨1, by simp, (pEx_ratio d hd 1 (one_pow _)).symm⟩

/-- `sec1_example`, proved. -/
theorem sec1_example_proved (d : ℕ) (hd : 2 ≤ d) :
    IsPd d (X - C (1 / (d : ℂ)) * X ^ d) ∧ mval (X - C (1 / (d : ℂ)) * X ^ d) = ((d : ℝ) - 1) / d ∧
      ((((d : ℝ) - 1) / d : ℝ) : EReal) ≤ Kd d := by
  have hm : mval (pEx d) = ((d : ℝ) - 1) / d := by rw [mval, pEx_critRatios d hd, csInf_singleton]
  refine ⟨pEx_isPd d hd, hm, ?_⟩
  rw [← hm]
  exact le_iSup (fun p : {p : ℂ[X] // IsPd d p} => ((mval p.1 : ℝ) : EReal)) ⟨pEx d, pEx_isPd d hd⟩

/-- `log 452 < 6.11369`, from `log 452 = 9 log 2 + log(1 - 15/128)` and five terms of the series of `log(1 - x)`. -/
theorem log452_lt : Real.log 452 < 6.11369 := by
  have hx : |(15 / 128 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have h := Real.abs_log_sub_add_sum_range_le hx 5
  have hsplit : Real.log 452 = 9 * Real.log 2 + Real.log (1 - 15 / 128) := by
    rw [show (452 : ℝ) = 2 ^ 9 * (1 - 15 / 128) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast; ring
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 15 / 128)] at h
  have hle := (abs_le.mp h).2
  generalize hy : Real.log (1 - 15 / 128) = y at hle hsplit
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  have h2 := Real.log_two_lt_d9
  rw [hsplit]
  linarith

/-- `intro_improves_JN`, proved. -/
theorem intro_improves_JN_proved (d : ℕ) (hd : 452 ≤ d) :
    (4 : ℝ) - 0.00597 / (d * Real.log d) < 4 - 529 * Real.log 2 ^ 2 / (576 * (d : ℝ) ^ 2) := by
  have hd' : (452 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have he : Real.exp 1 ≤ 452 := by linarith [Real.exp_one_lt_d9]
  have hmono : Real.log d / d ≤ Real.log 452 / 452 :=
    Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans hd')) hd'
  have hlogd : 0 < Real.log d := Real.log_pos (by linarith)
  have hlogd_le : Real.log d ≤ Real.log 452 / 452 * d := by
    rw [div_le_iff₀ hdpos] at hmono; exact hmono
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : Real.log 2 ^ 2 < 0.6931471808 ^ 2 := by
    have := Real.log_two_lt_d9
    nlinarith
  have k1 : 529 * Real.log 2 ^ 2 * Real.log d < 529 * 0.6931471808 ^ 2 * Real.log d := by
    have := mul_lt_mul_of_pos_right hsq hlogd
    linarith
  have k2 : Real.log d < 6.11369 / 452 * d := by
    have h452 : Real.log 452 / 452 < 6.11369 / 452 := div_lt_div_of_pos_right log452_lt (by norm_num)
    have := mul_lt_mul_of_pos_right h452 hdpos
    linarith
  have k3 : 529 * 0.6931471808 ^ 2 * Real.log d < 529 * 0.6931471808 ^ 2 * (6.11369 / 452 * d) :=
    mul_lt_mul_of_pos_left k2 (by norm_num)
  have hc : (529 * 0.6931471808 ^ 2 * (6.11369 / 452) : ℝ) < 576 * 0.00597 := by norm_num
  have k4 : 529 * 0.6931471808 ^ 2 * (6.11369 / 452 * (d : ℝ)) < 576 * 0.00597 * (d : ℝ) := by
    have := mul_lt_mul_of_pos_right hc hdpos
    linarith
  have key : 529 * Real.log 2 ^ 2 * Real.log d < 576 * 0.00597 * (d : ℝ) := by linarith
  have h1 : 529 * Real.log 2 ^ 2 / (576 * (d : ℝ) ^ 2) < 0.00597 / (d * Real.log d) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left key hdpos]
  exact sub_lt_sub_left h1 4

end Smale.Exact
