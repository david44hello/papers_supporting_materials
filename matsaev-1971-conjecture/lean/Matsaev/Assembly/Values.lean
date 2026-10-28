/-
Matsaev/Assembly/Values.lean — the worked values after the proof of Lemma 3.4: `t_* = 2 sin(π/12)`, `D_* = 2^(-3/2)` for
`p = 4`, and `t_* = (√5 - 1)/2`, `D_* = 1/2` for `p = 6`. Author: Dave Goel.

`t_*` is the unique zero in `(0, 1)` of `f' = g/(1+t^p)²`, `g(t) = 1 + t^(2p-2) - (p-1)t^(p-2)(1+t²)` (Scalar/N1.lean). The
identities `g(t₀) = 0` and the values of `f(t₀)` are polynomial identities in `t₀` modulo `t₀² = 2 - √3`, `√3² = 3`
(`p = 4`) or `t₀² + t₀ - 1 = 0` (`p = 6`); the multipliers in `linear_combination` were found by polynomial division.
-/
import Matsaev.Scalar.N1

namespace Matsaev.Values

open Real Set

/-- If `t₀ ∈ (0, 1)` and `g_p(t₀) = 0`, then `t₀` is the unique critical point of `f` in `(0, 1)` and `D_* = f(t₀)`. -/
lemma crit_eq {p t₀ : ℝ} (hp : 2 < p) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hg : gN1 p t₀ = 0) :
    (∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun p) s = 0 ↔ s = t₀) ∧ Dstar p = dfun p t₀ := by
  obtain ⟨t, -, hcrit, -, -, -, hD, -, -⟩ := lemma_3_3_proved p hp
  have hd : deriv (dfun p) t₀ = 0 := by
    rw [(hasDerivAt_dfun (p := p) ht₀.1).deriv, hg, zero_div]
  have htt : t₀ = t := (hcrit t₀ ht₀).mp hd
  subst htt
  exact ⟨hcrit, hD⟩

lemma gN1_four (t : ℝ) : gN1 4 t = 1 + t ^ 6 - 3 * t ^ 2 * (1 + t ^ 2) := by
  unfold gN1
  rw [show (2 * 4 - 2 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, show (4 - 2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  ring

lemma dfun_four (t : ℝ) : dfun 4 t = (t - t ^ 3) / (1 + t ^ 4) := by
  unfold dfun
  rw [show (4 - 1 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

lemma gN1_six (t : ℝ) : gN1 6 t = 1 + t ^ 10 - 5 * t ^ 4 * (1 + t ^ 2) := by
  unfold gN1
  rw [show (2 * 6 - 2 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, show (6 - 2 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_natCast]
  ring

lemma dfun_six (t : ℝ) : dfun 6 t = (t - t ^ 5) / (1 + t ^ 6) := by
  unfold dfun
  rw [show (6 - 1 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- `p = 4`: `t_* = 2 sin(π/12)` and `D_* = 2^(-3/2)`. -/
theorem values_four :
    (∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun 4) s = 0 ↔ s = 2 * Real.sin (π / 12)) ∧ Dstar 4 = (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
  set t := 2 * Real.sin (π / 12) with htdef
  set r := √3 with hrdef
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg 3
  have hr1 : 1 < r := by nlinarith
  have hcos : Real.cos (π / 6) = r / 2 := Real.cos_pi_div_six
  have ht2 : t ^ 2 = 2 - r := by
    have h1 : Real.cos (π / 6) = 2 * Real.cos (π / 12) ^ 2 - 1 := by
      rw [← Real.cos_two_mul]; congr 1; ring
    have h2 := Real.sin_sq_add_cos_sq (π / 12)
    rw [htdef]
    linear_combination 4 * h2 + 2 * h1 - 2 * hcos
  have ht0 : 0 < t := by
    have := Real.sin_pos_of_pos_of_lt_pi (by positivity : 0 < π / 12) (by linarith [Real.pi_pos])
    linarith
  have ht1 : t < 1 := by nlinarith
  have hg : gN1 4 t = 0 := by
    rw [gN1_four]
    linear_combination (r ^ 2 - r * t ^ 2 - r + t ^ 4 - t ^ 2 - 5) * ht2 + (3 - r) * hr2
  obtain ⟨hcrit, hD⟩ := crit_eq (by norm_num) ⟨ht0, ht1⟩ hg
  refine ⟨hcrit, ?_⟩
  rw [hD, dfun_four]
  have hden : 0 < 1 + t ^ 4 := by positivity
  have hnum : 0 < t - t ^ 3 := by nlinarith
  have hsq : 8 * (t - t ^ 3) ^ 2 = (1 + t ^ 4) ^ 2 := by
    linear_combination (r ^ 3 - r ^ 2 * t ^ 2 + 2 * r ^ 2 + r * t ^ 4 - 4 * r * t ^ 2 - 2 * r - t ^ 6 + 6 * t ^ 4 -
      6 * t ^ 2 - 4) * ht2 + (3 - r ^ 2) * hr2
  have hval : ((t - t ^ 3) / (1 + t ^ 4)) ^ 2 = 1 / 8 := by
    rw [div_pow, div_eq_iff (by positivity)]
    linarith
  have h8 : ((2 : ℝ) ^ (-(3 / 2 : ℝ))) ^ 2 = 1 / 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show (-(3 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  exact (pow_left_inj₀ (div_pos hnum hden).le (Real.rpow_nonneg (by norm_num) _) two_ne_zero).mp (hval.trans h8.symm)

/-- `p = 6`: `t_* = (√5 - 1)/2` and `D_* = 1/2`. -/
theorem values_six : (∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun 6) s = 0 ↔ s = (√5 - 1) / 2) ∧ Dstar 6 = 1 / 2 := by
  set t := (√5 - 1) / 2 with htdef
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h50 : 0 ≤ √5 := Real.sqrt_nonneg 5
  have ht : t ^ 2 + t - 1 = 0 := by
    rw [htdef]
    linear_combination (1 / 4 : ℝ) * h5
  have ht0 : 0 < t := by rw [htdef]; nlinarith
  have ht1 : t < 1 := by rw [htdef]; nlinarith
  have hg : gN1 6 t = 0 := by
    rw [gN1_six]
    linear_combination (t ^ 8 - t ^ 7 + 2 * t ^ 6 - 3 * t ^ 5 - 3 * t ^ 3 - 2 * t ^ 2 - t - 1) * ht
  obtain ⟨hcrit, hD⟩ := crit_eq (by norm_num) ⟨ht0, ht1⟩ hg
  refine ⟨hcrit, ?_⟩
  rw [hD, dfun_six, div_eq_iff (by positivity)]
  linear_combination ((-t ^ 4 - t ^ 3 - t + 1) / 2) * ht

end Matsaev.Values
