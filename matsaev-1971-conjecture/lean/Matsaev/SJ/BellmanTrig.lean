-- Matsaev/SJ/BellmanTrig.lean — angle facts for Steps F-I of Theorem 3.6: the coset distance, cos near θs + kπ/2, the λ-determinant.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Angle.Defs
import Matsaev.Angle.Basic
import Matsaev.SJ.BellmanDefs

namespace Matsaev.SJ

open Real

/-- The coset distance is attained: some `k` has `|θ - (θ' + k π/2)| = angDist θ θ'` (floor or ceiling of `(θ-θ')/(π/2)`). -/
theorem exists_int_angDist (θ θ' : ℝ) : ∃ k : ℤ, |θ - (θ' + k * (π / 2))| = Angle.angDist θ θ' := by
  have hπ : 0 < π / 2 := by positivity
  set x := (θ - θ') / (π / 2) with hx
  have hθ : θ - θ' = x * (π / 2) := by rw [hx, div_mul_cancel₀ _ hπ.ne']
  unfold Angle.angDist
  rw [← hx]
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · refine ⟨⌊x⌋, ?_⟩
    rw [min_eq_left h]
    have e : θ - (θ' + (⌊x⌋ : ℝ) * (π / 2)) = π / 2 * Int.fract x := by
      rw [Int.fract]
      linear_combination hθ
    rw [e, abs_of_nonneg (mul_nonneg hπ.le (Int.fract_nonneg x))]
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [min_eq_right h]
    have e : θ - (θ' + ((⌊x⌋ + 1 : ℤ) : ℝ) * (π / 2)) = -(π / 2 * (1 - Int.fract x)) := by
      push_cast
      rw [Int.fract]
      linear_combination hθ
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg hπ.le (by linarith [Int.fract_lt_one x]))]

/-- `|cos(θs + k π/2)| ≥ sin θs` for `θs ∈ (0, π/4)` (it is `cos θs` or `sin θs`; `Real.cos_add_int_mul_pi`). -/
theorem sin_le_abs_cos_add_int_mul (θs : ℝ) (h0 : 0 < θs) (h1 : θs < π / 4) (k : ℤ) :
    Real.sin θs ≤ |Real.cos (θs + k * (π / 2))| := by
  have hsin : 0 < Real.sin θs := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hsc : Real.sin θs ≤ Real.cos θs := by
    rw [← Real.cos_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_pos]) (by linarith)
  have hcos : 0 < Real.cos θs :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · have e : θs + ((2 * m : ℤ) : ℝ) * (π / 2) = θs + (m : ℝ) * π := by push_cast; ring
    rw [e, Real.cos_add_int_mul_pi, abs_mul]
    simp only [abs_neg_one_zpow, one_mul, abs_of_pos hcos]
    exact hsc
  · have e : θs + ((2 * m + 1 : ℤ) : ℝ) * (π / 2) = (θs + π / 2) + (m : ℝ) * π := by push_cast; ring
    rw [e, Real.cos_add_int_mul_pi, Real.cos_add_pi_div_two, abs_mul]
    simp only [abs_neg_one_zpow, one_mul, abs_neg, abs_of_pos hsin, le_refl]

/-- The determinant of the λ-system is bounded away from `0` near `θs ∈ (0, π/4)`: at `θs`,
`detL = cs(s^(q-2) - c^(q-2)) < 0` (`c = cos θs > s = sin θs > 0`, `φ(x) = x^(q-1)` for `x ≥ 0`), and `detL` is continuous
(`Matsaev.Angle.continuous_phi`). -/
theorem detL_bound_near (q θs : ℝ) (hq : 2 < q) (h0 : 0 < θs) (h1 : θs < π / 4) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧ ∀ θ : ℝ, |θ - θs| ≤ ε → d ≤ |detL q (Real.cos θ) (Real.sin θ)| := by
  set g : ℝ → ℝ := fun θ => detL q (Real.cos θ) (Real.sin θ) with hg
  have hφ := Matsaev.Angle.continuous_phi (q := q) (by linarith)
  have hcont : Continuous g := by
    simp only [hg, detL]
    exact (Real.continuous_cos.mul (hφ.comp Real.continuous_sin)).sub
      (Real.continuous_sin.mul (hφ.comp Real.continuous_cos))
  -- the value at θs is negative: c φ(s) - s φ(c) = c s (s^(q-2) - c^(q-2)), 0 < s < c
  have hsin : 0 < Real.sin θs := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos θs :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsc : Real.sin θs < Real.cos θs := by
    rw [← Real.cos_pi_div_two_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le (by linarith [Real.pi_pos]) (by linarith)
  have hval : g θs < 0 := by
    simp only [hg, detL, Matsaev.Angle.phi_eq_mul, abs_of_pos hsin, abs_of_pos hcos]
    have hpow : Real.sin θs ^ (q - 2) < Real.cos θs ^ (q - 2) :=
      Real.rpow_lt_rpow hsin.le hsc (by linarith)
    have hcs : 0 < Real.cos θs * Real.sin θs := mul_pos hcos hsin
    nlinarith
  have hpos : 0 < |g θs| := abs_pos.mpr hval.ne
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont θs (|g θs| / 2) (by positivity)
  refine ⟨δ / 2, |g θs| / 2, by positivity, by positivity, fun θ hθ => ?_⟩
  have hd : dist (g θ) (g θs) < |g θs| / 2 := hball θ (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at hd
  have htri := abs_sub_abs_le_abs_sub (g θs) (g θ)
  rw [abs_sub_comm] at htri
  show |g θs| / 2 ≤ |g θ|
  linarith

/-- Zeros of a `π`-antiperiodic function at `θa` and `θa - π/2` give zeros on the whole coset `θa + (π/2)ℤ`. -/
theorem zero_on_coset (g : ℝ → ℝ) (hg : ∀ θ, g (θ + π) = -g θ) (θa : ℝ) (h0 : g θa = 0) (h1 : g (θa - π / 2) = 0) :
    ∀ k : ℤ, g (θa + k * (π / 2)) = 0 := by
  -- a zero of g stays a zero after any shift by m π, m ∈ ℤ (antiperiodicity in both directions)
  have hback : ∀ θ, g (θ - π) = -g θ := fun θ => by
    have := hg (θ - π)
    rw [sub_add_cancel] at this
    linarith
  have hshift : ∀ θ, g θ = 0 → ∀ m : ℤ, g (θ + m * π) = 0 := by
    intro θ hθ m
    induction m using Int.induction_on with
    | zero => simpa using hθ
    | succ n ih =>
      have e : θ + ((n : ℤ) + 1 : ℤ) * π = (θ + (n : ℤ) * π) + π := by push_cast; ring
      rw [e, hg, ih, neg_zero]
    | pred n ih =>
      have e : θ + (-(n : ℤ) - 1 : ℤ) * π = (θ + (-(n : ℤ) : ℤ) * π) - π := by push_cast; ring
      rw [e, hback, ih, neg_zero]
  intro k
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · have e : θa + ((2 * m : ℤ) : ℝ) * (π / 2) = θa + (m : ℝ) * π := by push_cast; ring
    rw [e]
    exact hshift θa h0 m
  · have e : θa + ((2 * m + 1 : ℤ) : ℝ) * (π / 2) = (θa - π / 2) + ((m + 1 : ℤ) : ℝ) * π := by
      push_cast; ring
    rw [e]
    exact hshift (θa - π / 2) h1 (m + 1)

end Matsaev.SJ
