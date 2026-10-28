/-
Smale/Proofs/TextClaims.lean — in-text claims of paper 009 (posted v1.80): a zero of P_c in 0 < |z| < 1 makes H
non-univalent (tex l.235-236); the critical points of z - z^d/d and the value of p(β)/β there (tex l.66-67); the
paper's arithmetic on the constants of [JN] (tex l.33, l.48-49, l.84, l.122-123).
-/
import Smale.Proofs.Dieudonne
import Smale.Proofs.Sec1Exact

namespace Smale

open Polynomial Complex Metric Filter Topology

/-- The two points `z e^{±iθ}`, `0 < θ < π`, `z ≠ 0`, are distinct. -/
theorem exp_pm_ne (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (z : ℂ) (hz0 : z ≠ 0) :
    z * exp (θ * I) ≠ z * exp (-(θ * I)) := by
  intro h
  have h1 := exp_sub_exp_neg 1 θ
  simp only [Nat.cast_one, one_mul, one_mul] at h1
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  have h2 : z * (exp (θ * I) - exp (-(θ * I))) = 0 := by rw [mul_sub, h, sub_self]
  rw [h1, ← ofReal_sin] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hz0 h3
  · rcases mul_eq_zero.1 h3 with h4 | h4
    · exact mul_ne_zero two_ne_zero I_ne_zero h4
    · exact hsin (ofReal_eq_zero.1 h4)

/-- `‖z e^{±iθ}‖ = ‖z‖`. -/
theorem norm_mul_exp_pm (θ : ℝ) (z : ℂ) :
    ‖z * exp (θ * I)‖ = ‖z‖ ∧ ‖z * exp (-(θ * I))‖ = ‖z‖ := by
  refine ⟨by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one], ?_⟩
  rw [norm_mul, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I, mul_one]

/-- tex l.235-236: "So if `-1 < c < 1` and `P_c(z) = 0` with `0 < |z| < 1`, then `H` takes the same value at the two
distinct points `ze^{±iθ}` of `𝔻`, and `H` is not univalent in `𝔻`" (`c = cos θ`, `θ = arccos c ∈ (0, π)`). -/
theorem sec4_P_zero_not_univalent_proved (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (c : ℝ) (hc1 : -1 < c) (hc2 : c < 1)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) (h0 : (dieudonne H n c).eval z = 0) :
    Real.cos (Real.arccos c) = c ∧ 0 < Real.arccos c ∧ Real.arccos c < Real.pi ∧
      z * exp (Real.arccos c * I) ≠ z * exp (-(Real.arccos c * I)) ∧
      z * exp (Real.arccos c * I) ∈ disk ∧ z * exp (-(Real.arccos c * I)) ∈ disk ∧
      H.eval (z * exp (Real.arccos c * I)) = H.eval (z * exp (-(Real.arccos c * I))) ∧
      ¬ IsUnivalentOn (fun w => H.eval w) disk := by
  set θ := Real.arccos c with hθ
  have hcos : Real.cos θ = c := Real.cos_arccos hc1.le hc2.le
  have hθ0 : 0 < θ := Real.arccos_pos.2 hc2
  have hθπ : θ < Real.pi := Real.arccos_lt_pi.2 hc1
  have hne := exp_pm_ne θ hθ0 hθπ z hz0
  obtain ⟨hn1, hn2⟩ := norm_mul_exp_pm θ z
  have hin1 : z * exp (θ * I) ∈ disk := mem_ball_zero_iff.2 (hn1 ▸ hz1)
  have hin2 : z * exp (-(θ * I)) ∈ disk := mem_ball_zero_iff.2 (hn2 ▸ hz1)
  have heq : H.eval (z * exp (θ * I)) = H.eval (z * exp (-(θ * I))) := by
    have h := sec4_dieudonne_identity_proved H n hn θ z
    rw [hcos, h0, mul_zero] at h
    exact sub_eq_zero.1 h
  exact ⟨hcos, hθ0, hθπ, hne, hin1, hin2, heq, fun hu => hne (hu.2 hin1 hin2 heq)⟩

/-- tex l.66-67: the critical points `β` of `p = z - z^d/d` are the `(d-1)`-st roots of unity, and
`p(β)/β = 1 - β^{d-1}/d = (d-1)/d` at each. -/
theorem sec1_example_crit_proved (d : ℕ) (hd : 2 ≤ d) (β : ℂ) :
    ((X - C (1 / (d : ℂ)) * X ^ d).derivative.eval β = 0 ↔ β ^ (d - 1) = 1) ∧
      (β ^ (d - 1) = 1 → (X - C (1 / (d : ℂ)) * X ^ d).eval β / β = 1 - β ^ (d - 1) / d ∧
        1 - β ^ (d - 1) / (d : ℂ) = ((d : ℂ) - 1) / d) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  refine ⟨?_, fun hβ => ?_⟩
  · rw [show X - C (1 / (d : ℂ)) * X ^ d = Exact.pEx d from rfl, Exact.pEx_derivative d hd]
    simp only [eval_sub, eval_one, eval_pow, eval_X]
    rw [sub_eq_zero, eq_comm]
  · have hβ0 : β ≠ 0 := by
      rintro rfl
      rw [zero_pow (show d - 1 ≠ 0 by omega)] at hβ
      exact zero_ne_one hβ
    have hpow : β ^ d = β * β ^ (d - 1) := by rw [← pow_succ']; congr 1; omega
    refine ⟨?_, by rw [hβ]; field_simp⟩
    simp only [eval_sub, eval_X, eval_mul, eval_C, eval_pow, hpow]
    field_simp

/-- tex l.33, l.48-49, l.84: `√(8081/6656) = 1.1018586…` (truncated decimals), so the bound of [JN] exceeds `1.1018`,
and `1.1559837 > 1.1018586…` ("improving the bound 1.1018"). -/
theorem intro_JN_digits_proved :
    (1.1018586 : ℝ) ≤ Real.sqrt (8081 / 6656) ∧ Real.sqrt (8081 / 6656) < 1.1018587 ∧
      (1.1018 : ℝ) < Real.sqrt (8081 / 6656) ∧ Real.sqrt (8081 / 6656) < 1.1559837 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- tex l.122-123, the paper's reading of [JN, Thm. 1.3]: `√(8081/6656) ≤ 𝓑₁ < √(7/5)` gives `1.1018 < 𝓑₁ < 1.1833`
(the numbers), and `𝓑_d < 4 - 529(log 2)²/(576d²)` at `d = 2` "gives `𝓑₂ < 3.89`". -/
theorem intro_JN_B1_B2_proved :
    (1.1018 : ℝ) < Real.sqrt (8081 / 6656) ∧ Real.sqrt (7 / 5) < 1.1833 ∧
      (4 : ℝ) - 529 * Real.log 2 ^ 2 / (576 * 2 ^ 2) < 3.89 := by
  refine ⟨intro_JN_digits_proved.2.2.1, by rw [Real.sqrt_lt' (by norm_num)]; norm_num, ?_⟩
  have h := Real.log_two_gt_d9
  have h2 : (0.69 : ℝ) ^ 2 < Real.log 2 ^ 2 := by
    apply pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
  nlinarith

/-- tex l.75-76: "All these bounds tend to `4` as `d → ∞`": `4^{(d-2)/(d-1)}`, `4(d-1)/(d+1)` and `4 - 2.263/√d`. -/
theorem intro_bounds_tend_to_4_proved :
    Tendsto (fun d : ℕ => (4 : ℝ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1))) atTop (𝓝 4) ∧
      Tendsto (fun d : ℕ => 4 * ((d : ℝ) - 1) / ((d : ℝ) + 1)) atTop (𝓝 4) ∧
      Tendsto (fun d : ℕ => 4 - 2.263 / Real.sqrt d) atTop (𝓝 4) := by
  have hN : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨?_, ?_, ?_⟩
  · have h1 : Tendsto (fun d : ℕ => (d : ℝ) - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) hN
    have h2 : Tendsto (fun d : ℕ => (1 : ℝ) / ((d : ℝ) - 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop h1
    have h3 : Tendsto (fun d : ℕ => ((d : ℝ) - 2) / ((d : ℝ) - 1)) atTop (𝓝 1) := by
      have h4 := (tendsto_const_nhds (x := (1 : ℝ))).sub h2
      rw [sub_zero] at h4
      refine h4.congr' (eventually_atTop.2 ⟨2, fun d hd => ?_⟩)
      have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
      have hne : (d : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    have h5 := ((Real.continuousAt_const_rpow (by norm_num : (4 : ℝ) ≠ 0)).tendsto).comp h3
    rwa [Real.rpow_one] at h5
  · have h1 : Tendsto (fun d : ℕ => (d : ℝ) + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 hN
    have h2 : Tendsto (fun d : ℕ => (8 : ℝ) / ((d : ℝ) + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop h1
    have h3 := (tendsto_const_nhds (x := (4 : ℝ))).sub h2
    rw [sub_zero] at h3
    refine h3.congr' (Eventually.of_forall fun d => ?_)
    have hne : (d : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · have h1 : Tendsto (fun d : ℕ => Real.sqrt d) atTop atTop := Real.tendsto_sqrt_atTop.comp hN
    have h2 : Tendsto (fun d : ℕ => (2.263 : ℝ) / Real.sqrt d) atTop (𝓝 0) := tendsto_const_nhds.div_atTop h1
    have h3 := (tendsto_const_nhds (x := (4 : ℝ))).sub h2
    rwa [sub_zero] at h3

end Smale
