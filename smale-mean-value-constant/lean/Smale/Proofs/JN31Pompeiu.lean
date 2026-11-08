/-
Smale/Proofs/JN31Pompeiu.lean — the Cauchy-Pompeiu formula for a compactly supported `C¹` function `u` on `ℂ`:
`∫ (∂u/∂z̄)(ζ) / (ζ - z) dA(ζ) = -π u(z)`. Polar coordinates about `z`, then the fundamental theorem of calculus along rays
and around circles.
-/
import Mathlib

namespace Smale

open Complex Metric Set Filter Topology MeasureTheory
open scoped Real

/-- The Wirtinger derivative `∂u/∂z̄ = (u_x + i u_y)/2`. -/
noncomputable def dbar (u : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2) * (fderiv ℝ u ζ 1 + I * fderiv ℝ u ζ I)

/-- A real-linear map on `ℂ` through its values at `1` and `i`. -/
lemma clm_apply_re_im (L : ℂ →L[ℝ] ℂ) (w : ℂ) : L w = w.re • L 1 + w.im • L I := by
  have h : w = w.re • (1 : ℂ) + w.im • I := by
    simp [Complex.re_add_im]
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul]

/-- The pointwise identity behind the formula: in polar coordinates, `ρ ∂̄u / (ρ e^{iθ}) = (∂_ρ + (i/ρ) ∂_θ)/2`. -/
lemma polar_identity (L : ℂ →L[ℝ] ℂ) {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    ρ • ((1 / 2) * (L 1 + I * L I) * ((ρ : ℂ) * Complex.exp (θ * I))⁻¹) =
      (1 / 2) * (L (Complex.exp (θ * I)) + I * L (I * Complex.exp (θ * I))) := by
  set c : ℝ := Real.cos θ with hc
  set s : ℝ := Real.sin θ with hs
  have he : Complex.exp (θ * I) = (c : ℂ) + (s : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq θ
    exact_mod_cast this
  have hinv : Complex.exp (θ * I) * ((c : ℂ) - (s : ℂ) * I) = 1 := by
    rw [he]
    linear_combination hcs - (s : ℂ) ^ 2 * Complex.I_sq
  have hinv' : (Complex.exp (θ * I))⁻¹ = (c : ℂ) - (s : ℂ) * I := inv_eq_of_mul_eq_one_right hinv
  have h1 : L (Complex.exp (θ * I)) = c • L 1 + s • L I := by
    rw [clm_apply_re_im L, he]
    simp
  have h2 : L (I * Complex.exp (θ * I)) = (-s) • L 1 + c • L I := by
    rw [clm_apply_re_im L, he]
    simp
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  rw [h1, h2, mul_inv, hinv', Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul,
    Complex.real_smul]
  push_cast
  field_simp
  linear_combination (-(s : ℂ) * L I) * Complex.I_sq

lemma hasDerivAt_ray (e z : ℂ) (ρ : ℝ) : HasDerivAt (fun r : ℝ => (r : ℂ) * e + z) e ρ := by
  have h := ((hasDerivAt_id ρ).ofReal_comp.mul_const e).add_const z
  simpa using h

lemma hasDerivAt_arc (ρ : ℝ) (z : ℂ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (ρ : ℂ) * Complex.exp (t * I) + z) ((ρ : ℂ) * (I * Complex.exp (θ * I))) θ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp.mul_const I
  have h2 := (h1.cexp.const_mul (ρ : ℂ)).add_const z
  convert h2 using 2
  ring

variable {u : ℂ → ℂ}

/-- Along a ray the derivative integrates to `-u(z)`. -/
lemma ray_integral (hu : ContDiff ℝ 1 u) {z : ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ξ, M < ‖ξ - z‖ → u ξ = 0 ∧ fderiv ℝ u ξ = 0) {e : ℂ} (he : ‖e‖ = 1) :
    ∫ ρ in Ioi (0 : ℝ), fderiv ℝ u ((ρ : ℂ) * e + z) e = -u z := by
  have hdiff : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hDcont : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hpath : Continuous fun ρ : ℝ => (ρ : ℂ) * e + z := by fun_prop
  have hfar : ∀ ρ : ℝ, M < ρ → M < ‖((ρ : ℂ) * e + z) - z‖ := fun ρ hρ => by
    have hρ0 : 0 ≤ ρ := hM0.trans hρ.le
    rw [add_sub_cancel_right, norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ0]
    exact hρ
  have hcont' : Continuous fun ρ : ℝ => fderiv ℝ u ((ρ : ℂ) * e + z) e :=
    (hDcont.comp hpath).clm_apply continuous_const
  have hint : IntegrableOn (fun ρ : ℝ => fderiv ℝ u ((ρ : ℂ) * e + z) e) (Ioi 0) := by
    refine (hcont'.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := M))).of_forall_sdiff_eq_zero
      measurableSet_Ioi fun ρ hρ => ?_
    have h1 : M < ρ := by
      by_contra hle
      exact hρ.2 ⟨le_of_lt hρ.1, not_lt.1 hle⟩
    rw [(hM _ (hfar ρ h1)).2]
    rfl
  have hlim : Tendsto (fun ρ : ℝ => u ((ρ : ℂ) * e + z)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop M] with ρ hρ
    exact (hM _ (hfar ρ hρ)).1.symm
  have hfc : Continuous fun ρ : ℝ => u ((ρ : ℂ) * e + z) := hu.continuous.comp hpath
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := (0 : ℝ)) (f := fun ρ : ℝ => u ((ρ : ℂ) * e + z))
    (f' := fun ρ : ℝ => fderiv ℝ u ((ρ : ℂ) * e + z) e) hfc.continuousAt.continuousWithinAt
    (fun ρ _ => (hdiff _).hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_ray e z ρ)) hint hlim
  rw [h]
  simp

/-- Around a circle the angular derivative integrates to `0`. -/
lemma arc_integral (hu : ContDiff ℝ 1 u) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    ∫ θ in Ioo (-π) π, fderiv ℝ u ((ρ : ℂ) * Complex.exp (θ * I) + z) (I * Complex.exp (θ * I)) = 0 := by
  have hdiff : Differentiable ℝ u := hu.differentiable one_ne_zero
  have hDcont : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  set F : ℝ → ℂ := fun θ => fderiv ℝ u ((ρ : ℂ) * Complex.exp (θ * I) + z) (I * Complex.exp (θ * I)) with hFdef
  have hFcont : Continuous F := by
    refine (hDcont.comp ?_).clm_apply ?_ <;> fun_prop
  have hder : ∀ θ : ℝ, HasDerivAt (fun t : ℝ => (ρ : ℂ)⁻¹ * u ((ρ : ℂ) * Complex.exp (t * I) + z)) (F θ) θ := by
    intro θ
    have h1 := ((hdiff _).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_arc ρ z θ)).const_mul (ρ : ℂ)⁻¹
    have h2 : (ρ : ℂ) * (I * Complex.exp (θ * I)) = ρ • (I * Complex.exp (θ * I)) := by
      rw [Complex.real_smul]
    have h3 : (ρ : ℂ)⁻¹ * (fderiv ℝ u ((ρ : ℂ) * Complex.exp (θ * I) + z)) ((ρ : ℂ) * (I * Complex.exp (θ * I))) = F θ := by
      rw [h2, map_smul, Complex.real_smul, hFdef]
      field_simp
    rw [h3] at h1
    exact h1
  have hpi : (-π : ℝ) ≤ π := by linarith [Real.pi_pos]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := -π) (b := π) (fun θ _ => hder θ)
    (hFcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo] at hint
  rw [hint]
  have hexp : Complex.exp ((π : ℝ) * I) = Complex.exp (((-π : ℝ) : ℂ) * I) := by
    push_cast
    rw [Complex.exp_pi_mul_I, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  simp only [hexp, sub_self]

/-- A continuous function on the plane, zero beyond radius `M` in its first coordinate, is integrable on the polar target. -/
lemma integrableOn_target {F : ℝ × ℝ → ℂ} (hF : Continuous F) {M : ℝ} (hM : ∀ p : ℝ × ℝ, M < p.1 → F p = 0) :
    IntegrableOn F (Ioi 0 ×ˢ Ioo (-π) π) := by
  have hY : IsCompact (Icc (0 : ℝ) M ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  refine (hF.continuousOn.integrableOn_compact hY).of_forall_sdiff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  refine hM p ?_
  by_contra hle
  exact hp.2 ⟨⟨le_of_lt hp.1.1, not_lt.1 hle⟩, Ioo_subset_Icc_self hp.1.2⟩

/-- The same, with the coordinates in the other order. -/
lemma integrableOn_target_swap {F : ℝ × ℝ → ℂ} (hF : Continuous F) {M : ℝ} (hM : ∀ p : ℝ × ℝ, M < p.1 → F p = 0) :
    IntegrableOn (fun w : ℝ × ℝ => F w.swap) (Ioo (-π) π ×ˢ Ioi 0) := by
  have hY : IsCompact (Icc (-π) π ×ˢ Icc (0 : ℝ) M) := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous fun w : ℝ × ℝ => F w.swap := hF.comp continuous_swap
  refine (hcont.continuousOn.integrableOn_compact hY).of_forall_sdiff_eq_zero
    (measurableSet_Ioo.prod measurableSet_Ioi) fun w hw => ?_
  refine hM w.swap ?_
  by_contra hle
  exact hw.2 ⟨Ioo_subset_Icc_self hw.1.1, ⟨le_of_lt hw.1.2, not_lt.1 hle⟩⟩

/-- **The Cauchy-Pompeiu formula.** -/
theorem cauchy_pompeiu (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (z : ℂ) :
    ∫ ζ, dbar u ζ * (ζ - z)⁻¹ = -(π : ℂ) * u z := by
  have hDcont : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  -- the radius beyond which everything vanishes
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ, M < ‖ξ - z‖ → u ξ = 0 ∧ fderiv ℝ u ξ = 0 := by
    obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall z
    refine ⟨max r 0, le_max_right _ _, fun ξ hξ => ?_⟩
    have hnot : ξ ∉ tsupport u := fun h => by
      have h1 := hr h
      rw [mem_closedBall, dist_eq_norm] at h1
      have := le_max_left r 0
      linarith
    exact ⟨image_eq_zero_of_notMem_tsupport hnot, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot⟩
  -- the two polar pieces
  set pol : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * Complex.exp (p.2 * I) with hpol
  have hpolc : Continuous pol := by fun_prop
  set A : ℝ × ℝ → ℂ := fun p => fderiv ℝ u (pol p + z) (Complex.exp (p.2 * I)) with hAdef
  set B : ℝ × ℝ → ℂ := fun p => fderiv ℝ u (pol p + z) (I * Complex.exp (p.2 * I)) with hBdef
  have hAc : Continuous A := (hDcont.comp (hpolc.add continuous_const)).clm_apply (by fun_prop)
  have hBc : Continuous B := (hDcont.comp (hpolc.add continuous_const)).clm_apply (by fun_prop)
  have hfar : ∀ p : ℝ × ℝ, M < p.1 → fderiv ℝ u (pol p + z) = 0 := fun p hp => by
    refine (hM _ ?_).2
    rw [add_sub_cancel_right, hpol, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hM0.trans hp.le)]
    exact hp
  have hA0 : ∀ p : ℝ × ℝ, M < p.1 → A p = 0 := fun p hp => by
    simp only [hAdef, hfar p hp]
    rfl
  have hB0 : ∀ p : ℝ × ℝ, M < p.1 → B p = 0 := fun p hp => by
    simp only [hBdef, hfar p hp]
    rfl
  have hAint := integrableOn_target hAc hA0
  have hBint := integrableOn_target hBc hB0
  -- `A` integrates, angle outside, to `-2π u(z)`
  have hAval : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, A p = -(2 * π : ℂ) * u z := by
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap,
      setIntegral_prod _ (integrableOn_target_swap hAc hA0)]
    have hin : ∀ θ : ℝ, ∫ ρ in Ioi (0 : ℝ), A ((θ, ρ) : ℝ × ℝ).swap = -u z := fun θ => by
      have h1 := ray_integral hu hM0 hM (e := Complex.exp (θ * I)) (Complex.norm_exp_ofReal_mul_I θ)
      simpa [hAdef, hpol] using h1
    simp only [hin]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), Complex.real_smul]
    push_cast
    ring
  -- `B` integrates, radius outside, to `0`
  have hBval : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, B p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hBint]
    refine setIntegral_eq_zero_of_forall_eq_zero fun ρ hρ => ?_
    exact arc_integral hu hρ z
  -- put together
  have hshift : ∫ ζ, dbar u ζ * (ζ - z)⁻¹ = ∫ ξ, dbar u (ξ + z) * ξ⁻¹ := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℂ)) (fun ζ => dbar u ζ * (ζ - z)⁻¹) z
    simpa using h.symm
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := polarCoord_target
  have hsym : ∀ p : ℝ × ℝ, Complex.polarCoord.symm p = pol p := fun p => by
    rw [Complex.polarCoord_symm_apply]
    simp only [hpol]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [hshift, ← Complex.integral_comp_polarCoord_symm, htarget]
  have hcongr : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, p.1 • (dbar u (Complex.polarCoord.symm p + z) *
      (Complex.polarCoord.symm p)⁻¹) = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, (1 / 2 : ℂ) * (A p + I * B p) := by
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    have h := polar_identity (fderiv ℝ u (pol p + z)) (ρ := p.1) hp.1 p.2
    simp only [hsym, dbar]
    exact h
  rw [hcongr, integral_const_mul, integral_add hAint (hBint.const_mul I), integral_const_mul, hAval, hBval]
  ring

end Smale
