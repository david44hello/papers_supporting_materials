/-
Smale/Proofs/JNRunge.lean — Runge on `W(closed disk)`: a function `G` holomorphic on the unit disk is, on `|z| ≤ r < 1`,
uniformly near `p ∘ W` for a polynomial `p` (`W` univalent). The Cauchy formula, pulled back through `W`, writes `G ∘ W⁻¹`
as an integral of functions `1/(W ζ - w)`, each of them a uniform limit of polynomials by pole pushing.
-/
import Smale.Proofs.JNUnivalent
import Smale.Proofs.JNPole

namespace Smale

open Polynomial Complex Metric Filter Topology Set MeasureTheory
open scoped Real

/-- The closure of the polynomials in `C(E, ℂ)`. -/
local notation "𝒜[" E "]" => Subalgebra.topologicalClosure (polynomialFunctions E)

/-- The slope of a univalent map never vanishes. -/
theorem univalent_dslope_ne_zero {W : ℂ → ℂ} (hW : IsUnivalentOn W disk) {z ζ : ℂ} (hz : z ∈ disk) (hζ : ζ ∈ disk) :
    dslope W z ζ ≠ 0 := by
  by_cases h : ζ = z
  · rw [h, dslope_same]
    exact univalent_deriv_ne_zero hW hz
  · rw [dslope_of_ne _ h, slope_def_field]
    refine div_ne_zero (sub_ne_zero.2 fun h1 => h (hW.2 hζ hz h1)) (sub_ne_zero.2 h)

/-- **The Cauchy formula pulled back through `W`.** -/
theorem cauchy_pullback {W G : ℂ → ℂ} (hW : IsUnivalentOn W disk) (hG : DifferentiableOn ℂ G disk) {s : ℝ} (hs : s < 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) s) :
    (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, s), G ζ * deriv W ζ * (W ζ - W z)⁻¹ = G z := by
  have hzd : z ∈ disk := ball_subset_ball hs.le hz
  have hs0 : 0 < s := pos_of_mem_ball hz
  set Φ : ℂ → ℂ := fun ζ => G ζ * deriv W ζ / dslope W z ζ with hΦdef
  have hds : DifferentiableOn ℂ (dslope W z) disk :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hzd)).2 hW.1
  have hΦ : DifferentiableOn ℂ Φ disk :=
    (hG.mul (hW.1.deriv isOpen_ball)).div hds fun ζ hζ => univalent_dslope_ne_zero hW hzd hζ
  have hcauchy := (hΦ.diffContOnCl_ball (closedBall_subset_ball hs)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
  have hΦz : Φ z = G z := by
    have h1 : deriv W z ≠ 0 := univalent_deriv_ne_zero hW hzd
    simp only [hΦdef, dslope_same]
    field_simp
  rw [hΦz] at hcauchy
  rw [← hcauchy]
  congr 1
  refine circleIntegral.integral_congr hs0.le fun ζ hζ => ?_
  have hζn : ‖ζ‖ = s := by simpa using hζ
  have hzn : ‖z‖ < s := by simpa using hz
  have hne : ζ ≠ z := fun h => by
    rw [h] at hζn
    linarith
  have hζd : ζ ∈ disk := by simpa [hζn] using hs
  have h1 : ζ - z ≠ 0 := sub_ne_zero.2 hne
  have h2 : W ζ - W z ≠ 0 := sub_ne_zero.2 fun h => hne (hW.2 hζd hzd h)
  simp only [hΦdef, dslope_of_ne _ hne, slope_def_field, smul_eq_mul]
  field_simp

/-- An interval integral of a continuous function with values in a closed subspace stays in that subspace. -/
theorem intervalIntegral_mem_of_isClosed {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : Submodule ℝ X) (hS : IsClosed (S : Set X)) {F : ℝ → X} (hF : Continuous F) (hmem : ∀ θ, F θ ∈ S) (a b : ℝ) :
    ∫ θ in a..b, F θ ∈ S := by
  have : CompleteSpace S := hS.completeSpace_coe
  set F' : ℝ → S := fun θ => ⟨F θ, hmem θ⟩ with hF'def
  have hF' : Continuous F' := hF.subtype_mk _
  have h := S.subtypeL.intervalIntegral_comp_comm (μ := volume) (hF'.intervalIntegrable a b)
  have h2 : ∫ θ in a..b, F θ = S.subtypeL (∫ θ in a..b, F' θ) := by
    rw [← h]
    rfl
  rw [h2]
  exact (∫ θ in a..b, F' θ).2

/-- **Runge on `W(closed disk r)`.** -/
theorem exists_poly_near_comp {W G : ℂ → ℂ} (hW : IsUnivalentOn W disk) (hG : DifferentiableOn ℂ G disk) {r : ℝ}
    (h0 : 0 ≤ r) (hr : r < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ closedBall (0 : ℂ) r, ‖p.eval (W z) - G z‖ < ε := by
  obtain ⟨s, hrs, hs1⟩ := exists_between hr
  have hs0 : 0 < s := lt_of_le_of_lt h0 hrs
  set K : Set ℂ := W '' closedBall (0 : ℂ) r with hKdef
  have hK : IsCompact K := univalent_isCompact_image hW hr
  have hKc : IsPreconnected Kᶜ := compl_image_closedBall_isPreconnected hW h0 hr
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set ζ : ℝ → ℂ := circleMap 0 s with hζdef
  have hζcont : Continuous ζ := continuous_circleMap 0 s
  have hζn : ∀ θ, ‖ζ θ‖ = s := fun θ => by
    rw [hζdef, norm_circleMap_zero, abs_of_pos hs0]
  have hζd : ∀ θ, ζ θ ∈ disk := fun θ => by
    rw [mem_ball_zero_iff, hζn]
    exact hs1
  have hWζ : Continuous fun θ => W (ζ θ) := hW.1.continuousOn.comp_continuous hζcont hζd
  have hW'ζ : Continuous fun θ => deriv W (ζ θ) := (hW.1.deriv isOpen_ball).continuousOn.comp_continuous hζcont hζd
  have hGζ : Continuous fun θ => G (ζ θ) := hG.continuousOn.comp_continuous hζcont hζd
  have hdζ : Continuous fun θ => deriv ζ θ := by
    have : (fun θ => deriv ζ θ) = fun θ => circleMap 0 s θ * I := funext fun θ => deriv_circleMap 0 s θ
    rw [this]
    exact hζcont.mul continuous_const
  have hnotK : ∀ θ, W (ζ θ) ∉ K := by
    rintro θ ⟨z, hz, hzw⟩
    have h1 : z = ζ θ := hW.2 (closedBall_subset_ball hr hz) (hζd θ) hzw
    have h2 : ‖z‖ ≤ r := by simpa using hz
    rw [h1, hζn] at h2
    linarith
  have hne : ∀ (θ : ℝ) (w : K), W (ζ θ) - (w : ℂ) ≠ 0 := fun θ w h =>
    hnotK θ (by rw [sub_eq_zero.1 h]; exact w.2)
  -- the integrand, as a continuous map with values in `C(K, ℂ)`
  set Fc : C(ℝ × K, ℂ) :=
    ⟨fun p => deriv ζ p.1 * (G (ζ p.1) * deriv W (ζ p.1) * (W (ζ p.1) - (p.2 : ℂ))⁻¹), by
      refine (hdζ.comp continuous_fst).mul (((hGζ.comp continuous_fst).mul (hW'ζ.comp continuous_fst)).mul ?_)
      exact ((hWζ.comp continuous_fst).sub (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p => hne p.1 p.2⟩ with hFcdef
  set F : C(ℝ, C(K, ℂ)) := Fc.curry with hFdef
  have hFapply : ∀ θ (w : K), F θ w = deriv ζ θ * (G (ζ θ) * deriv W (ζ θ) * (W (ζ θ) - (w : ℂ))⁻¹) := fun _ _ => rfl
  have hFmem : ∀ θ, F θ ∈ 𝒜[K] := by
    intro θ
    obtain ⟨-, f, hf, hfw⟩ := poleIn_of_compl_preconnected hK hKc (hnotK θ)
    have heq : F θ = (-(deriv ζ θ * (G (ζ θ) * deriv W (ζ θ)))) • f := by
      ext w
      rw [hFapply, ContinuousMap.smul_apply, hfw, smul_eq_mul, ← neg_sub (W (ζ θ)) (w : ℂ), inv_neg]
      ring
    rw [heq]
    exact Subalgebra.smul_mem _ hf _
  -- the integral stays in the closure
  set S : Submodule ℝ C(K, ℂ) := (𝒜[K]).toSubmodule.restrictScalars ℝ with hSdef
  have hSclosed : IsClosed (S : Set C(K, ℂ)) := Subalgebra.isClosed_topologicalClosure _
  have hImem : ∫ θ in (0 : ℝ)..2 * π, F θ ∈ 𝒜[K] :=
    intervalIntegral_mem_of_isClosed S hSclosed F.continuous (fun θ => hFmem θ) _ _
  have hhmem : (2 * π * I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F θ ∈ 𝒜[K] := Subalgebra.smul_mem _ hImem _
  obtain ⟨p, hp⟩ := exists_poly_near_of_mem_closure hhmem hε
  refine ⟨p, fun z hz => ?_⟩
  have hzb : z ∈ ball (0 : ℂ) s := closedBall_subset_ball hrs hz
  have hwK : W z ∈ K := ⟨z, hz, rfl⟩
  have hval : ((2 * π * I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F θ) ⟨W z, hwK⟩ = G z := by
    rw [ContinuousMap.smul_apply]
    have hint := (ContinuousMap.evalCLM ℝ (⟨W z, hwK⟩ : K)).intervalIntegral_comp_comm (μ := volume)
      (F.continuous.intervalIntegrable 0 (2 * π))
    have hev : (∫ θ in (0 : ℝ)..2 * π, F θ) ⟨W z, hwK⟩ = ∫ θ in (0 : ℝ)..2 * π, F θ ⟨W z, hwK⟩ := hint.symm
    rw [hev, ← cauchy_pullback hW hG hs1 hzb]
    rfl
  have h1 := hp ⟨W z, hwK⟩
  rwa [hval] at h1

end Smale
