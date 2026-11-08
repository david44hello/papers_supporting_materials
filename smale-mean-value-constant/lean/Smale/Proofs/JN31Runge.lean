/-
Smale/Proofs/JN31Runge.lean — Runge's theorem, polynomial form: a function holomorphic near a compact set with connected
complement is a uniform limit of polynomials there. The Cauchy-Pompeiu formula, applied to the function cut off by a bump,
writes it as an integral of functions `1/(ζ - z)`, each of them a uniform limit of polynomials by pole pushing.
-/
import Smale.Proofs.JNPole
import Smale.Proofs.JN31Pompeiu

namespace Smale

open Polynomial Complex Metric Filter Topology Set MeasureTheory
open scoped Real Manifold ContDiff

/-- The closure of the polynomials in `C(E, ℂ)`. -/
local notation "𝒜[" E "]" => Subalgebra.topologicalClosure (polynomialFunctions E)

/-- A smooth bump: `1` near a compact set, supported in a compact part of an open set around it. -/
theorem exists_bump {E U : Set ℂ} (hE : IsCompact E) (hU : IsOpen U) (hEU : E ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 1 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ᶠ z in 𝓝ˢ E, χ z = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hE.exists_cthickening_subset_open hU hEU
  have hint : E ⊆ interior (cthickening (δ / 2) E) := fun z hz => by
    refine interior_maximal (thickening_subset_cthickening (δ / 2) E) isOpen_thickening ?_
    exact self_subset_thickening (by positivity) E hz
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, ℂ)) (n := 1) hE.isClosed hint
  have hsupp : Function.support f ⊆ cthickening (δ / 2) E := fun z hz => by
    by_contra hnot
    exact hz (hf0 z hnot)
  have hts : tsupport f ⊆ cthickening (δ / 2) E := closure_minimal hsupp isClosed_cthickening
  refine ⟨f, f.contMDiff.contDiff, ?_, ?_, hf1⟩
  · exact HasCompactSupport.of_support_subset_isCompact hE.cthickening hsupp
  · exact hts.trans ((cthickening_mono (by linarith) E).trans hδU)

/-- The Wirtinger derivative of a holomorphic function vanishes. -/
theorem dbar_eq_zero_of_differentiableAt {g : ℂ → ℂ} {z : ℂ} (h : DifferentiableAt ℂ g z) : dbar g z = 0 := by
  have h1 : fderiv ℝ g z = (fderiv ℂ g z).restrictScalars ℝ := (h.hasFDerivAt.restrictScalars ℝ).fderiv
  have h2 : fderiv ℂ g z I = I * fderiv ℂ g z 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [dbar, h1]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [h2]
  linear_combination (1 / 2 * fderiv ℂ g z 1) * Complex.I_sq

/-- An integral of a continuous function of compact support with values in a closed subspace stays in that subspace. -/
theorem integral_mem_of_isClosed {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (S : Submodule ℝ X) (hS : IsClosed (S : Set X)) {F : ℂ → X} (hF : Continuous F) (hc : HasCompactSupport F)
    (hmem : ∀ ζ, F ζ ∈ S) : ∫ ζ, F ζ ∈ S := by
  have : CompleteSpace S := hS.completeSpace_coe
  set F' : ℂ → S := fun ζ => ⟨F ζ, hmem ζ⟩ with hF'def
  have hF' : Continuous F' := hF.subtype_mk _
  have hc' : HasCompactSupport F' :=
    HasCompactSupport.of_support_subset_isCompact hc.isCompact fun ζ hζ =>
      subset_tsupport F fun h => hζ (Subtype.ext h)
  have h := S.subtypeL.integral_comp_comm (hF'.integrable_of_hasCompactSupport (μ := volume) hc')
  have h2 : ∫ ζ, F ζ = S.subtypeL (∫ ζ, F' ζ) := by
    rw [← h]
    rfl
  rw [h2]
  exact (∫ ζ, F' ζ).2

/-- **Runge's theorem, polynomial form.** -/
theorem runge_poly {E U : Set ℂ} (hE : IsCompact E) (hc : IsPreconnected Eᶜ) (hU : IsOpen U) (hEU : E ⊆ U) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G U) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ[X], ∀ z ∈ E, ‖P.eval z - G z‖ < ε := by
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := exists_bump hE hU hEU
  set u : ℂ → ℂ := fun z => (χ z : ℂ) * G z with hudef
  -- `u` is `C¹`
  have hu : ContDiff ℝ 1 u := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · have hGc : ContDiffAt ℝ 1 G z :=
        ((hG.analyticAt (hU.mem_nhds hz)).contDiffAt (n := 1)).restrict_scalars ℝ
      have hχC : ContDiffAt ℝ 1 (fun w => (χ w : ℂ)) z := (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt
      exact hχC.mul hGc
    · have hz' : z ∉ tsupport χ := fun h => hz (hχU h)
      have hzero : u =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hz'] with w hw
        simp [hudef, image_eq_zero_of_notMem_tsupport hw]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have huc : HasCompactSupport u :=
    HasCompactSupport.of_support_subset_isCompact hχc.isCompact fun z hz =>
      subset_tsupport χ fun h => hz (by simp [hudef, h])
  -- near `E`, `u = G`, so `∂̄u = 0`
  obtain ⟨N₀, hN₀o, hEN₀, hN₀1⟩ := mem_nhdsSet_iff_exists.1 hχ1
  set N : Set ℂ := N₀ ∩ U with hNdef
  have hNo : IsOpen N := hN₀o.inter hU
  have hEN : E ⊆ N := subset_inter hEN₀ hEU
  have hd0 : ∀ z ∈ N, dbar u z = 0 := by
    intro z hz
    have heq : u =ᶠ[𝓝 z] G := by
      filter_upwards [hN₀o.mem_nhds hz.1] with w hw
      have h1 : χ w = 1 := hN₀1 hw
      simp [hudef, h1]
    have h1 : dbar u z = dbar G z := by
      rw [dbar, dbar, heq.fderiv_eq]
    rw [h1]
    exact dbar_eq_zero_of_differentiableAt (hG.differentiableAt (hU.mem_nhds hz.2))
  -- the integrand
  set d : ℂ → ℂ := dbar u with hddef
  have hDc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hdc : Continuous d := by
    have h1 : Continuous fun ζ => fderiv ℝ u ζ (1 : ℂ) := hDc.clm_apply continuous_const
    have h2 : Continuous fun ζ => fderiv ℝ u ζ I := hDc.clm_apply continuous_const
    exact continuous_const.mul (h1.add (continuous_const.mul h2))
  have hdcs : HasCompactSupport d :=
    HasCompactSupport.of_support_subset_isCompact huc.isCompact fun ζ hζ => by
      by_contra hnot
      apply hζ
      show dbar u ζ = 0
      rw [dbar, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
      simp
  have : CompactSpace E := isCompact_iff_compactSpace.1 hE
  set Fc : C(ℂ × E, ℂ) :=
    ⟨fun p => d p.1 * (p.1 - (p.2 : ℂ))⁻¹, by
      refine continuous_iff_continuousAt.2 fun p => ?_
      by_cases hp : p.1 ∈ E
      · have hzero : (fun p : ℂ × E => d p.1 * (p.1 - (p.2 : ℂ))⁻¹) =ᶠ[𝓝 p] fun _ => 0 := by
          filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (hNo.mem_nhds (hEN hp))] with w hw
          rw [show d w.1 = 0 from hd0 _ hw, zero_mul]
        exact continuousAt_const.congr hzero.symm
      · refine (hdc.comp continuous_fst).continuousAt.mul (ContinuousAt.inv₀ ?_ ?_)
        · exact (continuous_fst.sub (continuous_subtype_val.comp continuous_snd)).continuousAt
        · exact sub_ne_zero.2 fun h => hp (h ▸ p.2.2)⟩ with hFcdef
  set F : C(ℂ, C(E, ℂ)) := Fc.curry with hFdef
  have hFapply : ∀ ζ (w : E), F ζ w = d ζ * (ζ - (w : ℂ))⁻¹ := fun _ _ => rfl
  have hFmem : ∀ ζ, F ζ ∈ 𝒜[E] := by
    intro ζ
    by_cases hζ : ζ ∈ E
    · have hzero : F ζ = 0 := by
        ext w
        rw [hFapply, show d ζ = 0 from hd0 _ (hEN hζ), zero_mul]
        rfl
      rw [hzero]
      exact Subalgebra.zero_mem _
    · obtain ⟨-, f, hf, hfw⟩ := poleIn_of_compl_preconnected hE hc hζ
      have heq : F ζ = (-d ζ) • f := by
        ext w
        rw [hFapply, ContinuousMap.smul_apply, hfw, smul_eq_mul, ← neg_sub (w : ℂ) ζ, inv_neg]
        ring
      rw [heq]
      exact Subalgebra.smul_mem _ hf _
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact hdcs.isCompact fun ζ hζ =>
      subset_tsupport d fun h => hζ (by
        ext w
        rw [hFapply, h, zero_mul]
        rfl)
  -- the integral stays in the closure
  set S : Submodule ℝ C(E, ℂ) := (𝒜[E]).toSubmodule.restrictScalars ℝ with hSdef
  have hSclosed : IsClosed (S : Set C(E, ℂ)) := Subalgebra.isClosed_topologicalClosure _
  have hImem : ∫ ζ, F ζ ∈ 𝒜[E] := integral_mem_of_isClosed S hSclosed F.continuous hFcs fun ζ => hFmem ζ
  have hhmem : (-(π : ℂ)⁻¹) • ∫ ζ, F ζ ∈ 𝒜[E] := Subalgebra.smul_mem _ hImem _
  obtain ⟨P, hP⟩ := exists_poly_near_of_mem_closure hhmem hε
  refine ⟨P, fun z hz => ?_⟩
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hval : ((-(π : ℂ)⁻¹) • ∫ ζ, F ζ) ⟨z, hz⟩ = G z := by
    rw [ContinuousMap.smul_apply]
    have hint := (ContinuousMap.evalCLM ℝ (⟨z, hz⟩ : E)).integral_comp_comm
      (F.continuous.integrable_of_hasCompactSupport (μ := volume) hFcs)
    have hev : (∫ ζ, F ζ) ⟨z, hz⟩ = ∫ ζ, F ζ ⟨z, hz⟩ := hint.symm
    have hCP := cauchy_pompeiu hu huc z
    have hzu : u z = G z := by
      have h1 : χ z = 1 := hN₀1 (hEN₀ hz)
      simp [hudef, h1]
    have hsame : ∫ ζ, F ζ ⟨z, hz⟩ = ∫ ζ, dbar u ζ * (ζ - z)⁻¹ := rfl
    rw [hev, hsame, hCP, hzu, smul_eq_mul]
    field_simp
  have h1 := hP ⟨z, hz⟩
  rwa [hval] at h1

end Smale
