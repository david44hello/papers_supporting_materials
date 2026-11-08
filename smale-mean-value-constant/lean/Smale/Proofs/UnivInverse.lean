/-
Smale/Proofs/UnivInverse.lean — injective holomorphic maps on an open set: no critical point, open image, holomorphic inverse.
-/
import Smale.Proofs.JNUnivalent

namespace Smale

open Complex Metric Set Filter Topology

/-- An injective holomorphic map on an open set has no critical point: rescale a small ball to the unit disk. -/
theorem injOn_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : IsUnivalentOn f U) {z : ℂ} (hz : z ∈ U) :
    deriv f z ≠ 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU z hz
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hmem : ∀ w ∈ disk, z + (δ : ℂ) * w ∈ U := by
    intro w hw
    apply hball
    have hw1 : ‖w‖ < 1 := by simpa using hw
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    nlinarith
  have haff : Differentiable ℂ fun w : ℂ => z + (δ : ℂ) * w := by fun_prop
  have hW : IsUnivalentOn (fun w => f (z + (δ : ℂ) * w)) disk := by
    refine ⟨hf.1.comp haff.differentiableOn hmem, fun w₁ h₁ w₂ h₂ h => ?_⟩
    have h3 := hf.2 (hmem w₁ h₁) (hmem w₂ h₂) h
    exact mul_left_cancel₀ hδc (add_left_cancel h3)
  have h0mem : (0 : ℂ) ∈ disk := mem_ball_self one_pos
  have hne := univalent_deriv_ne_zero hW h0mem
  have hfz : HasDerivAt f (deriv f z) (z + (δ : ℂ) * 0) := by
    rw [mul_zero, add_zero]
    exact (hf.1.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have haffd : HasDerivAt (fun w : ℂ => z + (δ : ℂ) * w) (δ : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (δ : ℂ)).const_add z
  have hcomp := hfz.comp (0 : ℂ) haffd
  intro hzero
  apply hne
  have : deriv (fun w => f (z + (δ : ℂ) * w)) 0 = deriv f z * (δ : ℂ) := hcomp.deriv
  rw [this, hzero, zero_mul]

/-- An injective holomorphic map on an open set has an open image and a holomorphic inverse. -/
theorem univalent_inverse {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : IsUnivalentOn f U) :
    IsOpen (f '' U) ∧ IsUnivalentOn (Function.invFunOn f U) (f '' U) ∧
      Function.invFunOn f U '' (f '' U) = U ∧ (∀ z ∈ U, Function.invFunOn f U (f z) = z) ∧
      (∀ w ∈ f '' U, f (Function.invFunOn f U w) = w) ∧
      ∀ z ∈ U, HasDerivAt (Function.invFunOn f U) (deriv f z)⁻¹ (f z) := by
  set g : ℂ → ℂ := Function.invFunOn f U with hgdef
  have hgf : ∀ z ∈ U, g (f z) = z := fun z hz => hf.2.leftInvOn_invFunOn hz
  have hfg : ∀ w ∈ f '' U, f (g w) = w := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hgf z hz]
  have hstrict : ∀ z ∈ U, HasStrictDerivAt f (deriv f z) z := fun z hz =>
    (hf.1.analyticOnNhd hU z hz).hasStrictDerivAt
  have hmap : ∀ z ∈ U, map f (𝓝 z) = 𝓝 (f z) := fun z hz =>
    (hstrict z hz).map_nhds_eq (injOn_deriv_ne_zero hU hf hz)
  have hnhds : ∀ {z : ℂ}, z ∈ U → ∀ {s : Set ℂ}, s ∈ 𝓝 z → f '' s ∈ 𝓝 (f z) := fun hz _ hs => by
    rw [← hmap _ hz]
    exact image_mem_map hs
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨z, hz, rfl⟩
    exact hnhds hz (hU.mem_nhds hz)
  have hcont : ∀ z ∈ U, ContinuousAt g (f z) := by
    intro z hz
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hnhds hz (inter_mem (hU.mem_nhds hz) (ball_mem_nhds z hε))]
    rintro _ ⟨x, ⟨hxU, hxb⟩, rfl⟩
    rw [hgf x hxU, hgf z hz]
    exact hxb
  have hder : ∀ z ∈ U, HasDerivAt g (deriv f z)⁻¹ (f z) := by
    intro z hz
    have h1 : HasDerivAt f (deriv f z) (g (f z)) := by
      rw [hgf z hz]
      exact (hstrict z hz).hasDerivAt
    refine h1.of_local_left_inverse (hcont z hz) (injOn_deriv_ne_zero hU hf hz) ?_
    filter_upwards [hopen.mem_nhds ⟨z, hz, rfl⟩] with y hy using hfg y hy
  refine ⟨hopen, ⟨?_, ?_⟩, ?_, hgf, hfg, hder⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hder z hz).differentiableAt.differentiableWithinAt
  · intro w₁ h₁ w₂ h₂ h
    rw [← hfg w₁ h₁, ← hfg w₂ h₂, h]
  · ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hgf x hx]
    · intro hz
      exact ⟨f z, ⟨z, hz, rfl⟩, hgf z hz⟩

end Smale
