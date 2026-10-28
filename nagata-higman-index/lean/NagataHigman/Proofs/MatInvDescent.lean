/-
NagataHigman/Proofs/MatInvDescent.lean — Corollary 1.1: generation of a polynomial subalgebra descends along K/F.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib

namespace NagataHigman.Proofs.MatInvDescent

open MvPolynomial

/-- An `F`-linear left inverse `φ : K → F` of `algebraMap F K`. -/
theorem exists_retraction (F K : Type*) [Field F] [Field K] [Algebra F K] :
    ∃ φ : K →ₗ[F] F, ∀ a : F, φ (algebraMap F K a) = a := by
  obtain ⟨φ, hφ⟩ := (Algebra.linearMap F K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F K).injective)
  exact ⟨φ, fun a => LinearMap.congr_fun hφ a⟩

/-- Apply an `F`-linear `φ : K → F` to every coefficient of a `K`-polynomial. -/
noncomputable def coeffMap {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    (φ : K →ₗ[F] F) (q : MvPolynomial σ K) : MvPolynomial σ F :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ (map_zero φ) q.coeff)

theorem coeff_coeffMap {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    (φ : K →ₗ[F] F) (q : MvPolynomial σ K) (m : σ →₀ ℕ) :
    (coeffMap φ q).coeff m = φ (q.coeff m) :=
  Finsupp.mapRange_apply (hf := map_zero φ) ..

theorem coeffMap_add {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    (φ : K →ₗ[F] F) (q r : MvPolynomial σ K) :
    coeffMap φ (q + r) = coeffMap φ q + coeffMap φ r := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_coeffMap, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]

theorem coeffMap_zero {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    (φ : K →ₗ[F] F) : coeffMap φ (0 : MvPolynomial σ K) = 0 := by
  refine MvPolynomial.ext _ _ fun m => ?_
  simp only [coeff_coeffMap, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]

/-- `coeffMap φ (c • map r) = φ c • r`. -/
theorem coeffMap_smul_map {F K σ : Type*} [Field F] [Field K] [Algebra F K]
    (φ : K →ₗ[F] F) (c : K) (r : MvPolynomial σ F) :
    coeffMap φ (c • MvPolynomial.map (algebraMap F K) r) = φ c • r := by
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [coeff_coeffMap, coeff_smul, coeff_map, coeff_smul, smul_eq_mul, smul_eq_mul,
    mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem mem_adjoin_of_map_mem {F K σ : Type*} [Field F] [Field K] [Algebra F K] (S : Set (MvPolynomial σ F))
    (p : MvPolynomial σ F)
    (h : MvPolynomial.map (algebraMap F K) p ∈
      Algebra.adjoin K (MvPolynomial.map (algebraMap F K) '' S)) :
    p ∈ Algebra.adjoin F S := by
  obtain ⟨φ, hφ⟩ := exists_retraction F K
  have hφ1 : φ 1 = 1 := by simpa using hφ 1
  have hcl : ∀ r ∈ Submonoid.closure S, r ∈ Algebra.adjoin F S := fun r hr =>
    (Submonoid.closure_le (S := (Algebra.adjoin F S).toSubsemiring.toSubmonoid)).mpr
      Algebra.subset_adjoin hr
  -- adjoin K (map '' S) = span K (closure (map '' S)), and closure (map '' S) = map '' closure S
  have hspan : MvPolynomial.map (algebraMap F K) p ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (Submonoid.closure S : Set (MvPolynomial σ F))) := by
    have h' : MvPolynomial.map (algebraMap F K) p ∈
        Subalgebra.toSubmodule (Algebra.adjoin K (MvPolynomial.map (algebraMap F K) '' S)) := h
    rw [Algebra.adjoin_eq_span, ← MonoidHom.map_mclosure (MvPolynomial.map (algebraMap F K)) S]
      at h'
    simpa only [Submonoid.coe_map] using h'
  -- every `x` in that span satisfies `coeffMap φ (c • x) ∈ adjoin F S` for all `c : K`
  have key : ∀ x ∈ Submodule.span K
      (MvPolynomial.map (algebraMap F K) '' (Submonoid.closure S : Set (MvPolynomial σ F))),
      ∀ c : K, coeffMap φ (c • x) ∈ Algebra.adjoin F S := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, hr, rfl⟩ := hx
      intro c
      rw [coeffMap_smul_map]
      exact Subalgebra.smul_mem _ (hcl r hr) _
    | zero => intro c; rw [smul_zero, coeffMap_zero]; exact Subalgebra.zero_mem _
    | add x y _ _ hx hy =>
      intro c; rw [smul_add, coeffMap_add]; exact Subalgebra.add_mem _ (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx (c * a)
  have hp := key _ hspan 1
  rwa [coeffMap_smul_map, hφ1, one_smul] at hp

end NagataHigman.Proofs.MatInvDescent
