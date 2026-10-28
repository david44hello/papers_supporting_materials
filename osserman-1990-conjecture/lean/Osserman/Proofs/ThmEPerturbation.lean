/-
ThmEPerturbation.lean — spectral changes along an orthonormal eigenframe, paper 013, lines 762–778.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmEProjection
import Osserman.Proofs.ThmESpectral

namespace Osserman.Proofs.ThmEPerturbation

open Osserman Matrix Osserman.Proofs.Spectral Osserman.Proofs.ThmEProjection
open Osserman.Proofs.ThmESpectral

noncomputable def shiftSpan {t : ℕ} (v : Fin t → Vec 16) (s : Fin t → ℝ) (τ μ : ℝ) :
    Submodule ℝ (Vec 16) :=
  Submodule.span ℝ (Set.range fun a : {a : Fin t // τ - s a = μ} => v a.1)

lemma shiftSpan_le {t : ℕ} (v : Fin t → Vec 16) (s : Fin t → ℝ) (τ μ : ℝ) :
    shiftSpan v s τ μ ≤ frameSpan v := by
  rw [shiftSpan, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span (Set.mem_range_self a.1)

section Perturbation

variable {t : ℕ} (R R' : CurvTensor 16) (x : Vec 16) (v : Fin t → Vec 16) (s : Fin t → ℝ) (τ : ℝ)
variable (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0)
variable (hperp : ∀ a, x ⬝ᵥ v a = 0) (heigen : ∀ a, R.op (v a) x x = τ • v a)
variable (hchange : R'.jacobi x = R.jacobi x - ∑ a, s a • vecMulVec (v a) (v a))

include hv hperp heigen hchange

lemma shiftSpan_le_new (μ : ℝ) : shiftSpan v s τ μ ≤ Esp R' x μ := by
  rw [shiftSpan, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  apply mem_Esp.mpr
  exact ⟨by rw [updated_frame R R' x v s τ hv heigen hchange, a.2], hperp a.1⟩

lemma old_rest_le_new (μ : ℝ) : Esp R x μ ⊓ orthSub (frameSpan v) ≤ Esp R' x μ := by
  intro y hy
  apply mem_Esp.mpr
  refine ⟨?_, (mem_Esp.mp hy.1).2⟩
  rw [updated_action R R' x v s hchange, (mem_Esp.mp hy.1).1]
  simp only [(mem_orth_frame v y).mp hy.2, zero_smul, smul_zero, Finset.sum_const_zero, sub_zero]

lemma coefficients_outside (μ : ℝ) (y : Vec 16) (hy : y ∈ Esp R' x μ) :
    ∀ a : Fin t, τ - s a ≠ μ → v a ⬝ᵥ y = 0 := by
  intro a different
  have member : v a ∈ Esp R' x (τ - s a) :=
    mem_Esp.mpr ⟨updated_frame R R' x v s τ hv heigen hchange a, hperp a⟩
  exact eig_dot_zero R' x _ _ different (v a) y member hy

lemma new_projection_mem (μ : ℝ) (y : Vec 16) (hy : y ∈ Esp R' x μ) :
    frameProj v *ᵥ y ∈ shiftSpan v s τ μ := by
  classical
  rw [projection_action]
  apply Submodule.sum_mem
  intro a _
  by_cases equal : τ - s a = μ
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self (⟨a, equal⟩ : {a : Fin t // τ - s a = μ})))
  · rw [coefficients_outside R R' x v s τ hv hperp heigen hchange μ y hy a equal, zero_smul]
    exact Submodule.zero_mem _

lemma weighted_projection (μ : ℝ) (y : Vec 16) (hy : y ∈ Esp R' x μ) :
    (∑ a, s a • ((v a ⬝ᵥ y) • v a)) = (τ - μ) • (frameProj v *ᵥ y) := by
  classical
  rw [projection_action, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases equal : τ - s a = μ
  · have scalar : s a = τ - μ := by linarith
    rw [scalar]
  · rw [coefficients_outside R R' x v s τ hv hperp heigen hchange μ y hy a equal, zero_smul, smul_zero, smul_zero]

lemma projection_eigen (y : Vec 16) : R.op (frameProj v *ᵥ y) x x = τ • (frameProj v *ᵥ y) := by
  rw [projection_action]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, heigen, Finset.smul_sum,
    smul_smul, mul_comm]

lemma new_rest_mem (μ : ℝ) (y : Vec 16) (hy : y ∈ Esp R' x μ) :
    y - frameProj v *ᵥ y ∈ Esp R x μ ⊓ orthSub (frameSpan v) := by
  have change := updated_action R R' x v s hchange y
  rw [(mem_Esp.mp hy).1, weighted_projection R R' x v s τ hv hperp heigen hchange μ y hy] at change
  have original : R.op y x x = μ • y + (τ - μ) • (frameProj v *ᵥ y) := by
    calc
      _ = (R.op y x x - (τ - μ) • (frameProj v *ᵥ y)) + (τ - μ) • (frameProj v *ᵥ y) := by module
      _ = _ := by rw [← change]
  refine ⟨mem_Esp.mpr ⟨?_, ?_⟩, projection_complement v hv y⟩
  · rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, original, projection_eigen R R' x v s τ hv hperp heigen hchange]
    module
  · exact (perp x).sub_mem (mem_Esp.mp hy).2 ((span_le_perp v x hperp) (projection_mem v y))

lemma updated_eigenspace (μ : ℝ) :
    Esp R' x μ = (Esp R x μ ⊓ orthSub (frameSpan v)) ⊔ shiftSpan v s τ μ := by
  apply le_antisymm
  · intro y hy
    apply Submodule.mem_sup.mpr
    exact ⟨y - frameProj v *ᵥ y, new_rest_mem R R' x v s τ hv hperp heigen hchange μ y hy,
      frameProj v *ᵥ y, new_projection_mem R R' x v s τ hv hperp heigen hchange μ y hy, by abel⟩
  · exact sup_le (old_rest_le_new R R' x v s τ hv hperp heigen hchange μ)
      (shiftSpan_le_new R R' x v s τ hv hperp heigen hchange μ)

lemma rest_shift_inf (μ : ℝ) :
    (Esp R x μ ⊓ orthSub (frameSpan v)) ⊓ shiftSpan v s τ μ = ⊥ := by
  apply eq_bot_iff.mpr
  intro y hy
  have zero := hy.1.2 y (shiftSpan_le v s τ μ hy.2)
  exact dotProduct_self_eq_zero.mp zero

lemma shiftSpan_finrank (μ : ℝ) :
    Module.finrank ℝ ↥(shiftSpan v s τ μ) = Fintype.card {a : Fin t // τ - s a = μ} := by
  classical
  apply finrank_span_eq_card
  exact (span_independent v hv).comp (fun a : {a : Fin t // τ - s a = μ} => a.1) Subtype.val_injective

lemma new_finrank (μ : ℝ) :
    R'.redMult x μ = Module.finrank ℝ ↥(Esp R x μ ⊓ orthSub (frameSpan v)) +
      Fintype.card {a : Fin t // τ - s a = μ} := by
  classical
  have dimensions := Submodule.finrank_sup_add_finrank_inf_eq
    (Esp R x μ ⊓ orthSub (frameSpan v)) (shiftSpan v s τ μ)
  rw [rest_shift_inf R R' x v s τ hv hperp heigen hchange μ, finrank_bot, add_zero,
    shiftSpan_finrank R R' x v s τ hv hperp heigen hchange μ, ← updated_eigenspace R R' x v s τ hv hperp heigen hchange μ] at dimensions
  exact dimensions

lemma old_span_le : frameSpan v ≤ Esp R x τ := by
  rw [frameSpan, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact mem_Esp.mpr ⟨heigen a, hperp a⟩

lemma old_complement_mem (y : Vec 16) (hy : y ∈ Esp R x τ) :
    y - frameProj v *ᵥ y ∈ Esp R x τ ⊓ orthSub (frameSpan v) := by
  refine ⟨mem_Esp.mpr ⟨?_, ?_⟩, projection_complement v hv y⟩
  · rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, (mem_Esp.mp hy).1,
      projection_eigen R R' x v s τ hv hperp heigen hchange]
    module
  · exact (perp x).sub_mem (mem_Esp.mp hy).2 ((span_le_perp v x hperp) (projection_mem v y))

lemma old_eigenspace_split :
    Esp R x τ = frameSpan v ⊔ (Esp R x τ ⊓ orthSub (frameSpan v)) := by
  apply le_antisymm
  · intro y hy
    exact Submodule.mem_sup.mpr ⟨frameProj v *ᵥ y, projection_mem v y,
      y - frameProj v *ᵥ y, old_complement_mem R R' x v s τ hv hperp heigen hchange y hy, by abel⟩
  · exact sup_le (old_span_le R R' x v s τ hv hperp heigen hchange) inf_le_left

lemma old_rest_finrank (μ : ℝ) :
    Module.finrank ℝ ↥(Esp R x μ ⊓ orthSub (frameSpan v)) =
      R.redMult x μ - (if μ = τ then t else 0) := by
  classical
  by_cases equal : μ = τ
  · subst μ
    have inf_zero : frameSpan v ⊓ (Esp R x τ ⊓ orthSub (frameSpan v)) = ⊥ := by
      apply eq_bot_iff.mpr
      intro y hy
      exact dotProduct_self_eq_zero.mp (hy.2.2 y hy.1)
    have dimensions := Submodule.finrank_sup_add_finrank_inf_eq
      (frameSpan v) (Esp R x τ ⊓ orthSub (frameSpan v))
    rw [inf_zero, finrank_bot, add_zero, ← old_eigenspace_split R R' x v s τ hv hperp heigen hchange] at dimensions
    have rank : Module.finrank ℝ ↥(frameSpan v) = t := by
      change Module.finrank ℝ ↥(Submodule.span ℝ (Set.range v)) = t
      simpa only [Fintype.card_fin] using finrank_span_eq_card (span_independent v hv)
    rw [rank] at dimensions
    simp only [ite_true]
    change _ = Module.finrank ℝ ↥(Esp R x τ) - t
    omega
  · have inclusion : Esp R x μ ≤ orthSub (frameSpan v) := by
      intro y hy
      rw [mem_orth_frame]
      intro a
      exact eig_dot_zero R x τ μ (Ne.symm equal) (v a) y (mem_Esp.mpr ⟨heigen a, hperp a⟩) hy
    rw [inf_eq_left.mpr inclusion, if_neg equal, Nat.sub_zero]
    rfl

theorem multiplicity_update (μ : ℝ) :
    R'.redMult x μ = R.redMult x μ - (if μ = τ then t else 0) +
      Fintype.card {a : Fin t // τ - s a = μ} := by
  classical
  rw [new_finrank R R' x v s τ hv hperp heigen hchange μ,
    old_rest_finrank R R' x v s τ hv hperp heigen hchange μ]

end Perturbation

end Osserman.Proofs.ThmEPerturbation

