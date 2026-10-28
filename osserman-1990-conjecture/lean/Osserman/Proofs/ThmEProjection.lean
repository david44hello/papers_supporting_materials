/-
ThmEProjection.lean — orthonormal frame projections for Theorem E, paper 013, lines 762–778.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.Threshold
import Osserman.Proofs.Spectral

namespace Osserman.Proofs.ThmEProjection

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.Spectral

noncomputable def frameSpan {t : ℕ} (v : Fin t → Vec 16) : Submodule ℝ (Vec 16) :=
  Submodule.span ℝ (Set.range v)

noncomputable def frameProj {t : ℕ} (v : Fin t → Vec 16) : Matrix (Fin 16) (Fin 16) ℝ :=
  ∑ a, vecMulVec (v a) (v a)

lemma projection_action {t : ℕ} (v : Fin t → Vec 16) (y : Vec 16) :
    frameProj v *ᵥ y = ∑ a, (v a ⬝ᵥ y) • v a := by
  simp only [frameProj, Matrix.sum_mulVec, outer_mulVec_real]

lemma mem_orth_frame {t : ℕ} (v : Fin t → Vec 16) (y : Vec 16) :
    y ∈ orthSub (frameSpan v) ↔ ∀ a, v a ⬝ᵥ y = 0 := by
  constructor
  · intro h a
    exact h (v a) (Submodule.subset_span (Set.mem_range_self a))
  · intro h
    change ∀ z ∈ Submodule.span ℝ (Set.range v), z ⬝ᵥ y = 0
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨a, rfl⟩ := hz; exact h a
    | zero => exact zero_dotProduct _
    | add a b ha hb iha ihb => rw [add_dotProduct, iha, ihb, add_zero]
    | smul c z hz ih => rw [smul_dotProduct, ih, smul_zero]

lemma projection_frame {t : ℕ} (v : Fin t → Vec 16)
    (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0) (a : Fin t) :
    frameProj v *ᵥ v a = v a := by
  rw [projection_action]
  simp only [hv, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma projection_span {t : ℕ} (v : Fin t → Vec 16)
    (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0) (y : Vec 16) (hy : y ∈ frameSpan v) :
    frameProj v *ᵥ y = y := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact projection_frame v hv a
  | zero => exact Matrix.mulVec_zero _
  | add y z hy hz ihy ihz => rw [Matrix.mulVec_add, ihy, ihz]
  | smul c y hy ih => rw [Matrix.mulVec_smul, ih]

lemma projection_mem {t : ℕ} (v : Fin t → Vec 16) (y : Vec 16) : frameProj v *ᵥ y ∈ frameSpan v := by
  rw [projection_action]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a))

lemma projection_complement {t : ℕ} (v : Fin t → Vec 16)
    (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0) (y : Vec 16) :
    y - frameProj v *ᵥ y ∈ orthSub (frameSpan v) := by
  rw [mem_orth_frame]
  intro a
  rw [dotProduct_sub, projection_action, dotProduct_sum]
  simp only [dotProduct_smul, hv, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_self]

lemma projection_zero {t : ℕ} (v : Fin t → Vec 16) (y : Vec 16) (hy : y ∈ orthSub (frameSpan v)) :
    frameProj v *ᵥ y = 0 := by
  rw [projection_action]
  simp only [(mem_orth_frame v y).mp hy, zero_smul, Finset.sum_const_zero]

lemma span_le_perp {t : ℕ} (v : Fin t → Vec 16) (x : Vec 16) (hv : ∀ a, x ⬝ᵥ v a = 0) :
    frameSpan v ≤ perp x := by
  rw [frameSpan, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hv a

lemma span_independent {t : ℕ} (v : Fin t → Vec 16)
    (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0) : LinearIndependent ℝ v := by
  rw [linearIndependent_iff']
  intro s c zero a ha
  have image := congrArg (fun y : Vec 16 => v a ⬝ᵥ y) zero
  simpa only [dotProduct_sum, dotProduct_smul, hv, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, ha, ite_true, dotProduct_zero] using image

lemma updated_action {t : ℕ} (R R' : CurvTensor 16) (x : Vec 16) (v : Fin t → Vec 16) (s : Fin t → ℝ)
    (hchange : R'.jacobi x = R.jacobi x - ∑ a, s a • vecMulVec (v a) (v a)) (y : Vec 16) :
    R'.op y x x = R.op y x x - ∑ a, s a • ((v a ⬝ᵥ y) • v a) := by
  rw [← Osserman.Proofs.Curv.jacobi_mulVec, hchange]
  simp only [Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, outer_mulVec_real,
    Osserman.Proofs.Curv.jacobi_mulVec]

lemma updated_frame {t : ℕ} (R R' : CurvTensor 16) (x : Vec 16) (v : Fin t → Vec 16)
    (s : Fin t → ℝ) (τ : ℝ) (hv : ∀ a b, v a ⬝ᵥ v b = if a = b then 1 else 0)
    (heigen : ∀ a, R.op (v a) x x = τ • v a)
    (hchange : R'.jacobi x = R.jacobi x - ∑ a, s a • vecMulVec (v a) (v a)) (a : Fin t) :
    R'.op (v a) x x = (τ - s a) • v a := by
  rw [updated_action R R' x v s hchange, heigen]
  have sum : (∑ b, s b • ((v b ⬝ᵥ v a) • v b)) = s a • v a := by
    simp only [hv, ite_smul, one_smul, zero_smul, smul_ite, smul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [sum]
  module

lemma clifford_frame {t : ℕ} (J : Fin t → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J)
    (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
    (∀ a b, (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0) ∧
      ∀ a, x ⬝ᵥ (J a *ᵥ x) = 0 := by
  have moved (a : Fin t) (y : Vec 16) : x ⬝ᵥ (J a *ᵥ y) = -((J a *ᵥ x) ⬝ᵥ y) := by
    have equal := Matrix.dotProduct_transpose_mulVec (J a) y x
    rw [hJ.1, Matrix.neg_mulVec, dotProduct_neg, dotProduct_comm y (J a *ᵥ x)] at equal
    exact equal.symm
  constructor
  · intro a b
    have relation := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℝ => x ⬝ᵥ (M *ᵥ x)) (hJ.2 a b)
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add, moved,
      dotProduct_comm (J b *ᵥ x) (J a *ᵥ x)] at relation
    by_cases equal : a = b
    · subst b
      have two : (-2 : Matrix (Fin 16) (Fin 16) ℝ) = (-2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by norm_num [two_smul]
      simp only [ite_true, two, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hx, smul_eq_mul] at relation
      simp only [ite_true]
      linarith
    · simp only [equal, ite_false, Matrix.zero_mulVec, dotProduct_zero] at relation ⊢
      linarith
  · intro a
    have equal := Matrix.dotProduct_transpose_mulVec (J a) x x
    rw [hJ.1, Matrix.neg_mulVec, dotProduct_neg] at equal
    linarith

end Osserman.Proofs.ThmEProjection
