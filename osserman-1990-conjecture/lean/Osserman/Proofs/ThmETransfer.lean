/-
ThmETransfer.lean — curvature perturbations along the Theorem E frame, paper 013, lines 762–778.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmEFrameConstruction
import Osserman.Proofs.ThmEPerturbation

namespace Osserman.Proofs.ThmETransfer

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.Spectral
open Osserman.Proofs.ThmEFrameConstruction Osserman.Proofs.ThmEProjection
open Osserman.Proofs.ThmEPerturbation

noncomputable def sumTensor {t : ℕ} (B : Fin t → CurvTensor 16) (s : Fin t → ℝ) : CurvTensor 16 where
  op := mkTri (fun u v w => ∑ a, s a • (B a).op u v w)
    (by intros; simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib])
    (by intros; simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul, mul_comm])
    (by intros; simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib])
    (by intros; simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul, mul_comm])
    (by intros; simp only [map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib])
    (by intros; simp only [map_smul, LinearMap.smul_apply, Finset.smul_sum, smul_smul, mul_comm])
  antisymm := by
    intro u v w
    change (∑ a, s a • (B a).op u v w) = -(∑ a, s a • (B a).op v u w)
    calc
      _ = ∑ a, s a • (-(B a).op v u w) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [(B a).antisymm]
      _ = _ := by simp only [smul_neg, Finset.sum_neg_distrib]
  skew := by
    intro u v w z
    change (∑ a, s a • (B a).op u v w) ⬝ᵥ z = -((∑ a, s a • (B a).op u v z) ⬝ᵥ w)
    simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]
    calc
      _ = ∑ a, s a * (-((B a).op u v z ⬝ᵥ w)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [(B a).skew]
      _ = _ := by simp only [mul_neg, Finset.sum_neg_distrib]
  bianchi := by
    intro u v w
    change (∑ a, s a • (B a).op u v w) + (∑ a, s a • (B a).op v w u) +
      (∑ a, s a • (B a).op w u v) = 0
    calc
      _ = ∑ a, s a • ((B a).op u v w + (B a).op v w u + (B a).op w u v) := by
        simp only [smul_add, Finset.sum_add_distrib]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [(B a).bianchi, smul_zero]

lemma sumTensor_op {t : ℕ} (B : Fin t → CurvTensor 16) (s : Fin t → ℝ) (u v w : Vec 16) :
    (sumTensor B s).op u v w = ∑ a, s a • (B a).op u v w := rfl

lemma perturb_tensor
    (hRJ : ∀ (J : Matrix (Fin 16) (Fin 16) ℝ), Jᵀ = -J →
      ∃ B : CurvTensor 16, (∀ u v w, B.op u v w = RJfun J u v w) ∧ ∀ x, B.jacobi x = jfam J x)
    (R : CurvTensor 16) {t : ℕ} (J : Fin t → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr J) (s : Fin t → ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - ∑ a, s a • RJfun (J a) u v w) ∧
      ∀ x, R'.jacobi x = R.jacobi x - ∑ a, s a • jfam (J a) x := by
  choose B hB hBJ using fun a => hRJ (J a) (hJ.1 a)
  let R' := subTensor R (sumTensor B s) 1
  have operator (u v w : Vec 16) : R'.op u v w = R.op u v w - ∑ a, s a • RJfun (J a) u v w := by
    simp only [R', subTensor_op, one_smul, sumTensor_op, hB]
  refine ⟨R', operator, ?_⟩
  intro x
  rw [Matrix.ext_iff_mulVec]
  intro y
  have each (a : Fin t) : RJfun (J a) y x x = jfam (J a) x *ᵥ y := by
    rw [← hB a, ← jacobi_mulVec, hBJ]
  simp only [Matrix.sub_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec, jacobi_mulVec, operator, each]

lemma perturbed_osserman (R R' : CurvTensor 16) (hO : R.IsOsserman) {t : ℕ}
    (J : Fin t → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J) (τ : ℝ)
    (hfr : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (R.jacobiMap x) τ)
    (s : Fin t → ℝ) (hjac : ∀ x, R'.jacobi x = R.jacobi x - ∑ a, s a • jfam (J a) x) :
    R'.IsOsserman := by
  classical
  have formula (x : Vec 16) (hx : x ⬝ᵥ x = 1) (μ : ℝ) :
      R'.redMult x μ = R.redMult x μ - (if μ = τ then t else 0) +
        Fintype.card {a : Fin t // τ - s a = μ} := by
    have frame := clifford_frame J hJ x hx
    have eigen (a : Fin t) : R.op (J a *ᵥ x) x x = τ • (J a *ᵥ x) :=
      Module.End.mem_eigenspace_iff.mp (hfr x hx a)
    exact multiplicity_update R R' x (fun a => J a *ᵥ x) s τ frame.1 frame.2 eigen (by simpa only [jfam] using hjac x) μ
  intro x y hx hy μ
  rw [formula x hx, formula y hy, hO x y hx hy μ]

theorem thm_E_intermediate_osserman_of_RJ_curv
    (hRJ : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J),
      (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ B : CurvTensor n, (∀ u v w, B.op u v w = RJfun J u v w) ∧ ∀ x, B.jacobi x = jfam J x)
    (R : CurvTensor 16) (hO : R.IsOsserman) {t : ℕ}
    (J : Fin t → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J) (τ : ℝ)
    (hfr : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (R.jacobiMap x) τ) (s : Fin t → ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - ∑ a, s a • RJfun (J a) u v w) ∧ R'.IsOsserman := by
  obtain ⟨R', operator, jacobi⟩ := perturb_tensor (fun J hJ => (hRJ J hJ).2) R J hJ s
  exact ⟨R', operator, perturbed_osserman R R' hO J hJ τ hfr s jacobi⟩

end Osserman.Proofs.ThmETransfer

