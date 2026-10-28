/-
Osserman/Proofs/Cayley.lean — Section 6 rows of paper 013 (l. 611-681), first batch: the sign change of a generator,
the pull-back of a curvature tensor, and the contraction of (eq:HopfM).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Curv
import Osserman.Proofs.Poly
import Osserman.Defs.TwoRoot
import Osserman.Cited.Isoparametric
import Osserman.Proofs.Threshold

namespace Osserman.Proofs.Cayley

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.Threshold

theorem sec6_sign_change_proved (H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 9) :
    Acay (Function.update H j (-H j)) = Acay H := by
  funext x
  have equal : (∑ i, (x ⬝ᵥ (Function.update H j (-H j) i *ᵥ x)) • Function.update H j (-H j) i) =
      ∑ i, (x ⬝ᵥ (H i *ᵥ x)) • H i := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases same : i = j
    · subst i
      simp [Matrix.neg_mulVec, dotProduct_neg]
    · simp [same]
  simp only [Acay, equal]

theorem pullback_curv_proved (R : CurvTensor 16) (T : Matrix (Fin 16) (Fin 16) ℝ)
    (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ) :
    ∃ R' : CurvTensor 16, ∀ u v w, R'.op u v w = pullbackFun T (fun a b c => R.op a b c) u v w := by
  have transpose_dot (a b : Vec 16) : (Tᵀ *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (T *ᵥ b) := by
    rw [dotProduct_comm]
    exact Matrix.dotProduct_transpose_mulVec T b a
  apply exists_curv (pullbackFun T (fun a b c => R.op a b c))
  · intro u u' v w
    simp only [pullbackFun, Matrix.mulVec_add, map_add, LinearMap.add_apply]
  · intro c u v w
    simp only [pullbackFun, Matrix.mulVec_smul, map_smul, LinearMap.smul_apply]
  · intro u v v' w
    simp only [pullbackFun, Matrix.mulVec_add, map_add, LinearMap.add_apply]
  · intro c u v w
    simp only [pullbackFun, Matrix.mulVec_smul, map_smul, LinearMap.smul_apply]
  · intro u v w w'
    simp only [pullbackFun, Matrix.mulVec_add, map_add]
  · intro c u v w
    simp only [pullbackFun, Matrix.mulVec_smul, map_smul]
  · intro u v w
    simp only [pullbackFun, R.antisymm (T *ᵥ u) (T *ᵥ v), Matrix.mulVec_neg]
  · intro u v w z
    simp only [pullbackFun, transpose_dot]
    exact R.skew _ _ _ _
  · intro u v w
    simp only [pullbackFun]
    rw [← Matrix.mulVec_add, ← Matrix.mulVec_add, R.bianchi, Matrix.mulVec_zero]

theorem sec6_hopf_contraction_proved (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) :
    x ⬝ᵥ ((∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x)) *ᵥ x) = ∑ i, (x ⬝ᵥ (S i *ᵥ x)) ^ 2 ∧
      x ⬝ᵥ ((vecMulVec x x + (1 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
        ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i)) *ᵥ x) =
        (x ⬝ᵥ x) ^ 2 + ((x ⬝ᵥ x) ^ 2 - ∑ i, (x ⬝ᵥ (S i *ᵥ x)) ^ 2) / 2 := by
  constructor
  · rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [quadratic_outer, dotProduct_comm (S i *ᵥ x) x]
  · simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.sub_mulVec, dotProduct_sub, quadratic_outer, Matrix.one_mulVec,
      Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul]
    change (x ⬝ᵥ x) ^ 2 + (1 / 2 : ℝ) *
      ((x ⬝ᵥ x) * (x ⬝ᵥ x) - ∑ i, (x ⬝ᵥ (S i *ᵥ x)) * (x ⬝ᵥ (S i *ᵥ x))) = _
    simp only [← pow_two]
    ring

end Osserman.Proofs.Cayley
