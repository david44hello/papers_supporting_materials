/-
Osserman/Proofs/CayleyCurvature.lean — the Brown–Gray formula R_Cay is an algebraic curvature tensor on ℝ^16
(paper 013, §1, l. 188-192): `sec1_Rcay_curv`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Curv
import Osserman.Proofs.StdSystem

namespace Osserman.Proofs.CayleyCurvature

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.StdSystem

lemma symmetric_wedge_curv (M : Matrix (Fin 16) (Fin 16) ℝ) (hM : Mᵀ = M) :
    ∃ R : CurvTensor 16, ∀ u v w, R.op u v w = wedge (M *ᵥ u) (M *ᵥ v) w := by
  refine exists_curv (fun u v w => wedge (M *ᵥ u) (M *ᵥ v) w) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro u u' v w
    simp only [wedge, Matrix.mulVec_add, add_dotProduct, add_smul, smul_add]
    module
  · intro c u v w
    simp only [wedge, Matrix.mulVec_smul, smul_dotProduct, smul_smul]
    module
  · intro u v v' w
    simp only [wedge, Matrix.mulVec_add, add_dotProduct, add_smul, smul_add]
    module
  · intro c u v w
    simp only [wedge, Matrix.mulVec_smul, smul_dotProduct, smul_smul]
    module
  · intro u v w w'
    simp only [wedge, dotProduct_add, add_smul]
    module
  · intro c u v w
    simp only [wedge, dotProduct_smul, smul_smul]
    module
  · intro u v w
    simp only [wedge]
    module
  · intro u v w z
    simp only [wedge, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  · intro u v w
    simp only [wedge]
    rw [symm_dot hM u w, symm_dot hM v u, symm_dot hM w v]
    module

theorem sec1_Rcay_curv_proved : ∃ R : CurvTensor 16, ∀ u v w, R.op u v w = RCayFun u v w := by
  obtain ⟨base, base_op⟩ := sec1_R1_curv_proved 16
  have each : ∀ i : Fin 9, ∃ R : CurvTensor 16, ∀ u v w,
      R.op u v w = wedge (stdSys i *ᵥ u) (stdSys i *ᵥ v) w :=
    fun i => symmetric_wedge_curv (stdSys i) (sec6_std_system_proved.2.1 i)
  choose tensors tensors_op using each
  let f := fun u v w => (3 : ℝ) • base.op u v w - ∑ i, (tensors i).op u v w
  have firstAdd : ∀ u u' v w, f (u + u') v w = f u v w + f u' v w := by
    intros
    simp only [f, map_add, LinearMap.add_apply, Finset.sum_add_distrib, smul_add]
    module
  have firstSmul : ∀ (c : ℝ) u v w, f (c • u) v w = c • f u v w := by
    intros
    simp only [f, map_smul, LinearMap.smul_apply, RingHom.id_apply]
    rw [← Finset.smul_sum]
    module
  have secondAdd : ∀ u v v' w, f u (v + v') w = f u v w + f u v' w := by
    intros
    simp only [f, map_add, LinearMap.add_apply, Finset.sum_add_distrib, smul_add]
    module
  have secondSmul : ∀ (c : ℝ) u v w, f u (c • v) w = c • f u v w := by
    intros
    simp only [f, map_smul, LinearMap.smul_apply, RingHom.id_apply]
    rw [← Finset.smul_sum]
    module
  have thirdAdd : ∀ u v w w', f u v (w + w') = f u v w + f u v w' := by
    intros
    simp only [f, map_add, Finset.sum_add_distrib, smul_add]
    module
  have thirdSmul : ∀ (c : ℝ) u v w, f u v (c • w) = c • f u v w := by
    intros
    simp only [f, map_smul, RingHom.id_apply]
    rw [← Finset.smul_sum]
    module
  have antisymmetric : ∀ u v w, f u v w = -f v u w := by
    intro u v w
    dsimp only [f]
    have eachAnti (i : Fin 9) := (tensors i).antisymm u v w
    rw [base.antisymm u v w]
    simp_rw [eachAnti]
    simp only [Finset.sum_neg_distrib]
    module
  have skew : ∀ u v w z, f u v w ⬝ᵥ z = -(f u v z ⬝ᵥ w) := by
    intro u v w z
    simp only [f, sub_dotProduct, smul_dotProduct, sum_dotProduct, smul_eq_mul]
    have eachSkew (i : Fin 9) := (tensors i).skew u v w z
    rw [base.skew u v w z]
    simp_rw [eachSkew]
    rw [Finset.sum_neg_distrib]
    ring
  have bianchi : ∀ u v w, f u v w + f v w u + f w u v = 0 := by
    intro u v w
    dsimp only [f]
    calc
      _ = (3 : ℝ) • (base.op u v w + base.op v w u + base.op w u v) -
          ∑ i, ((tensors i).op u v w + (tensors i).op v w u + (tensors i).op w u v) := by
        simp only [Finset.sum_add_distrib, smul_add]
        module
      _ = 0 := by
        rw [base.bianchi]
        simp only [CurvTensor.bianchi, Finset.sum_const_zero, smul_zero, sub_zero]
  obtain ⟨R, hR⟩ := exists_curv f firstAdd firstSmul secondAdd secondSmul thirdAdd thirdSmul antisymmetric skew bianchi
  refine ⟨R, ?_⟩
  intro u v w
  rw [hR]
  simp only [f, base_op, tensors_op, RCayFun, ROctFun, R1fun, wedge]
  module

end Osserman.Proofs.CayleyCurvature
