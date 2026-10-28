/-
Osserman/Proofs/CayleySectional.lean — the sectional curvatures of R_Cay lie in [1, 4] with both ends attained, and
R_Cay satisfies Theorem C's hypothesis (paper 013, §1, l. 190-192): `sec1_Rcay_sectional`, `thm_C_hyp_nonvacuous`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.CayleyCurvature
import Osserman.Proofs.CayleyJacobi

namespace Osserman.Proofs.CayleySectional

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.StdSystem
open Osserman.Proofs.CayleyEigenspaces Osserman.Proofs.CayleyJacobi Osserman.Proofs.CayleyCurvature

theorem thm_C_hyp_nonvacuous_proved : ∃ R : CurvTensor 16,
    (∀ u v w, R.op u v w = RCayFun u v w) ∧ TwoRootHyp R 1 3 := by
  obtain ⟨R, hR⟩ := sec1_Rcay_curv_proved
  refine ⟨R, hR, by norm_num, ?_⟩
  intro x hx
  have maps : R.jacobiMap x = Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x) := by
    apply LinearMap.ext
    intro y
    change R.op y x x = (Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y
    rw [hR, RCay_jacobi]
  have dimensions := reduced_dimensions x hx
  constructor
  · change Module.finrank ℝ ↥(Module.End.eigenspace (R.jacobiMap x) 1 ⊓ perp x) = 8
    rw [maps]
    exact dimensions.1
  · change Module.finrank ℝ ↥(Module.End.eigenspace (R.jacobiMap x) (1 + 3) ⊓ perp x) = 7
    rw [maps, show (1 : ℝ) + 3 = 4 by norm_num]
    exact dimensions.2

lemma jacobi_perp_action (x : Vec 16) (hx : x ⬝ᵥ x = 1) (y : Vec 16) (hy : x ⬝ᵥ y = 0) :
    (Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y =
      (5 / 2 : ℝ) • y + (3 / 2 : ℝ) • (Hcomb stdSys (hvec stdSys x) *ᵥ y) := by
  simp only [Osserman.Pi, Acay, hx, one_smul, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, outer_mulVec_real, hy, zero_smul, Hcomb, hvec]
  module

lemma sectional_bounds (x y : Vec 16) (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) (hxy : x ⬝ᵥ y = 0) :
    1 ≤ RCayFun y x x ⬝ᵥ y ∧ RCayFun y x x ⬝ᵥ y ≤ 4 := by
  have system := sec6_std_system_proved.2
  have hnorm := system_norm_identity stdSys system
  let a := hvec stdSys x
  have ha : a ⬝ᵥ a = 1 := hvec_unit stdSys hnorm x hx
  have haNeg : (-a) ⬝ᵥ (-a) = 1 := by simpa only [neg_dotProduct, dotProduct_neg, neg_neg] using ha
  have upper := quadratic_bound stdSys hnorm a ha y
  have lower := quadratic_bound stdSys hnorm (-a) haNeg y
  have negcomb : Hcomb stdSys (-a) = -Hcomb stdSys a := by
    simpa only [neg_one_smul] using Hcomb_smul stdSys (-1) a
  rw [hy] at upper
  rw [hy, negcomb, Matrix.neg_mulVec, dotProduct_neg] at lower
  have evaluation : RCayFun y x x ⬝ᵥ y =
      (5 / 2 : ℝ) + (3 / 2 : ℝ) * (y ⬝ᵥ (Hcomb stdSys a *ᵥ y)) := by
    rw [RCay_jacobi, jacobi_perp_action x hx y hxy, add_dotProduct, smul_dotProduct,
      smul_dotProduct, hy, dotProduct_comm (Hcomb stdSys a *ᵥ y) y]
    simp only [smul_eq_mul]
    ring
  rw [evaluation]
  constructor <;> linarith

lemma sectional_attained (x : Vec 16) (hx : x ⬝ᵥ x = 1) (value : ℝ)
    (positive : 0 < Module.finrank ℝ ↥(Module.End.eigenspace
      (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) value ⊓ perp x)) :
    ∃ y : Vec 16, y ⬝ᵥ y = 1 ∧ x ⬝ᵥ y = 0 ∧ RCayFun y x x ⬝ᵥ y = value := by
  let E := Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) value ⊓ perp x
  obtain ⟨z, nonzero⟩ := Module.finrank_pos_iff_exists_ne_zero.mp positive
  have vectorNonzero : (z : Vec 16) ≠ 0 := by
    intro equal
    exact nonzero (Subtype.ext equal)
  obtain ⟨c, unit⟩ := unit_rescale (z : Vec 16) vectorNonzero
  have member : c • (z : Vec 16) ∈ E := E.smul_mem c z.property
  have eigen := Module.End.mem_eigenspace_iff.mp member.1
  change (Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ (c • (z : Vec 16)) = value • (c • (z : Vec 16)) at eigen
  refine ⟨c • (z : Vec 16), unit, member.2, ?_⟩
  rw [RCay_jacobi, eigen, smul_dotProduct, unit, smul_eq_mul, mul_one]

theorem sec1_Rcay_sectional_proved :
    (∀ u v : Vec 16, u ⬝ᵥ u = 1 → v ⬝ᵥ v = 1 → u ⬝ᵥ v = 0 → 1 ≤ RCayFun v u u ⬝ᵥ v ∧ RCayFun v u u ⬝ᵥ v ≤ 4) ∧
    (∃ u v : Vec 16, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧ RCayFun v u u ⬝ᵥ v = 1) ∧
    (∃ u v : Vec 16, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧ RCayFun v u u ⬝ᵥ v = 4) := by
  refine ⟨sectional_bounds, ?_, ?_⟩
  · let x : Vec 16 := Pi.single 0 1
    have hx : x ⬝ᵥ x = 1 := by simp [x]
    have dimension := (reduced_dimensions x hx).1
    obtain ⟨y, hy, hxy, value⟩ := sectional_attained x hx 1 (by rw [dimension]; norm_num)
    exact ⟨x, y, hx, hy, hxy, value⟩
  · let x : Vec 16 := Pi.single 0 1
    have hx : x ⬝ᵥ x = 1 := by simp [x]
    have dimension := (reduced_dimensions x hx).2
    obtain ⟨y, hy, hxy, value⟩ := sectional_attained x hx 4 (by rw [dimension]; norm_num)
    exact ⟨x, y, hx, hy, hxy, value⟩

end Osserman.Proofs.CayleySectional
