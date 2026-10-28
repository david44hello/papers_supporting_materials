/-
Osserman/Proofs/CayleyJacobi.lean — the Jacobi family of R_Cay (all three display lines) and its reduced eigenspaces
of dimensions 8 and 7 (paper 013, §6, l. 660-668): `sec6_jacobi_Rcay`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.StdSystem
import Osserman.Proofs.CayleyEigenspaces

namespace Osserman.Proofs.CayleyJacobi

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.Curv
open Osserman.Proofs.Hopf Osserman.Proofs.StdSystem Osserman.Proofs.CayleyEigenspaces

lemma ROct_first (x y : Vec 16) :
    ROctFun y x x = (3 : ℝ) • ((vecMulVec x x - (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ)) *ᵥ y) +
      (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ y -
      (∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i) *ᵥ y := by
  have each (i : Fin 9) : wedge (stdSys i *ᵥ y) (stdSys i *ᵥ x) x =
      vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x) *ᵥ y -
      ((x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i) *ᵥ y := by
    simp only [wedge, outer_mulVec_real, Matrix.smul_mulVec]
    rw [symm_dot (sec6_std_system_proved.2.1 i) y x, dotProduct_comm (stdSys i *ᵥ x) x]
  rw [ROctFun]
  simp_rw [each]
  rw [Finset.sum_sub_distrib, ← Matrix.sum_mulVec, ← Matrix.sum_mulVec]
  simp only [wedge, Matrix.sub_mulVec, outer_mulVec_real, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_comm y x]
  module

lemma ROct_second (x y : Vec 16) :
    ROctFun y x x = ((4 : ℝ) • vecMulVec x x - (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
      (3 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
        ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i)) *ᵥ y := by
  rw [ROct_first, (sec6_hopf_proved stdSys sec6_std_system_proved.2 x).1]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  module

lemma ROct_third (x y : Vec 16) : ROctFun y x x = -((Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y) := by
  rw [ROct_second]
  simp only [Osserman.Pi, Acay, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  module

lemma RCay_jacobi (x y : Vec 16) : RCayFun y x x = (Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y := by
  rw [RCayFun, ROct_third, neg_neg]

lemma positive_perp_dimension (A : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16)
    (hx : x ⬝ᵥ x = 1) (fixes : A *ᵥ x = x)
    (dimension : Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' A) 1) = 8) :
    Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' A) 1 ⊓ perp x) = 7 := by
  let E := Module.End.eigenspace (Matrix.toLin' A) 1
  let f : E →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ x).comp E.subtype
  have member : x ∈ E := by
    apply Module.End.mem_eigenspace_iff.mpr
    change A *ᵥ x = (1 : ℝ) • x
    rw [fixes, one_smul]
  have nonzero : f ≠ 0 := by
    intro equal
    have evaluated := congrArg (fun g : E →ₗ[ℝ] ℝ => g ⟨x, member⟩) equal
    change x ⬝ᵥ x = 0 at evaluated
    linarith
  have rank := Module.Dual.finrank_ker_add_one_of_ne_zero nonzero
  let equivalence : LinearMap.ker f ≃ₗ[ℝ] ↥(E ⊓ perp x) :=
    { toFun := fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have same := equivalence.finrank_eq
  change Module.finrank ℝ ↥(E ⊓ perp x) = 7
  change Module.finrank ℝ E = 8 at dimension
  omega

lemma reduced_dimensions (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) 1 ⊓ perp x) = 8 ∧
      Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) 4 ⊓ perp x) = 7 := by
  let S := stdSys
  let A := Hcomb S (hvec S x)
  have system : IsSymmCliffordSystem S := sec6_std_system_proved.2
  have hnorm := system_norm_identity S system
  have unit := hvec_unit S hnorm x hx
  have fixes : A *ᵥ x = x := Hcomb_hvec_mulVec S (fun i => system.1 i) hnorm x hx
  have dimensions := combination_eigenspace_dimensions S system (hvec S x) unit
  have negative_perp : Module.End.eigenspace (Matrix.toLin' A) (-1) ≤ perp x := by
    intro y hy
    have eigen : A *ᵥ y = -y := by
      simpa only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, neg_one_smul] using hy
    have symmetric := Hcomb_symm S (fun i => system.1 i) (hvec S x)
    have orthogonal := symmetric.dotProduct_mulVec_comm (x := x) (y := y)
    rw [eigen, fixes, dotProduct_neg, dotProduct_comm y x] at orthogonal
    change x ⬝ᵥ y = 0
    linarith
  have action (y : Vec 16) (hy : y ∈ perp x) :
      (Pi x + (3 : ℝ) • Acay S x) *ᵥ y = (5 / 2 : ℝ) • y + (3 / 2 : ℝ) • (A *ᵥ y) := by
    change x ⬝ᵥ y = 0 at hy
    simp only [Osserman.Pi, Acay, hx, one_smul, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, outer_mulVec_real, hy, zero_smul]
    change _ = (5 / 2 : ℝ) • y + (3 / 2 : ℝ) • ((∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) *ᵥ y)
    module
  have one : (Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay S x)) 1 ⊓ perp x : Submodule ℝ (Vec 16)) =
      Module.End.eigenspace (Matrix.toLin' A) (-1) := by
    ext y
    constructor
    · intro hy
      have eigen : (Pi x + (3 : ℝ) • Acay S x) *ᵥ y = y := by
        have value := Module.End.mem_eigenspace_iff.mp hy.1
        simpa only [Matrix.toLin'_apply, one_smul] using value
      rw [action y hy.2] at eigen
      apply Module.End.mem_eigenspace_iff.mpr
      change A *ᵥ y = (-1 : ℝ) • y
      ext i
      have entry := congrFun eigen i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at entry ⊢
      linarith
    · intro hy
      refine ⟨?_, negative_perp hy⟩
      have eigen : A *ᵥ y = -y := by
        simpa only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, neg_one_smul] using hy
      apply Module.End.mem_eigenspace_iff.mpr
      change (Pi x + (3 : ℝ) • Acay S x) *ᵥ y = (1 : ℝ) • y
      rw [action y (negative_perp hy), eigen]
      module
  have four : (Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay S x)) 4 ⊓ perp x : Submodule ℝ (Vec 16)) =
      Module.End.eigenspace (Matrix.toLin' A) 1 ⊓ perp x := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, hy.2⟩
      have eigen : (Pi x + (3 : ℝ) • Acay S x) *ᵥ y = (4 : ℝ) • y := by
        exact Module.End.mem_eigenspace_iff.mp hy.1
      rw [action y hy.2] at eigen
      apply Module.End.mem_eigenspace_iff.mpr
      change A *ᵥ y = (1 : ℝ) • y
      ext i
      have entry := congrFun eigen i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at entry ⊢
      linarith
    · intro hy
      refine ⟨?_, hy.2⟩
      have eigen : A *ᵥ y = y := by
        have value := Module.End.mem_eigenspace_iff.mp hy.1
        simpa only [Matrix.toLin'_apply, one_smul] using value
      apply Module.End.mem_eigenspace_iff.mpr
      change (Pi x + (3 : ℝ) • Acay S x) *ᵥ y = (4 : ℝ) • y
      rw [action y hy.2, eigen]
      module
  change Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay S x)) 1 ⊓ perp x) = 8 ∧
    Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay S x)) 4 ⊓ perp x) = 7
  rw [one, four]
  exact ⟨dimensions.2, positive_perp_dimension A x hx fixes dimensions.1⟩

theorem sec6_jacobi_Rcay_proved :
    (∀ x y : Vec 16, ROctFun y x x = (3 : ℝ) • ((vecMulVec x x - (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ)) *ᵥ y) +
      (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ y - (∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i) *ᵥ y) ∧
    (∀ x y : Vec 16, ROctFun y x x = ((4 : ℝ) • vecMulVec x x - (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
      (3 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) + ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i)) *ᵥ y) ∧
    (∀ x y : Vec 16, ROctFun y x x = -((Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y)) ∧
      (∀ x y : Vec 16, RCayFun y x x = (Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) 1 ⊓ perp x) = 8 ∧
        Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) 4 ⊓ perp x) = 7 :=
  ⟨ROct_first, ROct_second, ROct_third, RCay_jacobi, reduced_dimensions⟩

end Osserman.Proofs.CayleyJacobi
