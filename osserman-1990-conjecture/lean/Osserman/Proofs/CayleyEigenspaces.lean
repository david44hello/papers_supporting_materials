/-
Osserman/Proofs/CayleyEigenspaces.lean — nonconstancy of h and the eigenspaces of S_w for a symmetric Clifford system
of nine matrices on ℝ^16 (paper 013, §6): `sec6_Sw`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Hopf
import Osserman.Proofs.Threshold2

namespace Osserman.Proofs.CayleyEigenspaces

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.Threshold2
open Osserman.Proofs.CayleyProducts Osserman.Proofs.Hopf

lemma system_norm_identity (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S)
    (x : Vec 16) : ∑ i, hvec S x i ^ 2 = (x ⬝ᵥ x) ^ 2 := (sec6_hopf_proved S hS x).2

lemma system_nonconstant (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    NonconstantOnUnit S := by
  let x : Vec 16 := Pi.single 0 1
  have hx : x ⬝ᵥ x = 1 := by simp [x]
  have ha := hvec_unit S (system_norm_identity S hS) x hx
  have nonzero : hvec S x ≠ 0 := by intro equal; simp [equal] at ha
  obtain ⟨i, hi⟩ : ∃ i, hvec S x i ≠ 0 := by
    by_contra absent
    push Not at absent
    apply nonzero
    ext i
    exact absent i
  obtain ⟨j, different⟩ := exists_ne i
  let y := S j *ᵥ x
  have hy : y ⬝ᵥ y = 1 := by
    dsimp only [y]
    rw [(show (S j).IsSymm from hS.1 j).dotProduct_mulVec_comm,
      Matrix.mulVec_mulVec, system_square S hS, Matrix.one_mulVec, hx]
  have conjugate : S j * S i * S j = -S i := by
    have identity := word_conjugate S hS j [i]
    simpa [word, wordSign, different] using identity
  have reflected : hvec S y i = -hvec S x i := by
    change (S j *ᵥ x) ⬝ᵥ (S i *ᵥ (S j *ᵥ x)) = -(x ⬝ᵥ (S i *ᵥ x))
    rw [dotProduct_comm (S j *ᵥ x), (show (S j).IsSymm from hS.1 j).dotProduct_mulVec_comm,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, conjugate, Matrix.neg_mulVec, dotProduct_neg]
  refine ⟨x, y, hx, hy, ?_⟩
  intro equal
  apply hi
  have entry := congrFun equal i
  rw [reflected] at entry
  linarith

lemma combination_product (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (u v : Fin 9 → ℝ) :
    Hcomb S u * Hcomb S v = ∑ i, ∑ j, (u i * v j) • (S i * S j) := by
  simp only [Hcomb, Matrix.sum_mul, Matrix.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

lemma combination_anticommutator (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ)
    (hS : IsSymmCliffordSystem S) (u v : Fin 9 → ℝ) :
    Hcomb S u * Hcomb S v + Hcomb S v * Hcomb S u = (2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  rw [combination_product, combination_product]
  have reverse : (∑ i, ∑ j, (v i * u j) • (S i * S j)) =
      ∑ i, ∑ j, (u i * v j) • (S j * S i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]
  rw [reverse]
  have pair : (∑ i, ∑ j, (u i * v j) • (S i * S j)) +
      (∑ i, ∑ j, (u i * v j) • (S j * S i)) =
      ∑ i, ∑ j, (u i * v j) • (S i * S j + S j * S i) := by
    simp only [smul_add, Finset.sum_add_distrib]
  rw [pair]
  simp_rw [hS.2]
  have two : (2 : Matrix (Fin 16) (Fin 16) ℝ) = (2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
    rw [two_smul]
    norm_num
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_eq_left True.intro, two, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp only [dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma combination_eigenspace_dimensions (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ)
    (hS : IsSymmCliffordSystem S) (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) :
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (Hcomb S w)) 1) = 8 ∧
      Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' (Hcomb S w)) (-1)) = 8 := by
  have dimensions := lem_4_1_pm_eigenspaces_proved S (fun i => hS.1 i) (system_norm_identity S hS)
    rfl (by norm_num) (system_nonconstant S hS) w hw
  have plus : Module.End.eigenspace (Matrix.toLin' (Hcomb S w)) 1 =
      LinearMap.ker (Matrix.toLin' (1 - Hcomb S w)) := by
    ext y
    simp only [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, one_smul, sub_eq_zero]
    exact eq_comm
  have minus : Module.End.eigenspace (Matrix.toLin' (Hcomb S w)) (-1) =
      LinearMap.ker (Matrix.toLin' (1 + Hcomb S w)) := by
    ext y
    simp only [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.add_mulVec, Matrix.one_mulVec, neg_one_smul]
    constructor
    · intro equal
      rw [equal, add_neg_cancel]
    · intro equal
      exact eq_neg_of_add_eq_zero_right equal
  rw [plus, minus]
  exact ⟨dimensions.2.1, dimensions.2.2⟩

theorem sec6_Sw_proved (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) (hx : x ≠ 0) :
    let q := x ⬝ᵥ x
    let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (S i *ᵥ x)) / q
    let Sw := ∑ i, w i • S i
    let Qx := (1 / 2 : ℝ) • (q • (1 : Matrix (Fin 16) (Fin 16) ℝ) + ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i)
    Acay S x = Qx - vecMulVec x x ∧ Sw *ᵥ x = x ∧ Sw * Sw = 1 ∧ Swᵀ = Sw ∧
      Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' Sw) 1) = 8 ∧
      Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' Sw) (-1)) = 8 ∧
      (∀ u : Fin 9 → ℝ, u ⬝ᵥ w = 0 → Sw *ᵥ ((∑ i, u i • S i) *ᵥ x) = -((∑ i, u i • S i) *ᵥ x)) ∧
      ∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x) = vecMulVec x x + q • (1 : Matrix (Fin 16) (Fin 16) ℝ) - Qx ∧
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i = (2 : ℝ) • Qx - q • (1 : Matrix (Fin 16) (Fin 16) ℝ) ∧
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i = q • Sw ∧ Qx = (q / 2) • (1 + Sw) := by
  let q := x ⬝ᵥ x
  let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (S i *ᵥ x)) / q
  let Sw := ∑ i, w i • S i
  let Qx := (1 / 2 : ℝ) • (q • (1 : Matrix (Fin 16) (Fin 16) ℝ) + ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i)
  change Acay S x = Qx - vecMulVec x x ∧ _
  have nonnegative : 0 ≤ q := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have positive : 0 < q := lt_of_le_of_ne nonnegative
    (fun equal => hx (dotProduct_self_eq_zero.mp equal.symm))
  have qne := ne_of_gt positive
  have hnorm := system_norm_identity S hS
  have unit : w ⬝ᵥ w = 1 := by
    have squares : ∑ i, w i ^ 2 = 1 := by
      change (∑ i, (hvec S x i / q) ^ 2) = 1
      simp only [div_pow, ← Finset.sum_div]
      rw [hnorm]
      change q ^ 2 / q ^ 2 = 1
      exact div_self (pow_ne_zero 2 qne)
    simpa only [dotProduct, pow_two] using squares
  have sh : (∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) = q • Sw := by
    dsimp only [Sw, w]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul]
    congr 1
    field_simp
  have dot : x ⬝ᵥ (Sw *ᵥ x) = q := by
    change x ⬝ᵥ (Hcomb S w *ᵥ x) = q
    rw [quadratic_combination]
    change (∑ i, (hvec S x i / q) * hvec S x i) = q
    calc
      _ = (∑ i, hvec S x i ^ 2) / q := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = q := by rw [hnorm]; change q ^ 2 / q = q; field_simp
  have psd := comb_posSemidef S (fun i => hS.1 i) hnorm w unit
  change (1 - Sw).PosSemidef at psd
  have zero : x ⬝ᵥ ((1 - Sw) *ᵥ x) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, dot]
    exact sub_self q
  have kernel : (1 - Sw) *ᵥ x = 0 :=
    (psd.dotProduct_mulVec_zero_iff (x := x)).mp (by simpa only [star_trivial] using zero)
  have fixes : Sw *ᵥ x = x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at kernel
    exact (sub_eq_zero.mp kernel).symm
  have square : Sw * Sw = 1 := threshold_sq S (fun i => hS.1 i) hnorm rfl (by norm_num)
    (system_nonconstant S hS) w unit
  have symmetric : Swᵀ = Sw := Hcomb_symm S (fun i => hS.1 i) w
  have dimensions := combination_eigenspace_dimensions S hS w unit
  refine ⟨rfl, fixes, square, symmetric, dimensions.1, dimensions.2, ?_, ?_, ?_, sh, ?_⟩
  · intro u hu
    have uv : w ⬝ᵥ u = 0 := (dotProduct_comm w u).trans hu
    have anti := combination_anticommutator S hS w u
    rw [uv, mul_zero, zero_smul] at anti
    have relation := eq_neg_of_add_eq_zero_left anti
    change Hcomb S w *ᵥ (Hcomb S u *ᵥ x) = -(Hcomb S u *ᵥ x)
    rw [Matrix.mulVec_mulVec, relation, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    change -(Hcomb S u *ᵥ (Sw *ᵥ x)) = -(Hcomb S u *ᵥ x)
    rw [fixes]
  · rw [(sec6_hopf_proved S hS x).1]
    module
  · module
  · rw [sh]
    module

end Osserman.Proofs.CayleyEigenspaces
