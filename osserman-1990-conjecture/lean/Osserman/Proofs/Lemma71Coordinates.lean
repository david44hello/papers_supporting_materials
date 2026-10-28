/-
Osserman/Proofs/Lemma71Coordinates.lean — conjugate coordinates in Lemma 7.1, paper 013, lines 701–711.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.StdSystem
import Osserman.Proofs.OctonionFacts

namespace Osserman.Proofs.Lemma71Coordinates

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts
open Osserman.Proofs.StdSystem

def conjLinear : Vec 16 →ₗ[ℝ] Vec 16 where
  toFun := conjChangeFun
  map_add' := by
    intro x y
    simp only [conjChangeFun, first_add, second_add, oconj_add, pair_add]
  map_smul' := by
    intro c x
    simp only [conjChangeFun, first_smul, second_smul, oconj_smul, pair_smul,
      RingHom.id_apply, id_eq]

lemma conj_mulVec (x : Vec 16) : conjChange *ᵥ x = conjChangeFun x := by
  change LinearMap.toMatrix' conjLinear *ᵥ x = conjLinear x
  exact LinearMap.toMatrix'_mulVec _ _

lemma conj_invol (x : Vec 16) : conjChange *ᵥ (conjChange *ᵥ x) = x := by
  simp only [conj_mulVec, conjChangeFun, first_pair, second_pair, oconj_invol, pair_parts]

lemma conj_symmetric : conjChangeᵀ = conjChange := by
  apply Matrix.IsSymm.ext
  intro r c
  have adjoint (x y : Vec 16) : conjChangeFun x ⬝ᵥ y = x ⬝ᵥ conjChangeFun y := by
    have parts (a b c d : Vec 8) : conjChangeFun (octPair a b) ⬝ᵥ octPair c d =
        octPair a b ⬝ᵥ conjChangeFun (octPair c d) := by
      simp only [conjChangeFun, first_pair, second_pair, pair_dot, oconj_move]
    simpa only [pair_parts] using parts (oct1 x) (oct2 x) (oct1 y) (oct2 y)
  have equal := adjoint (Pi.single r 1) (Pi.single c 1)
  simpa only [← conj_mulVec, Matrix.mulVec_single_one, dotProduct_single_one,
    single_one_dotProduct, Matrix.col_apply] using equal

lemma conj_square : conjChange * conjChange = 1 := by
  apply Matrix.mulVec_injective
  funext x
  simp only [← Matrix.mulVec_mulVec, conj_invol, Matrix.one_mulVec]

theorem lem_7_1_conj_change_proved :
    (∀ x : Vec 16, conjChange *ᵥ x = conjChangeFun x) ∧
      conjChange ∈ Matrix.orthogonalGroup (Fin 16) ℝ ∧ conjChange * conjChange = 1 ∧
      ∀ a b : Vec 8, oconj a ⬝ᵥ oconj b = a ⬝ᵥ b := by
  refine ⟨conj_mulVec, ?_, conj_square, oconj_dot⟩
  rw [Matrix.mem_orthogonalGroup_iff, conj_symmetric, conj_square]

lemma conj_dot (x y : Vec 16) : (conjChange *ᵥ x) ⬝ᵥ (conjChange *ᵥ y) = x ⬝ᵥ y := by
  have parts (a b c d : Vec 8) :
      conjChangeFun (octPair a b) ⬝ᵥ conjChangeFun (octPair c d) =
        octPair a b ⬝ᵥ octPair c d := by
    simp only [conjChangeFun, first_pair, second_pair, pair_dot, oconj_dot]
  simpa only [conj_mulVec, pair_parts] using parts (oct1 x) (oct2 x) (oct1 y) (oct2 y)

lemma pair_sum {ι : Type*} (s : Finset ι) (a b : ι → Vec 8) :
    ∑ i ∈ s, octPair (a i) (b i) = octPair (∑ i ∈ s, a i) (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    ext i
    refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
      simp only [octPair, Fin.append_left, Fin.append_right, Pi.zero_apply]
  | @insert k s hk ih => simp only [Finset.sum_insert hk, ih, pair_add]

lemma omul_sum_left {ι : Type*} (s : Finset ι) (a : ι → Vec 8) (u : Vec 8) :
    omul (∑ i ∈ s, a i) u = ∑ i ∈ s, omul (a i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_omul]
  | @insert k s hk ih => simp only [Finset.sum_insert hk, omul_add_left, ih]

lemma basis_sum (a : Vec 8) : ∑ k : Fin 8, a k • octBasis k = a := by
  ext j
  simp [octBasis, Finset.sum_apply, Pi.single_apply]

lemma std_zero_new (y : Vec 16) :
    conjChange *ᵥ (stdSys 0 *ᵥ (conjChange *ᵥ y)) = octPair (oct1 y) (-oct2 y) := by
  simp only [conj_mulVec, std_mulVec, stdSysFun, Fin.val_zero, dite_true, conjChangeFun,
    first_pair, second_pair, oconj_neg, oconj_invol]

lemma std_succ_new (k : Fin 8) (y : Vec 16) :
    conjChange *ᵥ (stdSys k.succ *ᵥ (conjChange *ᵥ y)) =
      octPair (omul (octBasis k) (oct2 y)) (omul (oconj (octBasis k)) (oct1 y)) := by
  have ne : k.succ.val ≠ 0 := by simp
  have bound : k.succ.val - 1 < 8 := by simpa using k.isLt
  have index : (⟨k.succ.val - 1, bound⟩ : Fin 8) = k := by ext; simp
  simp only [conj_mulVec, std_mulVec, stdSysFun, ne, dite_false, index,
    conjChangeFun, first_pair, second_pair, oconj_invol, oct_conj_mul_proved]

theorem lem_7_1_S_new_coords_proved (w0 : ℝ) (a : Vec 8) (y : Vec 16) :
    conjChange *ᵥ (stdComb w0 a *ᵥ (conjChange *ᵥ y)) =
      octPair (w0 • oct1 y + omul a (oct2 y)) (omul (oconj a) (oct1 y) - w0 • oct2 y) := by
  have conjugate_add (x z : Vec 16) : conjChange *ᵥ (x + z) =
      conjChange *ᵥ x + conjChange *ᵥ z := Matrix.mulVec_add _ _ _
  have conjugate_smul (c : ℝ) (x : Vec 16) : conjChange *ᵥ (c • x) = c • (conjChange *ᵥ x) :=
    Matrix.mulVec_smul _ _ _
  have conjugate_sum (f : Fin 8 → Vec 16) : conjChange *ᵥ (∑ k, f k) =
      ∑ k, conjChange *ᵥ f k := by
    simp only [conj_mulVec]
    change conjLinear (∑ k, f k) = ∑ k, conjLinear (f k)
    exact map_sum conjLinear f Finset.univ
  have conj_sum (f : Fin 8 → Vec 8) : oconj (∑ k, f k) = ∑ k, oconj (f k) := by
    have sum_id (s : Finset (Fin 8)) : oconj (∑ k ∈ s, f k) = ∑ k ∈ s, oconj (f k) := by
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        simpa only [zero_smul] using oconj_smul (0 : Vec 8) (0 : ℝ)
      | @insert k s hk ih => simp only [Finset.sum_insert hk, oconj_add, ih]
    exact sum_id Finset.univ
  simp only [stdComb, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    conjugate_add, conjugate_smul, conjugate_sum, std_zero_new, std_succ_new, pair_smul]
  rw [pair_sum, pair_add]
  have first : (∑ k : Fin 8, a k • omul (octBasis k) (oct2 y)) = omul a (oct2 y) := by
    conv_rhs => rw [← basis_sum a, omul_sum_left]
    simp only [omul_smul_left]
  have second : (∑ k : Fin 8, a k • omul (oconj (octBasis k)) (oct1 y)) =
      omul (oconj a) (oct1 y) := by
    conv_rhs => rw [← basis_sum a, conj_sum]
    rw [omul_sum_left]
    simp only [oconj_smul, omul_smul_left]
  rw [first, second]
  congr 1
  module

lemma conj_injective : Function.Injective (fun x : Vec 16 => conjChange *ᵥ x) := by
  intro x y h
  have equal := congrArg (fun z => conjChange *ᵥ z) h
  simpa only [conj_invol] using equal

lemma std_eigen_iff (w0 : ℝ) (a : Vec 8) (y : Vec 16) :
    stdComb w0 a *ᵥ (conjChange *ᵥ y) = conjChange *ᵥ y ↔
      w0 • oct1 y + omul a (oct2 y) = oct1 y ∧
        omul (oconj a) (oct1 y) - w0 • oct2 y = oct2 y := by
  constructor
  · intro equal
    have image := congrArg (fun z => conjChange *ᵥ z) equal
    rw [lem_7_1_S_new_coords_proved, conj_invol] at image
    exact ⟨by simpa only [first_pair] using congrArg oct1 image,
      by simpa only [second_pair] using congrArg oct2 image⟩
  · intro equal
    apply conj_injective
    change conjChange *ᵥ (stdComb w0 a *ᵥ (conjChange *ᵥ y)) = conjChange *ᵥ (conjChange *ᵥ y)
    rw [lem_7_1_S_new_coords_proved, conj_invol, equal.1, equal.2, pair_parts]

theorem lem_7_1_eigenspace_line_proved (w0 : ℝ) (a : Vec 8) (hw : w0 ^ 2 + a ⬝ᵥ a = 1) :
    (w0 ≠ -1 → {y : Vec 16 | stdComb w0 a *ᵥ (conjChange *ᵥ y) = conjChange *ᵥ y} =
        cayLine ((1 + w0)⁻¹ • oconj a)) ∧
      (w0 = -1 → {y : Vec 16 | stdComb w0 a *ᵥ (conjChange *ᵥ y) = conjChange *ᵥ y} = cayLineInf) := by
  constructor
  · intro hpole
    have denom : 1 + w0 ≠ 0 := by intro h; apply hpole; linarith
    ext y
    simp only [Set.mem_ofPred_eq, std_eigen_iff, cayLine, omul_smul_left]
    constructor
    · intro h
      ext i
      have entry := congrFun h.2 i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at entry ⊢
      field_simp
      nlinarith
    · intro h
      have aa : omul a (oct2 y) = ((1 + w0)⁻¹ * (a ⬝ᵥ a)) • oct1 y := by
        rw [h, omul_smul_right, oct_left_alt_proved, smul_smul]
      constructor
      · rw [aa]
        have scalar : w0 + (1 + w0)⁻¹ * (a ⬝ᵥ a) = 1 := by
          field_simp
          nlinarith [hw]
        rw [← add_smul, scalar, one_smul]
      · rw [h]
        have scalar : 1 - w0 * (1 + w0)⁻¹ = (1 + w0)⁻¹ := by field_simp; ring
        calc
          _ = (1 - w0 * (1 + w0)⁻¹) • omul (oconj a) (oct1 y) := by module
          _ = _ := by rw [scalar]
  · intro hpole
    have zero_a : a = 0 := dotProduct_self_eq_zero.mp (by nlinarith [hw])
    ext y
    simp only [Set.mem_ofPred_eq, std_eigen_iff, cayLineInf, hpole, zero_a,
      oconj_smul, zero_omul, neg_one_smul, add_zero]
    have conj_zero : oconj (0 : Vec 8) = 0 := by
      simpa only [zero_smul] using oconj_smul (0 : Vec 8) (0 : ℝ)
    rw [conj_zero, zero_omul]
    constructor
    · intro h
      ext i
      have entry := congrFun h.1 i
      simp only [Pi.neg_apply, Pi.zero_apply] at entry ⊢
      linarith
    · intro h
      simp [h]

theorem lem_7_1_a_skew_proved (K : Matrix (Fin 16) (Fin 16) ℝ)
    (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Estd x) :
    (∀ x : Vec 16, (K *ᵥ x) ⬝ᵥ x = 0) ∧ Kᵀ = -K := by
  have diagonal (x : Vec 16) : (K *ᵥ x) ⬝ᵥ x = 0 := by
    by_cases hx : x = 0
    · subst x; simp
    · exact (dotProduct_comm _ _).trans (hK x hx).2
  refine ⟨diagonal, ?_⟩
  ext i j
  have hii := diagonal (Pi.single i 1)
  have hjj := diagonal (Pi.single j 1)
  have sum := diagonal (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, Matrix.mulVec_single_one, dotProduct_add,
    add_dotProduct, dotProduct_single_one, Pi.add_apply, Matrix.col_apply] at hii hjj sum
  change K j i = -K i j
  linarith

end Osserman.Proofs.Lemma71Coordinates
