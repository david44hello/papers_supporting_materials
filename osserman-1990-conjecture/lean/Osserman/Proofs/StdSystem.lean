/-
Osserman/Proofs/StdSystem.lean — the standard symmetric Clifford system of nine matrices on ℝ^16 built from the
octonion swap maps (paper 013, §6): `sec6_std_system`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.OctonionLinear
import Osserman.Proofs.Threshold

namespace Osserman.Proofs.StdSystem

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.Threshold

def diagonalFun (x : Vec 16) : Vec 16 := octPair (oct1 x) (-oct2 x)

def swapFun (e : Vec 8) (x : Vec 16) : Vec 16 :=
  octPair (omul e (oconj (oct2 x))) (omul (oconj (oct1 x)) e)

lemma first_add (x y : Vec 16) : oct1 (x + y) = oct1 x + oct1 y := rfl
lemma second_add (x y : Vec 16) : oct2 (x + y) = oct2 x + oct2 y := rfl
lemma first_smul (x : Vec 16) (c : ℝ) : oct1 (c • x) = c • oct1 x := rfl
lemma second_smul (x : Vec 16) (c : ℝ) : oct2 (c • x) = c • oct2 x := rfl
lemma omul_neg_left (a b : Vec 8) : omul (-a) b = -omul a b := by
  simpa only [neg_one_smul] using omul_smul_left a b (-1)
lemma omul_neg_right (a b : Vec 8) : omul a (-b) = -omul a b := by
  simpa only [neg_one_smul] using omul_smul_right a b (-1)
lemma oconj_neg (a : Vec 8) : oconj (-a) = -oconj a := by
  simpa only [neg_one_smul] using oconj_smul a (-1)

lemma swap_add_e (e f : Vec 8) (x : Vec 16) : swapFun (e + f) x = swapFun e x + swapFun f x := by
  simp only [swapFun, omul_add_left, omul_add_right, pair_add]

lemma swap_add_x (e : Vec 8) (x y : Vec 16) : swapFun e (x + y) = swapFun e x + swapFun e y := by
  simp only [swapFun, first_add, second_add, oconj_add, omul_add_left, omul_add_right, pair_add]

lemma swap_smul_x (e : Vec 8) (c : ℝ) (x : Vec 16) : swapFun e (c • x) = c • swapFun e x := by
  simp only [swapFun, first_smul, second_smul, oconj_smul, omul_smul_left, omul_smul_right, pair_smul]

lemma diagonal_add (x y : Vec 16) : diagonalFun (x + y) = diagonalFun x + diagonalFun y := by
  simp only [diagonalFun, first_add, second_add, neg_add, pair_add]

lemma diagonal_smul (c : ℝ) (x : Vec 16) : diagonalFun (c • x) = c • diagonalFun x := by
  simp only [diagonalFun, first_smul, second_smul, smul_neg, pair_smul]

lemma swap_square (e : Vec 8) (x : Vec 16) : swapFun e (swapFun e x) = (e ⬝ᵥ e) • x := by
  simp only [swapFun, first_pair, second_pair, swap_square_left, swap_square_right]
  rw [← pair_smul, pair_parts]

lemma diagonal_square (x : Vec 16) : diagonalFun (diagonalFun x) = x := by
  simp only [diagonalFun, first_pair, second_pair, neg_neg, pair_parts]

lemma swap_adjoint_pair (e a b c d : Vec 8) :
    swapFun e (octPair a b) ⬝ᵥ octPair c d = octPair a b ⬝ᵥ swapFun e (octPair c d) := by
  simp only [swapFun, first_pair, second_pair, pair_dot]
  have second : omul (oconj a) e ⬝ᵥ d = a ⬝ᵥ omul e (oconj d) := by
    rw [dotProduct_comm, ← swap_adjoint e d a, dotProduct_comm]
  rw [swap_adjoint e b c, second, add_comm]

lemma swap_adjoint_fun (e : Vec 8) (x y : Vec 16) : swapFun e x ⬝ᵥ y = x ⬝ᵥ swapFun e y := by
  simpa only [pair_parts] using swap_adjoint_pair e (oct1 x) (oct2 x) (oct1 y) (oct2 y)

lemma diagonal_adjoint (x y : Vec 16) : diagonalFun x ⬝ᵥ y = x ⬝ᵥ diagonalFun y := by
  have pair (a b c d : Vec 8) : diagonalFun (octPair a b) ⬝ᵥ octPair c d =
      octPair a b ⬝ᵥ diagonalFun (octPair c d) := by
    simp only [diagonalFun, first_pair, second_pair, pair_dot, neg_dotProduct, dotProduct_neg]
  simpa only [pair_parts] using pair (oct1 x) (oct2 x) (oct1 y) (oct2 y)

lemma diagonal_swap (e : Vec 8) (x : Vec 16) :
    diagonalFun (swapFun e x) + swapFun e (diagonalFun x) = 0 := by
  simp only [diagonalFun, swapFun, first_pair, second_pair, oconj_neg, omul_neg_left, omul_neg_right]
  rw [pair_add]
  simp only [add_neg_cancel, neg_add_cancel]
  ext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
    simp only [octPair, Fin.append_left, Fin.append_right, Pi.zero_apply]

lemma swap_polarization (e f : Vec 8) (x : Vec 16) :
    swapFun e (swapFun f x) + swapFun f (swapFun e x) = (2 * (e ⬝ᵥ f)) • x := by
  have square := swap_square (e + f) x
  simp only [swap_add_e, swap_add_x, swap_square, normsq_add] at square
  ext i
  have entry := congrFun square i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at entry ⊢
  linarith

lemma stdFun_add (i : Fin 9) (x y : Vec 16) : stdSysFun i (x + y) = stdSysFun i x + stdSysFun i y := by
  unfold stdSysFun
  split_ifs
  · exact diagonal_add x y
  · exact swap_add_x _ x y

lemma stdFun_smul (i : Fin 9) (c : ℝ) (x : Vec 16) : stdSysFun i (c • x) = c • stdSysFun i x := by
  unfold stdSysFun
  split_ifs
  · exact diagonal_smul c x
  · exact swap_smul_x _ c x

def stdLinear (i : Fin 9) : Vec 16 →ₗ[ℝ] Vec 16 where
  toFun := stdSysFun i
  map_add' := stdFun_add i
  map_smul' := stdFun_smul i

lemma std_mulVec (i : Fin 9) (x : Vec 16) : stdSys i *ᵥ x = stdSysFun i x := by
  change LinearMap.toMatrix' (stdLinear i) *ᵥ x = stdLinear i x
  exact LinearMap.toMatrix'_mulVec _ _

lemma std_adjoint (i : Fin 9) (x y : Vec 16) : stdSysFun i x ⬝ᵥ y = x ⬝ᵥ stdSysFun i y := by
  unfold stdSysFun
  split_ifs
  · exact diagonal_adjoint x y
  · exact swap_adjoint_fun _ x y

lemma std_symmetric (i : Fin 9) : (stdSys i)ᵀ = stdSys i := by
  apply Matrix.IsSymm.ext
  intro r c
  have adjoint := std_adjoint i (Pi.single r 1) (Pi.single c 1)
  simp only [← std_mulVec, Matrix.mulVec_single_one, dotProduct_single_one,
    single_one_dotProduct, Matrix.col_apply] at adjoint
  exact adjoint

lemma std_clifford_fun (i j : Fin 9) (x : Vec 16) :
    stdSysFun i (stdSysFun j x) + stdSysFun j (stdSysFun i x) = if i = j then (2 : ℝ) • x else 0 := by
  by_cases iz : i.val = 0 <;> by_cases jz : j.val = 0
  · have equal : i = j := Fin.ext (iz.trans jz.symm)
    simp only [stdSysFun, dif_pos iz, dif_pos jz]
    change diagonalFun (diagonalFun x) + diagonalFun (diagonalFun x) = _
    rw [diagonal_square, ite_eq_left equal, two_smul]
  · have different : i ≠ j := fun equal => jz (equal ▸ iz)
    simp only [stdSysFun, dif_pos iz, dif_neg jz, ite_eq_right different]
    exact diagonal_swap _ x
  · have different : i ≠ j := fun equal => iz (equal.symm ▸ jz)
    simp only [stdSysFun, dif_neg iz, dif_pos jz, ite_eq_right different]
    rw [add_comm]
    exact diagonal_swap _ x
  · let a : Fin 8 := ⟨i.val - 1, by omega⟩
    let b : Fin 8 := ⟨j.val - 1, by omega⟩
    simp only [stdSysFun, dif_neg iz, dif_neg jz]
    change swapFun (octBasis a) (swapFun (octBasis b) x) +
      swapFun (octBasis b) (swapFun (octBasis a) x) = _
    rw [swap_polarization]
    by_cases equal : i = j
    · have ab : a = b := by subst j; rfl
      simp [octBasis, ab, equal]
    · have ab : a ≠ b := by intro same; have := congrArg Fin.val same; dsimp [a, b] at this; omega
      simp [octBasis, ab, equal]

theorem sec6_std_system_proved : (∀ i x, stdSys i *ᵥ x = stdSysFun i x) ∧ IsSymmCliffordSystem stdSys := by
  refine ⟨std_mulVec, std_symmetric, ?_⟩
  intro i j
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [std_mulVec]
  rw [std_clifford_fun]
  split_ifs <;> simp [Matrix.add_mulVec, Matrix.one_mulVec, two_smul]

end Osserman.Proofs.StdSystem
