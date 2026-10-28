/-
Osserman/Proofs/CayleyIdentify.lean — every Cayley family is an orthogonal transport of the standard one, so the
Cayley case of Theorem C is aR_1 + bT^*R_Cay (paper 013, §6): `sec6_identify` (uses the cited (Q) only).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.CayleyJacobi
import Osserman.Proofs.Cayley
import Osserman.Proofs.Poly
import Osserman.Cited.Isoparametric

namespace Osserman.Proofs.CayleyIdentify

open Osserman Matrix Osserman.Proofs.Threshold Osserman.Proofs.StdSystem
open Osserman.Proofs.CayleyJacobi Osserman.Proofs.Cayley Osserman.Proofs.Poly

lemma orthogonal_dot (U : Matrix (Fin 16) (Fin 16) ℝ) (hU : Uᵀ * U = 1) (x y : Vec 16) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
  rw [mulVec_dotProduct_eq, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

lemma orthogonal_action (U : Matrix (Fin 16) (Fin 16) ℝ) (hU : Uᵀ * U = 1) (x : Vec 16) :
    Uᵀ *ᵥ (U *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

lemma Pi_transport (U : Matrix (Fin 16) (Fin 16) ℝ) (hU : Uᵀ * U = 1) (x y : Vec 16) :
    Uᵀ *ᵥ (Pi (U *ᵥ x) *ᵥ (U *ᵥ y)) = Pi x *ᵥ y := by
  simp only [Osserman.Pi, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    outer_mulVec_real, Matrix.mulVec_sub, Matrix.mulVec_smul,
    orthogonal_dot U hU, orthogonal_action U hU]

lemma Acay_transport (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ)
    (U : Matrix (Fin 16) (Fin 16) ℝ) (hU : Uᵀ * U = 1) (x y : Vec 16) :
    Uᵀ *ᵥ (Acay S (U *ᵥ x) *ᵥ (U *ᵥ y)) = Acay (fun i => Uᵀ * S i * U) x *ᵥ y := by
  have coefficient (i : Fin 9) :
      (U *ᵥ x) ⬝ᵥ (S i *ᵥ (U *ᵥ x)) = x ⬝ᵥ ((Uᵀ * S i * U) *ᵥ x) := by
    rw [mulVec_dotProduct_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have action (i : Fin 9) : Uᵀ *ᵥ (S i *ᵥ (U *ᵥ y)) = (Uᵀ * S i * U) *ᵥ y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [Acay, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, outer_mulVec_real, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_add, Matrix.sum_mulVec, Matrix.mulVec_sum,
    orthogonal_dot U hU, orthogonal_action U hU]
  simp_rw [coefficient, action]

theorem sec6_identify_proved (H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hH : IsSymmCliffordSystem H) :
    ∃ T ∈ Matrix.orthogonalGroup (Fin 16) ℝ, ∀ x y : Vec 16,
      (3 : ℝ) • (Acay H x *ᵥ y) = pullbackFun T RCayFun y x x - Pi x *ᵥ y := by
  obtain ⟨T, hT, sign, hsign, first, rest⟩ :=
    Osserman.Cited.symm_clifford9_unique stdSys H sec6_std_system_proved.2 hH
  let C := fun i : Fin 9 => T * stdSys i * Tᵀ
  have family : Acay H = Acay C := by
    rcases hsign with positive | negative
    · subst sign
      have equal : H = C := by
        funext i
        by_cases zero : i = 0
        · subst i
          simpa only [one_smul] using first
        · exact rest i zero
      rw [equal]
    · subst sign
      have equal : H = Function.update C 0 (-C 0) := by
        funext i
        by_cases zero : i = 0
        · subst i
          simpa only [Function.update_self, neg_one_smul] using first
        · rw [Function.update_of_ne zero]
          exact rest i zero
      rw [equal, sec6_sign_change_proved]
  have hTT : T * Tᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 16) ℝ).mp hT
  have hTT' : Tᵀ * T = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 16) ℝ).mp hT
  have hTranspose : Tᵀ ∈ Matrix.orthogonalGroup (Fin 16) ℝ :=
    (Matrix.mem_orthogonalGroup_iff (Fin 16) ℝ).mpr (by simpa only [Matrix.transpose_transpose] using hTT')
  refine ⟨Tᵀ, hTranspose, ?_⟩
  intro x y
  rw [family]
  unfold pullbackFun
  rw [RCay_jacobi, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hU : (Tᵀ)ᵀ * Tᵀ = 1 := by simpa only [Matrix.transpose_transpose] using hTT
  rw [Pi_transport Tᵀ hU, Acay_transport stdSys Tᵀ hU]
  simp only [Matrix.transpose_transpose]
  change (3 : ℝ) • (Acay C x *ᵥ y) = Pi x *ᵥ y + (3 : ℝ) • (Acay C x *ᵥ y) - Pi x *ᵥ y
  module

end Osserman.Proofs.CayleyIdentify
