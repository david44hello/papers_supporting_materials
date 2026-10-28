/-
ThmE.lean — Theorem E of paper 013, lines 307–311 and 740–784.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmERestore
import Osserman.Proofs.ThmECayley

namespace Osserman.Proofs.ThmE

open Osserman Matrix Osserman.Proofs.ThmEFrames Osserman.Proofs.ThmEElementary
open Osserman.Proofs.ThmEFrameConstruction Osserman.Proofs.ThmEProjection
open Osserman.Proofs.ThmEMerge Osserman.Proofs.ThmERestore Osserman.Proofs.ThmECayley

theorem thm_E_of_lem_nik_3_2_1
    (hNik : ∀ (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
      (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
      (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford), R.IsClifford)
    (hRJ : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J),
      (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ B : CurvTensor n, (∀ u v w, B.op u v w = RJfun J u v w) ∧ ∀ x, B.jacobi x = jfam J x)
    (R : CurvTensor 16)
    (h3 : HasPattern R ![7, 7, 1] ∨ HasPattern R ![8, 6, 1] ∨ HasPattern R ![8, 5, 2] ∨ HasPattern R ![7, 6, 2]) :
    R.IsClifford := by
  obtain ⟨m, hm, ev, injective, pattern⟩ :
      ∃ m : Fin 3 → ℕ, IsThmEPattern m ∧
        ∃ ev : Fin 3 → ℝ, Function.Injective ev ∧
          ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i := by
    rcases h3 with first | second | third | fourth
    · exact ⟨![7, 7, 1], Or.inl rfl, first⟩
    · exact ⟨![8, 6, 1], Or.inr (Or.inl rfl), second⟩
    · exact ⟨![8, 5, 2], Or.inr (Or.inr (Or.inl rfl)), third⟩
    · exact ⟨![7, 6, 2], Or.inr (Or.inr (Or.inr rfl)), fourth⟩
  obtain ⟨J, frame⟩ := thm_E_frame_proved R m hm ev injective pattern
  obtain ⟨Rt, operator, jacobi, osserman, multiplicity, fields⟩ := thm_E_tilde_of_RJ_curv hRJ R m ev J frame
  have hJ := frame.2.2.2.1
  have positive : 0 < m 2 := by have smallest := (thm_E_smallest_proved m hm).1; omega
  let a : Fin (m 2) := ⟨0, positive⟩
  have nonzero : J a ≠ 0 := by
    intro equal
    let x0 : Vec 16 := Pi.single 0 1
    have unit : x0 ⬝ᵥ x0 = 1 := by simp [x0]
    have norm := (clifford_frame J hJ x0 unit).1 a a
    rw [equal, Matrix.zero_mulVec, zero_dotProduct] at norm
    norm_num at norm
  have clifford := thm_E_tilde_clifford_proved Rt (ev 0) (ev 1) (injective.ne (by decide))
    (m 0) (m 1 + m 2) (thm_E_merge_proved m hm) multiplicity
    (J a) (hJ.1 a) nonzero (fun x hx => fields x hx a)
  exact thm_E_restore_of_lem_nik_3_2_1 hNik hRJ R m ev J frame Rt operator clifford

end Osserman.Proofs.ThmE

