/-
ThmEClosed.lean — Theorem E interfaces with the proved rank-one curvature construction instantiated.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.ThmE
import Osserman.Proofs.Rem72a

namespace Osserman.Proofs.ThmEClosed

open Osserman Matrix

theorem thm_E_tilde_proved
    (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) :
    ∃ Rt : CurvTensor 16, (∀ u v w, Rt.op u v w = R.op u v w - (ev 2 - ev 1) • ∑ a, RJfun (J a) u v w) ∧
      (∀ x, Rt.jacobi x = R.jacobi x - (ev 2 - ev 1) • ∑ a, jfam (J a) x) ∧ Rt.IsOsserman ∧
      (∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x (ev 0) = m 0 ∧ Rt.redMult x (ev 1) = m 1 + m 2) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) (ev 1) :=
  Osserman.Proofs.ThmEMerge.thm_E_tilde_of_RJ_curv Osserman.Proofs.Rem72a.RJ_curv_proved R m ev J h

theorem thm_E_intermediate_osserman_proved
    (R : CurvTensor 16) (hO : R.IsOsserman) {t : ℕ}
    (J : Fin t → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J) (τ : ℝ)
    (hfr : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (R.jacobiMap x) τ) (s : Fin t → ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - ∑ a, s a • RJfun (J a) u v w) ∧ R'.IsOsserman :=
  Osserman.Proofs.ThmETransfer.thm_E_intermediate_osserman_of_RJ_curv Osserman.Proofs.Rem72a.RJ_curv_proved R hO J hJ τ hfr s

theorem thm_E_intermediate_pattern_proved
    (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) (h2 : m 2 = 2) (a : Fin (m 2)) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - (ev 2 - ev 1) • RJfun (J a) u v w) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        R'.redMult x (ev 0) = m 0 ∧ R'.redMult x (ev 1) = m 1 + 1 ∧ R'.redMult x (ev 2) = 1 :=
  Osserman.Proofs.ThmEMerge.thm_E_intermediate_pattern_of_RJ_curv Osserman.Proofs.Rem72a.RJ_curv_proved R m ev J h h2 a

theorem thm_E_restore_of_lem_nik_3_2_1
    (hNik : ∀ (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
      (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
      (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford), R.IsClifford)
    (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) (Rt : CurvTensor 16)
    (hRt : ∀ u v w, Rt.op u v w = R.op u v w - (ev 2 - ev 1) • ∑ a, RJfun (J a) u v w) (hC : Rt.IsClifford) :
    R.IsClifford :=
  Osserman.Proofs.ThmERestore.thm_E_restore_of_lem_nik_3_2_1 hNik Osserman.Proofs.Rem72a.RJ_curv_proved R m ev J h Rt hRt hC

theorem thm_E_of_lem_nik_3_2_1
    (hNik : ∀ (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
      (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
      (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford), R.IsClifford)
    (R : CurvTensor 16)
    (h3 : HasPattern R ![7, 7, 1] ∨ HasPattern R ![8, 6, 1] ∨ HasPattern R ![8, 5, 2] ∨ HasPattern R ![7, 6, 2]) :
    R.IsClifford :=
  Osserman.Proofs.ThmE.thm_E_of_lem_nik_3_2_1 hNik Osserman.Proofs.Rem72a.RJ_curv_proved R h3

end Osserman.Proofs.ThmEClosed

