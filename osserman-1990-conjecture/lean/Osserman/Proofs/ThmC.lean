/-
Osserman/Proofs/ThmC.lean — the final assembly of Theorem C (paper 013, l. 248-267) with Proposition 5.2 (row
`prop_5_2`, curried, verbatim) as an explicit premise: `thm_C_of_prop_5_2`. Row `thm_C` links to it once prop_5_2 is
proved. Uses the cited (A) (through sec3_plus_or_minus) and (Q) (through sec6_identify).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Spectral
import Osserman.Proofs.PlusMinus
import Osserman.Proofs.Sec5a
import Osserman.Proofs.OssTop
import Osserman.Proofs.CayleyIdentify
import Osserman.Proofs.CayleyCurvature
import Osserman.Proofs.Cayley

namespace Osserman.Proofs.ThmC

open Osserman Matrix Osserman.Proofs.Curv Osserman.Proofs.Spectral
open Osserman.Proofs.PlusMinus Osserman.Proofs.Sec5a Osserman.Proofs.OssTop
open Osserman.Proofs.CayleyIdentify Osserman.Proofs.CayleyCurvature Osserman.Proofs.Cayley

lemma operator_linear_combination (R A B : CurvTensor 16) (c d : ℝ)
    (hJ : ∀ x y : Vec 16, R.jacobi x *ᵥ y = c • (A.jacobi x *ᵥ y) + d • (B.jacobi x *ᵥ y)) :
    ∀ u v w, R.op u v w = c • A.op u v w + d • B.op u v w := by
  intro u v w
  rw [(sec2_determines_proved R).2, (sec2_determines_proved A).2, (sec2_determines_proved B).2]
  simp only [RAfun, Bpol, Matrix.smul_mulVec, Matrix.sub_mulVec, hJ]
  module

theorem thm_C_of_prop_5_2
    (h52 : ∀ (R : CurvTensor 16) (μ κ : ℝ), TwoRootHyp R μ κ →
      ∀ P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P →
      (∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
        ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) →
      IsFormCl8 (Amat R μ κ) ∨ IsFormCayley (Amat R μ κ))
    (R : CurvTensor 16)
    (h2 : ∃ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7) :
    ∃ μ κ : ℝ, κ ≠ 0 ∧ TwoRootHyp R μ κ ∧
      ∃ A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ, (∀ x, R.jacobi x = μ • Pi x + κ • A x) ∧
      ((IsFormCl7 A ∧ R.IsClifford) ∨ (IsFormCl8 A ∧ R.IsClifford) ∨
        (IsFormCayley A ∧ ∃ T ∈ Matrix.orthogonalGroup (Fin 16) ℝ,
          ∀ u v w, R.op u v w = (μ - κ / 3) • R1fun u v w + (κ / 3) • pullbackFun T RCayFun u v w)) := by
  obtain ⟨μ, κ, hypothesis⟩ := sec2_names_proved R h2
  have hJ (x : Vec 16) : R.jacobi x = μ • Pi x + κ • Amat R μ κ x := by
    rw [Amat, smul_smul, mul_inv_cancel₀ hypothesis.1, one_smul]
    module
  refine ⟨μ, κ, hypothesis.1, hypothesis, Amat R μ κ, hJ, ?_⟩
  rcases sec3_plus_or_minus_proved R μ κ hypothesis with plus | minus
  · obtain ⟨P, hP, hplus⟩ := plus
    have form := prop_5_1_proved R μ κ hypothesis P hP hplus
    exact Or.inl ⟨form, thm_C_clifford_cases_proved R μ κ _ hJ (Or.inl form)⟩
  · obtain ⟨P, hP, hminus⟩ := minus
    rcases h52 R μ κ hypothesis P hP hminus with form | form
    · exact Or.inr (Or.inl ⟨form, thm_C_clifford_cases_proved R μ κ _ hJ (Or.inr form)⟩)
    · obtain ⟨H, hH, hA⟩ := form
      obtain ⟨T, hT, identify⟩ := sec6_identify_proved H hH
      refine Or.inr (Or.inr ⟨⟨H, hH, hA⟩, T, hT, ?_⟩)
      obtain ⟨round, round_op⟩ := sec1_R1_curv_proved 16
      obtain ⟨cayley, cayley_op⟩ := sec1_Rcay_curv_proved
      obtain ⟨pulled, pulled_op⟩ := pullback_curv_proved cayley T hT
      have round_J (x y : Vec 16) : round.jacobi x *ᵥ y = Pi x *ᵥ y := by
        rw [jacobi_mulVec, round_op, sec1_jacobi_R1_proved]
      have pulled_R (u v w : Vec 16) : pulled.op u v w = pullbackFun T RCayFun u v w := by
        rw [pulled_op]
        unfold pullbackFun
        change Tᵀ *ᵥ cayley.op (T *ᵥ u) (T *ᵥ v) (T *ᵥ w) =
          Tᵀ *ᵥ RCayFun (T *ᵥ u) (T *ᵥ v) (T *ᵥ w)
        rw [cayley_op]
      have pulled_J (x y : Vec 16) : pulled.jacobi x *ᵥ y = pullbackFun T RCayFun y x x := by
        rw [jacobi_mulVec, pulled_R]
      have combination : ∀ x y : Vec 16, R.jacobi x *ᵥ y =
          (μ - κ / 3) • (round.jacobi x *ᵥ y) + (κ / 3) • (pulled.jacobi x *ᵥ y) := by
        intro x y
        rw [hJ, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hA, round_J, pulled_J]
        have scaled : κ • (Acay H x *ᵥ y) = (κ / 3) • ((3 : ℝ) • (Acay H x *ᵥ y)) := by module
        rw [scaled, identify]
        module
      intro u v w
      rw [operator_linear_combination R round pulled (μ - κ / 3) (κ / 3) combination, round_op, pulled_R]

end Osserman.Proofs.ThmC
