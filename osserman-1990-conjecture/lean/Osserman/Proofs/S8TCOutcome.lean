/-
S8TCOutcome.lean — assembly of the three-column alternative, paper 013, Section 8.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.S8TCUnit
import Osserman.Proofs.S8TCFactor

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial

theorem s8_tc_outcome_of_lem_8_2
    (hLemma : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (_hP3 : ∀ j, (P j).IsHomogeneous 3)
      (_hP : CubicIdentities P) (_hdiv : ∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)),
      ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧ ∀ x : Vec 16,
        evalField P x = (x ⬝ᵥ x) • (J *ᵥ x))
    (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hP2 : CubicIdentities (P 2)) :
    (∃ (i : Fin 3) (J : Matrix (Fin 16) (Fin 16) ℝ), Jᵀ = -J ∧ Jᵀ * J = 1 ∧
        (∀ x : Vec 16, evalField (P i) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ i) (linP J)) ∨
      ∃ (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ), c1 ^ 2 + c2 ^ 2 = 1 ∧ Jᵀ = -J ∧ Jᵀ * J = 1 ∧
        ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  classical
  by_cases zero : ∃ i, tcImg wt P i = 0
  · obtain ⟨i, hi⟩ := zero
    obtain ⟨J, skew, orthogonal, image, eigen⟩ := s8_tc_zero_column_proved R μ P wt h i hi
    exact Or.inl ⟨i, J, skew, orthogonal, image, eigen⟩
  · have nonzero (i : Fin 3) : tcImg wt P i ≠ 0 := fun equal => zero ⟨i, equal⟩
    let hQ := Osserman.Proofs.QPrime.s8_q_prime_proved
    obtain ⟨u0, u1, v, primitive, h0, h1⟩ := s8_tc_primitive_of_s8_q_prime hQ R μ P wt h nonzero
    obtain ⟨u3, h2, _⟩ := s8_tc_third_of_s8_q_prime hQ R μ P wt h u0 u1 v primitive h0 h1
    by_cases unit : IsUnit u3
    · obtain ⟨k0, k1, hk0, hk1⟩ := s8_tc_unit_const_proved R μ P wt h u0 u1 u3 v h0 h1 h2 unit
      exact Or.inr (s8_tc_lincomb_proved R μ P wt h k0 k1 hk0 hk1 (nonzero 2))
    · obtain ⟨J, skew, orthogonal, image, eigen⟩ :=
        s8_tc_nonunit_of_lem_8_2 hLemma R μ P wt h hP2 u3 v h2 unit
      exact Or.inl ⟨2, J, skew, orthogonal, image, eigen⟩

end Osserman.Proofs.S8TC
