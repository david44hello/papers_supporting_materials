/-
Osserman/Proofs/S84Move.lean — §8.4 of paper 013, the linear field and the move: rows s8_4_linear_field, s8_4_move
(statements copied verbatim from Osserman/Paper/Statements8.lean).
Premise rows (leading arguments with their exact types): lem_8_2_div_q, s8_tc_same_eigen, s8_tc_outcome,
s8_spectral_identity, s8_move_eigenfield.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. Equal signs: every field is divisible by `q` (`s8_4_same_sign`), and Lemma 8.2's first step makes `P_3 = qJx`
with `J` skew orthogonal. Opposite signs: the three-column hypotheses hold (`s8_4_three_col`); its outcome is a column
`qJx` (an eigenfield of `μ` or `σ`) or a combination `c_1P_1 + c_2P_2 = qJx` of the two double-eigenvalue fields,
which is an eigenfield of `μ` (`s8_tc_same_eigen`). Moving the field into `0` (`s8_move_eigenfield`) gives the table.
-/
import Osserman.Proofs.S84Fields
import Osserman.Proofs.S83Move

namespace Osserman.Proofs.S84

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.S83

/-- The type of row `s8_tc_same_eigen`. -/
abbrev SameEigenHyp : Prop :=
  ∀ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (_h : ThreeColHyp R μ P wt) (_hμ : μ 0 = μ 1) (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ)
    (_hc : c1 ^ 2 + c2 ^ 2 = 1)
    (_hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x)),
    IsEigenfield R (μ 0) (linP J)

/-- The type of row `s8_tc_outcome`. -/
abbrev OutcomeHyp : Prop :=
  ∀ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (_h : ThreeColHyp R μ P wt) (_hP2 : CubicIdentities (P 2)),
    (∃ (i : Fin 3) (J : Matrix (Fin 16) (Fin 16) ℝ), Jᵀ = -J ∧ Jᵀ * J = 1 ∧
        (∀ x : Vec 16, evalField (P i) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ i) (linP J)) ∨
      ∃ (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ), c1 ^ 2 + c2 ^ 2 = 1 ∧ Jᵀ = -J ∧ Jᵀ * J = 1 ∧
        ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x)

/-- Row `s8_4_linear_field`. -/
theorem s8_4_linear_field_proved (hdiv : DivQHyp) (hSame : SameEigenHyp) (hOut : OutcomeHyp) (hSpec : SpecIdHyp)
    (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec84Data R M N ev P) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      (IsEigenfield R (ev 3) (linP J) ∨ IsEigenfield R (ev 2) (linP J)) := by
  have hR := h.2.1
  have h0 := h.2.2.1
  have hne : (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (mul_ne_zero ?_ ?_)
    · exact fun e => absurd (hR.1 (e.trans h0.symm)) (by decide)
    · exact fun e => absurd (hR.1 (sub_eq_zero.mp e)) (by decide)
    · exact fun e => absurd (hR.1 (e.trans h0.symm)) (by decide)
    · exact fun e => absurd (hR.1 (sub_eq_zero.mp e)) (by decide)
  rcases lt_or_gt_of_ne hne with hs | hs
  · obtain ⟨ε, -, hTC⟩ := s8_4_three_col_proved hSpec R M N ev P h hs
    rcases hOut R _ P _ hTC h.2.2.2.2.2.2.2.2 with ⟨i, J, hJs, hJo, -, hJe⟩ | ⟨c1, c2, J, hc, hJs, hJo, hJ⟩
    · fin_cases i
      · exact ⟨J, hJs, hJo, Or.inr (by simpa using hJe)⟩
      · exact ⟨J, hJs, hJo, Or.inr (by simpa using hJe)⟩
      · exact ⟨J, hJs, hJo, Or.inl (by simpa using hJe)⟩
    · exact ⟨J, hJs, hJo, Or.inr (by simpa using hSame R _ P _ hTC rfl c1 c2 J hc hJ)⟩
  · have hq := s8_4_same_sign_proved hSpec R M N ev P h hs
    obtain ⟨-, -, -, h3, -, -, -, he2, hC2⟩ := h
    obtain ⟨J, hJP, -, hJs, hJo⟩ := hdiv (P 2) (h3 2) hC2 (hq 2)
    exact ⟨J, hJs, hJo, Or.inl (eigenfield_linP he2 J (evalField_of_eq hJP))⟩

/-- Row `s8_4_move`. -/
theorem s8_4_move_proved (hMove : MoveHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) :
    (IsEigenfield R (ev 3) (linP J) → ∃ R' : CurvTensor 16,
        (∀ u v z, R'.op u v z = R.op u v z - ev 3 • RJfun J u v z) ∧ PatternEv R' ![M + 1, N, 2] ![0, ev 1, ev 2]) ∧
      (IsEigenfield R (ev 2) (linP J) → ∃ R' : CurvTensor 16,
        (∀ u v z, R'.op u v z = R.op u v z - ev 2 • RJfun J u v z) ∧
          PatternEv R' ![M + 1, N, 1, 1] ![0, ev 1, ev 2, ev 3]) := by
  obtain ⟨hMN, hR, h0, -⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts hMN
  constructor
  · intro hJe
    obtain ⟨R', hop, -, -, hm⟩ := hMove R _ ev hR hsum J hJs hJo 3 0 (by decide) hJe
    refine ⟨R', by simpa [h0] using hop,
      ⟨inj_comp hR.1 ![0, 1, 2] (by decide) (by funext i; fin_cases i <;> simp [h0]), fun x hx i => ?_⟩⟩
    obtain ⟨-, b, c⟩ := hm x hx
    fin_cases i
    · simpa [h0] using b
    · simpa using c 1 (by decide) (by decide)
    · simpa using c 2 (by decide) (by decide)
  · intro hJe
    obtain ⟨R', hop, -, -, hm⟩ := hMove R _ ev hR hsum J hJs hJo 2 0 (by decide) hJe
    refine ⟨R', by simpa [h0] using hop,
      ⟨inj_comp hR.1 ![0, 1, 2, 3] (by decide) (by funext i; fin_cases i <;> simp [h0]), fun x hx i => ?_⟩⟩
    obtain ⟨a, b, c⟩ := hm x hx
    fin_cases i
    · simpa [h0] using b
    · simpa using c 1 (by decide) (by decide)
    · simpa using a
    · simpa using c 3 (by decide) (by decide)

end Osserman.Proofs.S84
