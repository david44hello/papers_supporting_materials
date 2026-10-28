/-
Osserman/Proofs/S84End.lean — §8.4 of paper 013: the endpoints are Clifford, the original tensor is restored (rows
s8_4_endpoints_clifford, s8_4_clifford, s8_4_pattern_clifford; statements copied verbatim from
Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. The endpoints: `(8,5,2)` by Theorem E (`thm_E_of_lem_nik_3_2_1`), `(8,5,1,1)` by §8.3
(`s8_3_pattern_clifford`), `(9,4,2)` and `(9,4,1,1)` by [Nik2006, Proposition 2.1] (`s8_prop21_uses`). The data of §8.4
give a skew orthogonal linear eigenfield `J` of `σ` or of `μ` (`s8_4_linear_field`); moving it into `0`
(`s8_4_move`) gives an endpoint `R' = R - cR_J` with `c = σ` or `μ` (nonzero), which is Clifford, and
[Nik2006, Lemma 3.2(1)] (`lem_nik_3_2_1`) restores `R`. Theorem F for `(7,5,2,1)`, `(8,4,2,1)`: shift the eigenvalue of
multiplicity `M` to `0` (`s8_shift_to_zero`), take the fields (`s8_4_fields`).
-/
import Osserman.Proofs.S83Opp2
import Osserman.Proofs.S84Move
import Osserman.Proofs.ThmEClosed

namespace Osserman.Proofs.S84

open Osserman Matrix Osserman.Proofs.S83

/-- Row `s8_4_endpoints_clifford`. -/
theorem s8_4_endpoints_clifford_proved (hQ : QPrimeHyp) (hCub : CubicIdHyp) (hDiv : DivQHyp) (hSpec : SpecIdHyp)
    (hMove : MoveHyp) (R' : CurvTensor 16)
    (hpat : HasPattern R' ![8, 5, 2] ∨ HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 2] ∨
      HasPattern R' ![9, 4, 1, 1]) :
    R'.IsClifford := by
  rcases hpat with h | h | h | h
  · exact ThmEClosed.thm_E_of_lem_nik_3_2_1 Rem72c.lem_nik_3_2_1_proved R' (Or.inr (Or.inr (Or.inl h)))
  · exact s8_3_pattern_clifford_proved hQ hCub hDiv hSpec hMove R' (Or.inr h)
  · exact s8_prop21_uses_proved R' (Or.inr (Or.inr (Or.inl h)))
  · exact s8_prop21_uses_proved R' (Or.inr (Or.inr (Or.inr h)))

/-- Row `s8_4_clifford`. -/
theorem s8_4_clifford_proved (hQ : QPrimeHyp) (hCub : CubicIdHyp) (hDiv : DivQHyp) (hSame : SameEigenHyp)
    (hOut : OutcomeHyp) (hSpec : SpecIdHyp) (hMove : MoveHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec84Data R M N ev P) : R.IsClifford := by
  have hinj := h.2.1.1
  have h0 := h.2.2.1
  have hne (i : Fin 4) (hi : i ≠ 0) : ev i ≠ 0 := fun e => hi (hinj (e.trans h0.symm))
  have hsum : ∑ i, (![M, N, 2, 1] : Fin 4 → ℕ) i + 1 = 16 ∧ ∑ i, (![M + 1, N, 2] : Fin 3 → ℕ) i + 1 = 16 ∧
      ∑ i, (![M + 1, N, 1, 1] : Fin 4 → ℕ) i + 1 = 16 := by
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Fin.sum_univ_succ]
  have hO := pattern_osserman hsum.1 h.2.1
  have ends := s8_4_endpoints_clifford_proved hQ hCub hDiv hSpec hMove
  obtain ⟨J, hJs, hJo, hJe⟩ := s8_4_linear_field_proved hDiv hSame hOut hSpec R M N ev P h
  obtain ⟨move3, move2⟩ := s8_4_move_proved hMove R M N ev P h J hJs hJo
  rcases hJe with e3 | e2
  · obtain ⟨R', hR', hpat'⟩ := move3 e3
    have hC' : R'.IsClifford := by
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ends R' (Or.inl ⟨_, hpat'⟩)
      · exact ends R' (Or.inr (Or.inr (Or.inl ⟨_, hpat'⟩)))
    exact Rem72c.lem_nik_3_2_1_proved R R' J hJs hJo _ (hne 3 (by decide)) hR' hO
      (pattern_osserman hsum.2.1 hpat') hC'
  · obtain ⟨R', hR', hpat'⟩ := move2 e2
    have hC' : R'.IsClifford := by
      rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ends R' (Or.inr (Or.inl ⟨_, hpat'⟩))
      · exact ends R' (Or.inr (Or.inr (Or.inr ⟨_, hpat'⟩)))
    exact Rem72c.lem_nik_3_2_1_proved R R' J hJs hJo _ (hne 2 (by decide)) hR' hO
      (pattern_osserman hsum.2.2 hpat') hC'

/-- Row `s8_4_pattern_clifford`. -/
theorem s8_4_pattern_clifford_proved (hQ : QPrimeHyp) (hCub : CubicIdHyp) (hDiv : DivQHyp) (hSame : SameEigenHyp)
    (hOut : OutcomeHyp) (hSpec : SpecIdHyp) (hMove : MoveHyp) (R : CurvTensor 16)
    (h : HasPattern R ![7, 5, 2, 1] ∨ HasPattern R ![8, 4, 2, 1]) : R.IsClifford := by
  obtain ⟨M, N, hMN, ev, hR⟩ : ∃ M N : ℕ, ((M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) ∧ HasPattern R ![M, N, 2, 1] := by
    rcases h with h | h
    · exact ⟨7, 5, Or.inl ⟨rfl, rfl⟩, h⟩
    · exact ⟨8, 4, Or.inr ⟨rfl, rfl⟩, h⟩
  obtain ⟨R0, -, -, hR0, -, -, hiff⟩ := S8TC.s8_shift_to_zero_proved R _ ev hR 0
  obtain ⟨P, hP⟩ := s8_4_fields_proved hCub R0 M N hMN _ hR0 (sub_self _)
  exact hiff.mp (s8_4_clifford_proved hQ hCub hDiv hSame hOut hSpec hMove R0 M N _ P hP)

end Osserman.Proofs.S84
