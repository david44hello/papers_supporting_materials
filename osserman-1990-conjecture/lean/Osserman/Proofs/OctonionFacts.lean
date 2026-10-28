/-
Osserman/Proofs/OctonionFacts.lean — pure octonion identities used in Lemma 7.1 (paper 013, l. 701-736):
`oct_left_alt`, `oct_no_zero_divisors`, `oct_adjoint`, `oct_conj_mul`, `oct_norm_mul`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.OctonionLinear
import Osserman.Defs.ThreeRoot

namespace Osserman.Proofs.OctonionFacts

open Osserman Matrix Osserman.Proofs.OctonionLinear

lemma oconj_invol (a : Vec 8) : oconj (oconj a) = a := by
  ext i
  fin_cases i <;> simp [oconj, vecOfOct, octConj, octOfVec]

lemma oconj_dot (a b : Vec 8) : oconj a ⬝ᵥ oconj b = a ⬝ᵥ b := by
  norm_num [dotProduct, Fin.sum_univ_succ, oconj, vecOfOct, octConj, octOfVec]

lemma oconj_move (a b : Vec 8) : oconj a ⬝ᵥ b = a ⬝ᵥ oconj b := by
  have equal := oconj_dot a (oconj b)
  rwa [oconj_invol] at equal

theorem oct_conj_mul_proved (a b : Vec 8) : oconj (omul a b) = omul (oconj b) (oconj a) := by
  ext i
  fin_cases i <;> simp [omul, oconj, vecOfOct, octConj, octMul, octOfVec] <;> ring

theorem oct_left_alt_proved (a u : Vec 8) : omul a (omul (oconj a) u) = (a ⬝ᵥ a) • u := by
  have equal := swap_square_left a u
  rw [oct_conj_mul_proved, oconj_invol] at equal
  exact equal

theorem oct_adjoint_proved (ω u r : Vec 8) : omul ω u ⬝ᵥ r = u ⬝ᵥ omul (oconj ω) r := by
  have equal := swap_adjoint ω (oconj u) r
  rw [oconj_invol, oconj_move, oct_conj_mul_proved, oconj_invol] at equal
  exact equal

theorem oct_norm_mul_proved (a b : Vec 8) : omul a b ⬝ᵥ omul a b = (a ⬝ᵥ a) * (b ⬝ᵥ b) := by
  rw [oct_adjoint_proved]
  have compose := oct_left_alt_proved (oconj a) b
  rw [oconj_invol, oconj_dot] at compose
  rw [compose, dotProduct_smul, smul_eq_mul]

theorem oct_no_zero_divisors_proved (a b : Vec 8) (h : omul a b = 0) : a = 0 ∨ b = 0 := by
  have norms := oct_norm_mul_proved a b
  rw [h, zero_dotProduct] at norms
  rcases mul_eq_zero.mp norms.symm with left | right
  · exact Or.inl (dotProduct_self_eq_zero.mp left)
  · exact Or.inr (dotProduct_self_eq_zero.mp right)

lemma omul_one (a : Vec 8) : omul a oone = a := by
  ext i
  fin_cases i <;> norm_num [omul, oone, vecOfOct, octMul, octOfVec, Pi.single_apply]

lemma one_omul (a : Vec 8) : omul oone a = a := by
  ext i
  fin_cases i <;> norm_num [omul, oone, vecOfOct, octMul, octOfVec, Pi.single_apply]

lemma omul_zero (a : Vec 8) : omul a 0 = 0 := by
  have equal := omul_smul_right a a 0
  simpa only [zero_smul] using equal

lemma zero_omul (a : Vec 8) : omul 0 a = 0 := by
  have equal := omul_smul_left a a 0
  simpa only [zero_smul] using equal

end Osserman.Proofs.OctonionFacts
