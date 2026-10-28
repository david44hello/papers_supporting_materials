/-
Osserman/Proofs/OctonionLinear.lean — formula-level linearity and adjoint identities for octonion multiplication
(paper 013, §6, l. 648-653; a foundation for `sec6_std_system`, no row of its own).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Cayley

namespace Osserman.Proofs.OctonionLinear

open Osserman Matrix

lemma omul_add_left (a b c : Vec 8) : omul (a + b) c = omul a c + omul b c := by
  ext i
  fin_cases i <;> simp [omul, vecOfOct, octMul, octOfVec] <;> ring

lemma omul_add_right (a b c : Vec 8) : omul a (b + c) = omul a b + omul a c := by
  ext i
  fin_cases i <;> simp [omul, vecOfOct, octMul, octOfVec] <;> ring

lemma omul_smul_left (a b : Vec 8) (c : ℝ) : omul (c • a) b = c • omul a b := by
  ext i
  fin_cases i <;> simp [omul, vecOfOct, octMul, octOfVec] <;> ring

lemma omul_smul_right (a b : Vec 8) (c : ℝ) : omul a (c • b) = c • omul a b := by
  ext i
  fin_cases i <;> simp [omul, vecOfOct, octMul, octOfVec] <;> ring

lemma oconj_add (a b : Vec 8) : oconj (a + b) = oconj a + oconj b := by
  ext i
  fin_cases i <;> simp [oconj, vecOfOct, octConj, octOfVec] <;> ring

lemma oconj_smul (a : Vec 8) (c : ℝ) : oconj (c • a) = c • oconj a := by
  ext i
  fin_cases i <;> simp [oconj, vecOfOct, octConj, octOfVec]

lemma pair_parts (x : Vec 16) : octPair (oct1 x) (oct2 x) = x := by
  ext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
    simp only [octPair, oct1, oct2, Fin.append_left, Fin.append_right]

@[simp] lemma first_pair (a b : Vec 8) : oct1 (octPair a b) = a := by
  ext i
  simp [octPair, oct1]

@[simp] lemma second_pair (a b : Vec 8) : oct2 (octPair a b) = b := by
  ext i
  simp only [octPair, oct2, Fin.append_right]

lemma pair_dot (a b c d : Vec 8) : octPair a b ⬝ᵥ octPair c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp only [octPair, dotProduct]
  rw [Fin.sum_univ_add (a := 8) (b := 8)]
  simp only [Fin.append_left, Fin.append_right]

lemma pair_add (a b c d : Vec 8) : octPair a b + octPair c d = octPair (a + c) (b + d) := by
  ext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
    simp only [octPair, Pi.add_apply, Fin.append_left, Fin.append_right]

lemma pair_smul (a b : Vec 8) (c : ℝ) : c • octPair a b = octPair (c • a) (c • b) := by
  ext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
    simp only [octPair, Pi.smul_apply, Fin.append_left, Fin.append_right]

set_option maxHeartbeats 800000 in
lemma swap_adjoint (e b c : Vec 8) : omul e (oconj b) ⬝ᵥ c = b ⬝ᵥ omul (oconj c) e := by
  norm_num [dotProduct, Fin.sum_univ_succ, omul, oconj, vecOfOct, octConj, octMul, octOfVec]
  ring

set_option maxHeartbeats 800000 in
lemma swap_square_left (e a : Vec 8) :
    omul e (oconj (omul (oconj a) e)) = (e ⬝ᵥ e) • a := by
  ext i
  fin_cases i <;> norm_num [dotProduct, Fin.sum_univ_succ, omul, oconj, vecOfOct,
    octConj, octMul, octOfVec] <;> ring

set_option maxHeartbeats 800000 in
lemma swap_square_right (e b : Vec 8) :
    omul (oconj (omul e (oconj b))) e = (e ⬝ᵥ e) • b := by
  ext i
  fin_cases i <;> norm_num [dotProduct, Fin.sum_univ_succ, omul, oconj, vecOfOct,
    octConj, octMul, octOfVec] <;> ring

end Osserman.Proofs.OctonionLinear
