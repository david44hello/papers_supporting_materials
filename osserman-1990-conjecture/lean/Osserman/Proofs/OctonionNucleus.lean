/-
Osserman/Proofs/OctonionNucleus.lean — the right nucleus of the octonions is ℝ, and distinct Cayley lines meet only
in 0 (paper 013, Lemma 7.1, l. 711-721): `oct_right_nucleus`, `cayley_lines_meet_zero`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.OctonionFacts

namespace Osserman.Proofs.OctonionNucleus

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts

theorem oct_right_nucleus_proved (c : Vec 8) :
    (∀ ω u : Vec 8, omul (omul ω u) c = omul ω (omul u c)) ↔ ∃ r : ℝ, c = r • oone := by
  constructor
  · intro h
    have eq_12_0 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (0 : Fin 8)
    have eq_12_1 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (1 : Fin 8)
    have eq_12_2 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (2 : Fin 8)
    have eq_12_3 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (3 : Fin 8)
    have eq_12_4 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (4 : Fin 8)
    have eq_12_5 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (5 : Fin 8)
    have eq_12_6 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (6 : Fin 8)
    have eq_12_7 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (2 : Fin 8) 1)) (7 : Fin 8)
    have eq_14_0 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (0 : Fin 8)
    have eq_14_1 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (1 : Fin 8)
    have eq_14_2 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (2 : Fin 8)
    have eq_14_3 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (3 : Fin 8)
    have eq_14_4 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (4 : Fin 8)
    have eq_14_5 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (5 : Fin 8)
    have eq_14_6 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (6 : Fin 8)
    have eq_14_7 := congrFun (h (Pi.single (1 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (7 : Fin 8)
    have eq_24_0 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (0 : Fin 8)
    have eq_24_1 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (1 : Fin 8)
    have eq_24_2 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (2 : Fin 8)
    have eq_24_3 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (3 : Fin 8)
    have eq_24_4 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (4 : Fin 8)
    have eq_24_5 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (5 : Fin 8)
    have eq_24_6 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (6 : Fin 8)
    have eq_24_7 := congrFun (h (Pi.single (2 : Fin 8) 1) (Pi.single (4 : Fin 8) 1)) (7 : Fin 8)
    norm_num [omul, vecOfOct, octMul, octOfVec, Pi.single_apply] at eq_12_0 eq_12_1 eq_12_2 eq_12_3 eq_12_4 eq_12_5 eq_12_6 eq_12_7 eq_14_0 eq_14_1 eq_14_2 eq_14_3 eq_14_4 eq_14_5 eq_14_6 eq_14_7 eq_24_0 eq_24_1 eq_24_2 eq_24_3 eq_24_4 eq_24_5 eq_24_6 eq_24_7
    refine ⟨c 0, ?_⟩
    ext i
    fin_cases i <;> norm_num [oone] <;> linarith
  · rintro ⟨r, rfl⟩
    intro ω u
    simp only [omul_smul_right, omul_one]

lemma omul_sub_left (a b c : Vec 8) : omul (a - b) c = omul a c - omul b c := by
  rw [sub_eq_add_neg, omul_add_left, sub_eq_add_neg]
  congr 1
  simpa only [neg_one_smul] using omul_smul_left b c (-1)

lemma zero_of_parts (y : Vec 16) (first : oct1 y = 0) (second : oct2 y = 0) : y = 0 := by
  rw [← pair_parts y, first, second]
  ext i
  refine Fin.addCases (m := 8) (n := 8) (fun j => ?_) (fun j => ?_) i <;>
    simp only [octPair, Fin.append_left, Fin.append_right, Pi.zero_apply]

theorem cayley_lines_meet_zero_proved :
    (∀ ω ω' : Vec 8, ω ≠ ω' → cayLine ω ∩ cayLine ω' = {0}) ∧ ∀ ω : Vec 8, cayLine ω ∩ cayLineInf = {0} := by
  constructor
  · intro ω ω' distinct
    ext y
    constructor
    · intro member
      have first : oct2 y = omul ω (oct1 y) := member.1
      have second : oct2 y = omul ω' (oct1 y) := member.2
      have product : omul (ω - ω') (oct1 y) = 0 := by rw [omul_sub_left, ← first, ← second, sub_self]
      have zero : oct1 y = 0 := by
        rcases oct_no_zero_divisors_proved (ω - ω') (oct1 y) product with coefficients | zero
        · exact False.elim (distinct (sub_eq_zero.mp coefficients))
        · exact zero
      have other : oct2 y = 0 := by rw [first, zero, omul_zero]
      exact Set.mem_singleton_iff.mpr (zero_of_parts y zero other)
    · intro equal
      have zero := Set.mem_singleton_iff.mp equal
      subst y
      change oct2 0 = omul ω (oct1 0) ∧ oct2 0 = omul ω' (oct1 0)
      change 0 = omul ω 0 ∧ 0 = omul ω' 0
      simp only [omul_zero, and_self]
  · intro ω
    ext y
    constructor
    · intro member
      have first : oct1 y = 0 := member.2
      have second : oct2 y = 0 := by
        have line : oct2 y = omul ω (oct1 y) := member.1
        rw [line, first, omul_zero]
      exact Set.mem_singleton_iff.mpr (zero_of_parts y first second)
    · intro equal
      have zero := Set.mem_singleton_iff.mp equal
      subst y
      change oct2 0 = omul ω (oct1 0) ∧ oct1 0 = 0
      change 0 = omul ω 0 ∧ 0 = 0
      simp only [omul_zero, and_self]

end Osserman.Proofs.OctonionNucleus

