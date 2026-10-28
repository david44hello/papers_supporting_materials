/-
Osserman/Proofs/Lemma71Algebra.lean — algebraic steps of Lemma 7.1, paper 013, lines 718–736.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.OctonionQuaternion
import Osserman.Proofs.OctonionNucleus

namespace Osserman.Proofs.Lemma71Algebra

open Osserman Matrix Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts

theorem lem_7_1_a_left_linear_proved (D : Matrix (Fin 8) (Fin 8) ℝ)
    (hD : ∀ ω : Vec 8, ∀ y ∈ cayLine ω, octPair (D *ᵥ oct1 y) (D *ᵥ oct2 y) ∈ cayLine ω) :
    ∀ ω u : Vec 8, D *ᵥ omul ω u = omul ω (D *ᵥ u) := by
  intro ω u
  have member : octPair u (omul ω u) ∈ cayLine ω := by simp [cayLine]
  have image := hD ω (octPair u (omul ω u)) member
  simpa only [cayLine, Set.mem_ofPred_eq, first_pair, second_pair] using image

theorem lem_7_1_a_right_mult_proved (D : Matrix (Fin 8) (Fin 8) ℝ)
    (hD : ∀ ω u : Vec 8, D *ᵥ omul ω u = omul ω (D *ᵥ u)) :
    (∀ u : Vec 8, D *ᵥ u = omul u (D *ᵥ oone)) ∧
      ∀ ω u : Vec 8, omul (omul ω u) (D *ᵥ oone) = omul ω (omul u (D *ᵥ oone)) := by
  have formula (u : Vec 8) : D *ᵥ u = omul u (D *ᵥ oone) := by
    simpa only [omul_one] using hD u oone
  refine ⟨formula, ?_⟩
  intro ω u
  rw [← formula, hD, formula]

theorem lem_7_1_b_gamma_proved (B C : Matrix (Fin 8) (Fin 8) ℝ)
    (hBC : ∀ ω u : Vec 8, B *ᵥ omul ω u = -omul (oconj ω) (C *ᵥ u)) :
    B = -C ∧ ∀ ω : Vec 8, C *ᵥ ω = omul (oconj ω) (C *ᵥ oone) := by
  have conj_one : oconj oone = oone := by
    ext i
    fin_cases i <;> norm_num [oconj, oone, vecOfOct, octConj, octOfVec, Pi.single_apply]
  have action (u : Vec 8) : B *ᵥ u = -(C *ᵥ u) := by
    simpa only [one_omul, conj_one] using hBC oone u
  have matrices : B = -C := by
    ext i j
    have value := congrFun (action (Pi.single j 1)) i
    simpa using value
  refine ⟨matrices, ?_⟩
  intro ω
  have equal := hBC ω oone
  rw [omul_one, action] at equal
  exact neg_injective equal

theorem lem_7_1_b_rel_proved (C : Matrix (Fin 8) (Fin 8) ℝ) (γ : Vec 8)
    (hC : ∀ ω u : Vec 8, C *ᵥ omul ω u = omul (oconj ω) (C *ᵥ u))
    (hγ : ∀ ω : Vec 8, C *ᵥ ω = omul (oconj ω) γ) :
    ∀ a b : Vec 8, omul (omul a b) γ = omul b (omul a γ) := by
  intro a b
  have equal := hC (oconj b) (oconj a)
  simpa only [hγ, oct_conj_mul_proved, oconj_invol] using equal

theorem lem_7_1_b_gamma_zero_proved (γ : Vec 8)
    (hγ : ∀ a b : Vec 8, omul (omul a b) γ = omul b (omul a γ)) : γ = 0 := by
  obtain ⟨f, injective, unital, multiplicative, p, hp⟩ :=
    Osserman.Proofs.OctonionQuaternion.oct_quaternion_subalgebra_proved γ
  let ii : Quaternion ℝ := ⟨0, 1, 0, 0⟩
  let jj : Quaternion ℝ := ⟨0, 0, 1, 0⟩
  have equal : f ((ii * jj) * p) = f (jj * (ii * p)) := by
    simpa only [multiplicative, hp] using hγ (f ii) (f jj)
  have quaternion_equal := injective equal
  have real_eq := congrArg (fun q : Quaternion ℝ => q.re) quaternion_equal
  have i_eq := congrArg (fun q : Quaternion ℝ => q.imI) quaternion_equal
  have j_eq := congrArg (fun q : Quaternion ℝ => q.imJ) quaternion_equal
  have k_eq := congrArg (fun q : Quaternion ℝ => q.imK) quaternion_equal
  simp [ii, jj, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
    Quaternion.imK_mul] at real_eq i_eq j_eq k_eq
  have zero : p = 0 := by
    apply Quaternion.ext <;> simp only [Quaternion.re_zero, Quaternion.imI_zero,
      Quaternion.imJ_zero, Quaternion.imK_zero] <;> linarith
  rw [← hp, zero, map_zero]

end Osserman.Proofs.Lemma71Algebra
