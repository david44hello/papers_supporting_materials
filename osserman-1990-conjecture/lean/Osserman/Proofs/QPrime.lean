/-
Osserman/Proofs/QPrime.lean — §8.2 of paper 013 (sec_small_roots.tex lines 60-61, posting copy): q = |x|² is irreducible,
hence prime in ℝ[x_1, …, x_16], and 𝒪 = ℝ[x]/(q) is a domain (row s8_q_prime).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots

namespace Osserman.Proofs.QPrime

open Osserman MvPolynomial

/-- Splitting off the variable `x_0`: `q = X^2 + C (x_1² + … + x_15²)` in `(ℝ[x_1..x_15])[X]`. -/
lemma finSuccEquiv_sqP :
    finSuccEquiv ℝ 15 (sqP 16) = Polynomial.X ^ 2 + Polynomial.C (sqP 15) := by
  unfold sqP
  rw [map_sum, Fin.sum_univ_succ]
  simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ, map_sum, Polynomial.C_pow]

/-- `-(x_1² + … + x_15²)` is not a square: evaluate at the all-ones point. -/
lemma sq_add_sqP_ne_zero (a : MvPolynomial (Fin 15) ℝ) : a ^ 2 + sqP 15 ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin 15 => (1 : ℝ))) h
  simp [sqP] at h1
  nlinarith [sq_nonneg (eval (fun _ : Fin 15 => (1 : ℝ)) a)]

lemma irreducible_X_sq_add_C :
    Irreducible (Polynomial.X ^ 2 + Polynomial.C (sqP 15) : Polynomial (MvPolynomial (Fin 15) ℝ)) := by
  have hmon : (Polynomial.X ^ 2 + Polynomial.C (sqP 15) :
      Polynomial (MvPolynomial (Fin 15) ℝ)).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (sqP 15) :
      Polynomial (MvPolynomial (Fin 15) ℝ)).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  rw [hmon.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot.def] at ha
  simp at ha
  exact sq_add_sqP_ne_zero a ha

lemma irreducible_sqP : Irreducible (sqP 16) := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv ℝ 15), finSuccEquiv_sqP]
  exact irreducible_X_sq_add_C

theorem s8_q_prime_proved : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal := by
  have hirr := irreducible_sqP
  have hprime : Prime (sqP 16) := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  refine ⟨hirr, hprime, ?_⟩
  have : (Ideal.span {sqP 16}).IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr hprime
  exact Ideal.Quotient.isDomain _

end Osserman.Proofs.QPrime
