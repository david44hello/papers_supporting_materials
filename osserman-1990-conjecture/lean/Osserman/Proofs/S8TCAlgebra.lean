/-
S8TCAlgebra.lean — scalar shifts and quotient-ring algebra of the three-column step, paper 013.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots
import Osserman.Cited.Nik2006
import Osserman.Proofs.Rem72dCounts
import Osserman.Proofs.ThmEElementary

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial Osserman.Proofs.Rem72a Osserman.Proofs.Rem72d
open Osserman.Proofs.ThmEElementary

theorem s8_shift_to_zero_proved {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ) (hR : PatternEv R m ev)
    (i₀ : Fin k) :
    ∃ R0 : CurvTensor 16, (∀ u v z, R0.op u v z = R.op u v z - ev i₀ • R1fun u v z) ∧
      (∀ x, R0.jacobi x = R.jacobi x - ev i₀ • Pi x) ∧ PatternEv R0 m (fun i => ev i - ev i₀) ∧
      (∀ i, i ≠ i₀ → ev i - ev i₀ ≠ 0) ∧ (R0.IsOsserman ↔ R.IsOsserman) ∧ (R0.IsClifford ↔ R.IsClifford) := by
  obtain ⟨R0, hop, hjac, hO, hC⟩ := shift_R1_proved R (ev i₀)
  refine ⟨R0, hop, hjac, ⟨?_, ?_⟩, ?_, hO, hC⟩
  · intro i j equal
    apply hR.1
    linarith
  · intro x hx i
    rw [thm_E_shift_proved R R0 (ev i₀) hop x hx (ev i), hR.2 x hx i]
  · intro i different
    exact sub_ne_zero.mpr (hR.1.ne different)

theorem s8_clifford_base_mult_proved {ν : ℕ} (R' : CurvTensor 16) (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ) (hη : ∀ α, η α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      Module.End.eigenspace (R'.jacobiMap x) l0 ⊓ perp x = perp x ⊓ ⨅ α, perp (Jα α *ᵥ x) ∧
        R'.redMult x l0 = 15 - ν := by
  classical
  intro x hx
  have empty : IsEmpty {a : Fin ν // l0 + η a = l0} :=
    ⟨fun a => hη a.1 (by linarith [a.2])⟩
  have span_zero : Submodule.span ℝ ((fun a => Jα a *ᵥ x) '' {a | l0 + η a = l0}) = ⊥ := by
    have set_zero : ((fun a => Jα a *ᵥ x) '' {a | l0 + η a = l0}) = ∅ := by
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro a equal
      exact False.elim (hη a (by linarith))
    rw [set_zero, Submodule.span_empty]
  constructor
  · rw [eig_clifford hJ (hjac x) hx l0, span_zero]
    simp only [ite_true, bot_sup_eq, Wsub]
  · simpa only [Fintype.card_of_isEmpty, ite_true, zero_add] using
      clifford_multiplicity R' Jα hJ l0 η hjac x hx l0

lemma piO_q : piO (sqP 16) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)

lemma piO_zero_of_dvd {p : MvPolynomial (Fin 16) ℝ} (hp : sqP 16 ∣ p) : piO p = 0 := by
  obtain ⟨z, rfl⟩ := hp
  rw [map_mul, piO_q, zero_mul]

lemma tcImg_product (wt : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (i : Fin 3) (a b : Fin 16) :
    tcImg wt P i a * tcImg wt P i b = piO (C |wt i| * P i a * P i b) := by
  have square : (C (Real.sqrt |wt i|) : MvPolynomial (Fin 16) ℝ) ^ 2 = C |wt i| := by
    rw [← map_pow, Real.sq_sqrt (abs_nonneg _)]
  unfold tcImg
  rw [← map_mul]
  congr 1
  calc
    (C (Real.sqrt |wt i|) * P i a) * (C (Real.sqrt |wt i|) * P i b) =
        C (Real.sqrt |wt i|) ^ 2 * P i a * P i b := by ring
    _ = _ := by rw [square]

theorem s8_tc_rankone_proved (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) :
    (∀ i, Real.sqrt |wt i| ≠ 0) ∧ ∀ a b : Fin 16,
      tcImg wt P 0 a * tcImg wt P 0 b + tcImg wt P 1 a * tcImg wt P 1 b = tcImg wt P 2 a * tcImg wt P 2 b := by
  obtain ⟨_, _, _, _, positive0, positive1, negative2, divisibility⟩ := h
  have nonzero (i : Fin 3) : wt i ≠ 0 := by
    fin_cases i
    · exact ne_of_gt positive0
    · exact ne_of_gt positive1
    · exact ne_of_lt negative2
  refine ⟨fun i => ne_of_gt (Real.sqrt_pos.mpr (abs_pos.mpr (nonzero i))), fun a b => ?_⟩
  have projected := piO_zero_of_dvd (divisibility a b)
  norm_num [Fin.sum_univ_succ, map_add] at projected
  rw [tcImg_product, tcImg_product, tcImg_product]
  simp only [abs_of_pos positive0, abs_of_pos positive1, abs_of_neg negative2, map_neg, neg_mul, map_mul]
  linear_combination projected

theorem s8_tc_minors_of_s8_q_prime
    (hQ : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal)
    (p : Fin 3 → Fin 16 → Ocal) (hp : ∀ a b, p 0 a * p 0 b + p 1 a * p 1 b = p 2 a * p 2 b) :
    ∀ a b : Fin 16,
      (p 0 a ^ 2 + p 1 a ^ 2) * (p 0 b ^ 2 + p 1 b ^ 2) - (p 0 a * p 0 b + p 1 a * p 1 b) ^ 2 =
        (p 0 a * p 1 b - p 1 a * p 0 b) ^ 2 ∧
      p 2 a ^ 2 * p 2 b ^ 2 - (p 2 a * p 2 b) ^ 2 = 0 ∧ p 0 a * p 1 b - p 1 a * p 0 b = 0 := by
  let := hQ.2.2
  intro a b
  have identity : (p 0 a ^ 2 + p 1 a ^ 2) * (p 0 b ^ 2 + p 1 b ^ 2) -
      (p 0 a * p 0 b + p 1 a * p 1 b) ^ 2 = (p 0 a * p 1 b - p 1 a * p 0 b) ^ 2 := by ring
  have zero : p 2 a ^ 2 * p 2 b ^ 2 - (p 2 a * p 2 b) ^ 2 = 0 := by ring
  refine ⟨identity, zero, ?_⟩
  have diagonal (i : Fin 16) : p 0 i ^ 2 + p 1 i ^ 2 = p 2 i ^ 2 := by simpa only [pow_two] using hp i i
  rw [diagonal a, diagonal b, hp a b, zero] at identity
  exact (sq_eq_zero_iff.mp identity.symm)

theorem s8_tc_sqrt_frac_of_s8_q_prime
    (hQ : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal)
    (u0 u1 : Ocal) (v p2 : Fin 16 → Ocal)
    (hp : ∀ a b, (u0 ^ 2 + u1 ^ 2) * (v a * v b) = p2 a * p2 b) (a : Fin 16) (ha : v a ≠ 0) :
    ∃ z : FractionRing Ocal, z ^ 2 = algebraMap Ocal (FractionRing Ocal) (u0 ^ 2 + u1 ^ 2) ∧
      z * algebraMap Ocal (FractionRing Ocal) (v a) = algebraMap Ocal (FractionRing Ocal) (p2 a) := by
  let := hQ.2.2
  let f := algebraMap Ocal (FractionRing Ocal)
  have nonzero : f (v a) ≠ 0 := fun zero =>
    ha ((IsFractionRing.injective Ocal (FractionRing Ocal)) (by simpa only [map_zero] using zero))
  have relation := congrArg f (hp a a)
  simp only [map_mul] at relation
  refine ⟨f (p2 a) / f (v a), ?_, ?_⟩
  · rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 nonzero)).mpr
    linear_combination -relation
  · exact div_mul_cancel₀ _ nonzero

theorem s8_tc_integral_of_s8_q_prime
    (hQ : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal)
    (z : FractionRing Ocal) (y : Ocal) (hz : z ^ 2 = algebraMap Ocal (FractionRing Ocal) y) :
    ∃ y' : Ocal, z = algebraMap Ocal (FractionRing Ocal) y' := by
  let := hQ.2.2
  let := Osserman.Cited.nik2006_thm_3_1
  have integral : IsIntegral Ocal z := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C y, Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hz, sub_self]
  obtain ⟨y', equal⟩ := IsIntegrallyClosed.isIntegral_iff.mp integral
  exact ⟨y', equal.symm⟩

lemma outer_equal_sign {A : Type*} [CommRing A] [IsDomain A] {ν : ℕ} (q p : Fin ν → A)
    (hp : ∀ a b, q a * q b = p a * p b) : p = q ∨ p = -q := by
  classical
  by_cases zero : q = 0
  · subst q
    left
    funext a
    have square := hp a a
    simpa only [Pi.zero_apply, zero_mul, mul_self_eq_zero] using square.symm
  · obtain ⟨a, nonzero⟩ : ∃ a, q a ≠ 0 := by
      simpa only [_root_.funext_iff, Pi.zero_apply, not_forall] using zero
    have factor : (p a - q a) * (p a + q a) = 0 := by linear_combination -(hp a a)
    rcases mul_eq_zero.mp factor with first | second
    · left
      have equal : p a = q a := sub_eq_zero.mp first
      funext b
      exact (mul_left_cancel₀ nonzero (by simpa only [equal] using (hp a b).symm))
    · right
      have equal : p a = -q a := eq_neg_of_add_eq_zero_left second
      funext b
      apply mul_left_cancel₀ nonzero
      have relation := hp a b
      rw [equal, neg_mul] at relation
      change q a * p b = q a * -q b
      linear_combination relation

theorem s8_tc_sign_of_s8_q_prime
    (hQ : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal)
    (u3 : Ocal) (v p2 : Fin 16 → Ocal) (hp : ∀ a b, (u3 * v a) * (u3 * v b) = p2 a * p2 b) :
    p2 = u3 • v ∨ p2 = (-u3) • v := by
  let := hQ.2.2
  have result := outer_equal_sign (u3 • v) p2 hp
  simpa only [neg_smul] using result

end Osserman.Proofs.S8TC
