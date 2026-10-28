/-
Lem82R1aAlg.lean — Lemma 8.2, the case r = 1, first four steps (paper 013, sec_small_roots.tex lines 115-120):
φ is a nonzero linear form; φ divides ⟨Cx,x⟩; the corrected C̃ = C - afᵀ is skew; φ divides q - |C̃x|² = xᵀ(I+C̃²)x.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.QPrime
import Osserman.Proofs.Lem82Common
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

namespace Osserman.Proofs.Lem82R1a

open Osserman Matrix MvPolynomial Osserman.Proofs.Lem82Common

/-! ### Linear and quadratic forms -/

lemma formP_zero : formP (0 : Vec 16) = 0 := by
  simp [formP]

lemma isHomogeneous_quadP (M : Matrix (Fin 16) (Fin 16) ℝ) : (quadP M).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
    (isHomogeneous_C_mul_X (M a b) a).mul (isHomogeneous_X ℝ b)

lemma linP_sub (A B : Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 16) : linP (A - B) j = linP A j - linP B j := by
  simp [linP, sub_mul, Finset.sum_sub_distrib]

lemma linP_vecMulVec (a f : Vec 16) (j : Fin 16) : linP (vecMulVec a f) j = C (a j) * formP f := by
  simp only [linP, formP, vecMulVec_apply, map_mul, Finset.mul_sum, mul_assoc]

/-! ### Degree-one forms are prime and do not divide `q` -/

lemma totalDegree_formP {f : Vec 16} (hf : formP f ≠ 0) : (formP f).totalDegree = 1 :=
  (isHomogeneous_formP f).totalDegree hf

lemma prime_formP {f : Vec 16} (hf : formP f ≠ 0) : Prime (formP f) := by
  have hirr : Irreducible (formP f) := by
    refine irreducible_of_totalDegree_eq_one (totalDegree_formP hf) fun c hc => ?_
    obtain ⟨d, hd⟩ := exists_coeff_ne_zero hf
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hd (zero_dvd_iff.mp (hc d))
    exact isUnit_iff_ne_zero.mpr hc0
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr

lemma totalDegree_of_isUnit {u : MvPolynomial (Fin 16) ℝ} (hu : IsUnit u) : u.totalDegree = 0 :=
  (isUnit_iff_totalDegree_of_isReduced.mp hu).2

lemma not_dvd_sqP {f : Vec 16} (hf : formP f ≠ 0) : ¬ formP f ∣ sqP 16 := by
  rintro ⟨g, hg⟩
  have hq0 : sqP 16 ≠ 0 := QPrime.irreducible_sqP.ne_zero
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hg
    exact hq0 hg
  have hdeg := totalDegree_mul_of_isDomain hf hg0
  rw [← hg, Lem82DivQ.sqP_isHomogeneous.totalDegree hq0, totalDegree_formP hf] at hdeg
  rcases QPrime.irreducible_sqP.isUnit_or_isUnit hg with hu | hu
  · have := totalDegree_of_isUnit hu
    rw [totalDegree_formP hf] at this
    omega
  · have := totalDegree_of_isUnit hu
    omega

/-! ### Polynomial identities from (eq:cubicidentities) -/

lemma norm_poly {P : Fin 16 → MvPolynomial (Fin 16) ℝ} (hP : CubicIdentities P) :
    ∑ j, P j ^ 2 = sqP 16 ^ 3 := by
  refine MvPolynomial.funext fun x => ?_
  have e := (hP x).2.1
  rw [map_pow, Lem82DivQ.eval_sqP, ← e]
  simp [evalField, dotProduct, sq]

/-! ### The rows -/

theorem lem_8_2_r1_form_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 φ Ψ Cm) :
    ∃ f : Vec 16, f ≠ 0 ∧ φ = formP f := by
  obtain ⟨-, -, -, -, hφ, hq, -, -⟩ := h
  obtain ⟨c, hc⟩ := Lem82DivQ.linear_eq_sum hφ
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  apply hq
  rw [← hc]
  simp

theorem lem_8_2_r1_div_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : Vec 16) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 (formP f) Ψ Cm) :
    ∃ a : Vec 16, quadP Cm = formP f * formP a := by
  obtain ⟨-, hP, -, -, -, hq, -, hdec⟩ := h
  have hf0 : formP f ≠ 0 := by
    intro h0
    rw [h0] at hq
    exact hq (dvd_zero _)
  have hid : formP f * ∑ j, Ψ j * X j + sqP 16 * quadP Cm = 0 := by
    rw [← tangency_poly hP, quadP_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdec j]
    ring
  have hdvd : formP f ∣ sqP 16 * quadP Cm := ⟨-∑ j, Ψ j * X j, by linear_combination hid⟩
  have hdvd' : formP f ∣ quadP Cm :=
    ((prime_formP hf0).dvd_or_dvd hdvd).resolve_left (not_dvd_sqP hf0)
  obtain ⟨g, hg⟩ := hdvd'
  have hg1 := eq_mul_homogeneousComponent (isHomogeneous_formP f) (isHomogeneous_quadP Cm) (by norm_num) hg
  obtain ⟨a, ha⟩ := Lem82DivQ.linear_eq_sum (homogeneousComponent_isHomogeneous (2 - 1) g)
  exact ⟨a, hg1.trans (by rw [← ha]; rfl)⟩

theorem lem_8_2_r1_skew_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : Vec 16) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 (formP f) Ψ Cm) (a : Vec 16)
    (ha : quadP Cm = formP f * formP a) :
    let Ct := Cm - vecMulVec a f
    let Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => Ψ j + sqP 16 * MvPolynomial.C (a j)
    (∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) ∧ Ctᵀ = -Ct ∧ ∀ j, (Ψt j).IsHomogeneous 2 := by
  intro Ct Ψt
  obtain ⟨-, -, -, -, -, -, hΨ, hdec⟩ := h
  refine ⟨fun j => ?_, ?_, fun j => ?_⟩
  · simp only [Ψt, Ct, linP_sub, linP_vecMulVec, hdec j]
    ring
  · have hsum : ∑ j, C (a j) * formP f * X j = formP f * formP a := by
      rw [show formP a = ∑ k, C (a k) * X k from rfl, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hq0 : quadP Ct = 0 := by
      rw [quadP_eq]
      simp only [Ct, linP_sub, linP_vecMulVec, sub_mul, Finset.sum_sub_distrib, ← quadP_eq, ha, hsum, sub_self]
    refine Lem82DivQ.skew_of_forall fun x => ?_
    rw [← eval_quadP, hq0, map_zero]
  · exact (hΨ j).add (Lem82DivQ.sqP_isHomogeneous.mul (isHomogeneous_C _ _))

theorem lem_8_2_r1_divides_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) :
    formP f ∣ sqP 16 - (∑ j, linP Ct j ^ 2) ∧ sqP 16 - (∑ j, linP Ct j ^ 2) = quadP (1 + Ct * Ct) := by
  have hq0 : sqP 16 ≠ 0 := QPrime.irreducible_sqP.ne_zero
  have key : sqP 16 ^ 2 * (sqP 16 - ∑ j, linP Ct j ^ 2) =
      formP f * ∑ j, (formP f * Ψt j ^ 2 + 2 * sqP 16 * Ψt j * linP Ct j) := by
    have e1 : sqP 16 ^ 2 * (sqP 16 - ∑ j, linP Ct j ^ 2) =
        ∑ j, P j ^ 2 - ∑ j, sqP 16 ^ 2 * linP Ct j ^ 2 := by
      rw [norm_poly hP, mul_sub, Finset.mul_sum]
      ring
    rw [e1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hdec j]
    ring
  refine ⟨?_, ?_⟩
  · by_cases hf0 : formP f = 0
    · rw [hf0, zero_mul] at key
      have e := (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hq0)
      rw [hf0, e, zero_dvd_iff]
    · have hdvd : formP f ∣ sqP 16 ^ 2 * (sqP 16 - ∑ j, linP Ct j ^ 2) := ⟨_, key⟩
      refine ((prime_formP hf0).dvd_or_dvd hdvd).resolve_left fun h2 => ?_
      exact not_dvd_sqP hf0 ((prime_formP hf0).dvd_of_dvd_pow h2)
  · refine MvPolynomial.funext fun x => ?_
    have hskew : (Ct *ᵥ (Ct *ᵥ x)) ⬝ᵥ x = -((Ct *ᵥ x) ⬝ᵥ (Ct *ᵥ x)) := by
      rw [dotProduct_comm (Ct *ᵥ (Ct *ᵥ x)) x, dotProduct_mulVec x Ct (Ct *ᵥ x), ← mulVec_transpose, hCt,
        neg_mulVec, neg_dotProduct]
    rw [eval_quadP, add_mulVec, one_mulVec, ← mulVec_mulVec, add_dotProduct, hskew, map_sub,
      Lem82DivQ.eval_sqP, map_sum]
    simp only [map_mul, Lem82DivQ.eval_linP, dotProduct, sq]
    ring

end Osserman.Proofs.Lem82R1a

