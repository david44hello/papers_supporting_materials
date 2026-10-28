/-
Lem82.lean — Lemma 8.2 of paper 013 (lem:cubic-gcd, sec_small_roots.tex of the posting copy, lines 79-99): rows
lem_8_2_homog_divisor, lem_8_2_units, lem_8_2_degree, lem_8_2_lift, lem_8_2_suffices, lem_8_2_tangency, lem_8_2,
lem_8_2_lift_nonvacuous, lem_8_2_lift_hyp_nonvacuous.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Premise rows of lem_8_2 (leading arguments with their exact types, abbrevs below): lem_8_2_r1, lem_8_2_r2, lem_8_2_r3.
Grading of `𝒪 = ℝ[x]/(q)`. The substitution `x ↦ tx` gives a ring map `ℝ[x] → 𝒪[t]`, `D ↦ ∑_k π(D_k)t^k` (`D_k` the
homogeneous components); it kills `q`, so it factors through `𝒪`. A homogeneous `F` of degree `n` goes to `π(F)t^n`.
If `π(D)e = π(F) ≠ 0`, the image of `π(D)` divides a monomial in the domain `𝒪[t]` (`q` is prime, `s8_q_prime`), so
its lowest and highest degrees agree (`k`), and `π(D) = π(D_k)`, `k ≤ n` (value at `t = 1`). With `F = 1` this gives the
units; with `F = P_j` the homogeneous divisor and the bound on its degree.
-/
import Osserman.Proofs.QPrime
import Osserman.Proofs.Lem82DivQ
import Osserman.Proofs.S8Example
import Osserman.Proofs.Lem82Common

namespace Osserman.Proofs.Lem82

open Osserman Matrix MvPolynomial Osserman.Proofs.Lem82Common

/-! ### Homogeneous components -/

lemma piO_eq_zero_iff (g : MvPolynomial (Fin 16) ℝ) : piO g = 0 ↔ sqP 16 ∣ g :=
  Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton

/-! ### The substitution `x ↦ tx` -/

/-- `D ↦ π(D(tx)) ∈ 𝒪[t]`. -/
noncomputable def scaleHom : MvPolynomial (Fin 16) ℝ →+* Polynomial Ocal :=
  eval₂Hom (Polynomial.C.comp (piO.comp C)) fun i => Polynomial.C (piO (X i)) * Polynomial.X

lemma coeff_scale (D : MvPolynomial (Fin 16) ℝ) (k : ℕ) :
    (scaleHom D).coeff k = piO (homogeneousComponent k D) := by
  induction D using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [scaleHom, eval₂Hom_C, RingHom.comp_apply, Polynomial.coeff_C,
      homogeneousComponent_of_mem (isHomogeneous_C (Fin 16) a)]
    split_ifs <;> simp
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add, map_add]
  | mul_X p n ih =>
    have hX := isHomogeneous_X ℝ n
    rw [map_mul, mul_comm p, scaleHom, eval₂Hom_X', ← scaleHom, ← mul_assoc]
    cases k with
    | zero => rw [Polynomial.coeff_mul_X_zero, hc_mul_of_lt hX (by omega), map_zero]
    | succ k => rw [Polynomial.coeff_mul_X, Polynomial.coeff_mul_C, ih, hc_mul_of_le hX (by omega), Nat.add_sub_cancel,
        map_mul, mul_comm]

lemma scale_homog {F : MvPolynomial (Fin 16) ℝ} {n : ℕ} (hF : F.IsHomogeneous n) :
    scaleHom F = Polynomial.C (piO F) * Polynomial.X ^ n := by
  ext k
  rw [coeff_scale, Polynomial.coeff_C_mul_X_pow, homogeneousComponent_of_mem hF]
  split_ifs <;> simp

lemma eval_one_scale (D : MvPolynomial (Fin 16) ℝ) : (scaleHom D).eval 1 = piO D := by
  show ((Polynomial.evalRingHom 1).comp scaleHom) D = piO D
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) fun i => ?_ <;> simp [scaleHom]

/-- The substitution on `𝒪`. -/
noncomputable def scaleO : Ocal →+* Polynomial Ocal :=
  Ideal.Quotient.lift _ scaleHom fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, scale_homog Lem82DivQ.sqP_isHomogeneous,
      show piO (sqP 16) = 0 from (piO_eq_zero_iff _).mpr dvd_rfl, map_zero, zero_mul, zero_mul]

lemma scaleO_piO (D : MvPolynomial (Fin 16) ℝ) : scaleO (piO D) = scaleHom D :=
  Ideal.Quotient.lift_mk _ _ _

local instance : IsDomain Ocal := QPrime.s8_q_prime_proved.2.2

/-- If `π(D)` divides `π(F) ≠ 0`, `F` homogeneous of degree `n`, then `π(D) = π(D_k)` for some `k ≤ n`. -/
lemma homog_factor (D : MvPolynomial (Fin 16) ℝ) (e : Ocal) {F : MvPolynomial (Fin 16) ℝ} {n : ℕ}
    (hF : F.IsHomogeneous n) (hF0 : piO F ≠ 0) (h : piO D * e = piO F) :
    ∃ k ≤ n, piO D = piO (homogeneousComponent k D) := by
  have hprod : scaleHom D * scaleO e = Polynomial.monomial n (piO F) := by
    rw [← scaleO_piO, ← map_mul, h, scaleO_piO, scale_homog hF, Polynomial.C_mul_X_pow_eq_monomial]
  have hm0 : Polynomial.monomial n (piO F) ≠ 0 := by rwa [Ne, Polynomial.monomial_eq_zero_iff]
  have ha : scaleHom D ≠ 0 := fun h0 => hm0 (by rw [← hprod, h0, zero_mul])
  have hb : scaleO e ≠ 0 := fun h0 => hm0 (by rw [← hprod, h0, mul_zero])
  have hdeg := Polynomial.natDegree_mul ha hb
  have htr := Polynomial.natTrailingDegree_mul ha hb
  rw [hprod, Polynomial.natDegree_monomial_eq n hF0] at hdeg
  rw [hprod, Polynomial.natTrailingDegree_monomial hF0] at htr
  have hla := Polynomial.natTrailingDegree_le_natDegree (p := scaleHom D)
  have hlb := Polynomial.natTrailingDegree_le_natDegree (p := scaleO e)
  refine ⟨(scaleHom D).natDegree, by omega, ?_⟩
  rw [← eval_one_scale, Polynomial.eval_eq_sum_range, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, one_pow,
    mul_one, coeff_scale]
  intro i hi
  rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by rw [Finset.mem_range] at hi; omega), zero_mul]

/-! ### The rows on `𝒪` -/

/-- **Lemma 8.2, proof** (lines 90-92), row `lem_8_2_homog_divisor`. -/
theorem lem_8_2_homog_divisor_proved (d : Ocal) (f : MvPolynomial (Fin 16) ℝ) (n : ℕ) (hf : f.IsHomogeneous n)
    (hf0 : piO f ≠ 0) (hd : d ∣ piO f) :
    ∃ (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ), φ.IsHomogeneous r ∧ d = piO φ := by
  obtain ⟨D, rfl⟩ : ∃ D, piO D = d := Ideal.Quotient.mk_surjective d
  obtain ⟨e, he⟩ := hd
  obtain ⟨k, -, hk⟩ := homog_factor D e hf hf0 he.symm
  exact ⟨k, _, homogeneousComponent_isHomogeneous k D, hk⟩

/-- **Lemma 8.2, proof** (line 92), row `lem_8_2_units`. -/
theorem lem_8_2_units_proved (u : Ocal) : IsUnit u ↔ ∃ c : ℝ, c ≠ 0 ∧ u = piO (MvPolynomial.C c) := by
  constructor
  · intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨D, rfl⟩ : ∃ D, piO D = u := Ideal.Quotient.mk_surjective u
    obtain ⟨k, hk0, hk⟩ := homog_factor D v (isHomogeneous_one (Fin 16) ℝ) (by rw [map_one]; exact one_ne_zero)
      (by rw [hv, map_one])
    obtain rfl : k = 0 := by omega
    rw [homogeneousComponent_zero] at hk
    refine ⟨D.coeff 0, fun h0 => (not_isUnit_zero : ¬ IsUnit (0 : Ocal)) ?_, hk⟩
    rwa [hk, h0, map_zero, map_zero] at hu
  · rintro ⟨c, hc, rfl⟩
    exact (IsUnit.mk0 c hc).map (piO.comp C)

/-- **Lemma 8.2, proof** (lines 91-93), row `lem_8_2_degree`. -/
theorem lem_8_2_degree_proved (φ f : MvPolynomial (Fin 16) ℝ) (r : ℕ) (hφ : φ.IsHomogeneous r)
    (hφq : ¬ sqP 16 ∣ φ) (hf : f.IsHomogeneous 3) (hfq : ¬ sqP 16 ∣ f) (hu : ¬ IsUnit (piO φ))
    (hd : piO φ ∣ piO f) : 1 ≤ r ∧ r ≤ 3 := by
  have hφ0 : piO φ ≠ 0 := fun h => hφq ((piO_eq_zero_iff φ).mp h)
  constructor
  · by_contra hr
    obtain rfl : r = 0 := by omega
    have hC : φ = C (φ.coeff 0) := by rw [← homogeneousComponent_zero, homogeneousComponent_eq_self hφ]
    refine hu ((lem_8_2_units_proved _).mpr ⟨φ.coeff 0, fun h0 => hφ0 ?_, by rw [← hC]⟩)
    rw [hC, h0, map_zero, map_zero]
  · obtain ⟨e, he⟩ := hd
    obtain ⟨k, hk3, hk⟩ := homog_factor φ e hf (fun h => hfq ((piO_eq_zero_iff f).mp h)) he.symm
    rw [homogeneousComponent_of_mem hφ] at hk
    by_cases hkr : k = r
    · omega
    · rw [ite_eq_right hkr, map_zero] at hk
      exact absurd hk hφ0

/-! ### The lift -/

/-- **Lemma 8.2, proof** (lines 93-96), row `lem_8_2_lift`. -/
theorem lem_8_2_lift_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hdiv : ∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)) (hnd : ¬ ∀ j, sqP 16 ∣ P j) :
    ∃ (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ),
      1 ≤ r ∧ r ≤ 3 ∧ φ.IsHomogeneous r ∧ ¬ sqP 16 ∣ φ ∧ (∀ j, (Ψ j).IsHomogeneous (3 - r)) ∧
      (∀ j, P j = φ * Ψ j + sqP 16 * linP Cm j) ∧ ¬ IsUnit (piO φ) ∧ ∀ j, piO φ ∣ piO (P j) := by
  obtain ⟨j0, hj0⟩ := not_forall.mp hnd
  obtain ⟨d, hdu, hdj⟩ := hdiv
  have hP0 : piO (P j0) ≠ 0 := fun h => hj0 ((piO_eq_zero_iff _).mp h)
  obtain ⟨r, φ, hφ, rfl⟩ := lem_8_2_homog_divisor_proved d (P j0) 3 (hP3 j0) hP0 (hdj j0)
  have hφq : ¬ sqP 16 ∣ φ := fun h => by
    have hj := hdj j0
    rw [(piO_eq_zero_iff φ).mpr h, zero_dvd_iff] at hj
    exact hP0 hj
  obtain ⟨hr1, hr3⟩ := lem_8_2_degree_proved φ (P j0) r hφ hφq (hP3 j0) hj0 hdu (hdj j0)
  -- `P_j ≡ φE_j` modulo `q`
  have hE (j : Fin 16) : ∃ E G : MvPolynomial (Fin 16) ℝ, P j = φ * E + sqP 16 * G := by
    obtain ⟨e, he⟩ := hdj j
    obtain ⟨E, rfl⟩ : ∃ E, piO E = e := Ideal.Quotient.mk_surjective e
    obtain ⟨G, hG⟩ := (piO_eq_zero_iff (P j - φ * E)).mp (by rw [map_sub, map_mul, he, sub_self])
    exact ⟨E, G, by rw [← hG]; ring⟩
  choose E G hEG using hE
  choose c hc using fun j => Lem82DivQ.linear_eq_sum (homogeneousComponent_isHomogeneous 1 (G j))
  refine ⟨r, φ, fun j => homogeneousComponent (3 - r) (E j), Matrix.of c, hr1, hr3, hφ, hφq,
    fun j => homogeneousComponent_isHomogeneous _ _, fun j => ?_, hdu, hdj⟩
  -- the components of degree 3
  rw [← homogeneousComponent_eq_self (hP3 j), hEG j, map_add, hc_mul_of_le hφ hr3,
    hc_mul_of_le Lem82DivQ.sqP_isHomogeneous (by norm_num), ← hc j]
  rfl

/-- **Lemma 8.2, proof** (lines 96-97), row `lem_8_2_suffices`. -/
theorem lem_8_2_suffices_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P r φ Ψ Cm)
    (hΨ : ∀ j, sqP 16 ∣ Ψ j) : ∀ j, sqP 16 ∣ P j := fun j => by
  rw [h.2.2.2.2.2.2.2 j]
  exact dvd_add (dvd_mul_of_dvd_right (hΨ j) φ) (dvd_mul_right _ _)

/-- **Lemma 8.2, proof** (lines 99, 115), row `lem_8_2_tangency`. -/
theorem lem_8_2_tangency_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P r φ Ψ Cm) :
    φ * ∑ j, Ψ j * X j = -(sqP 16 * quadP Cm) := by
  obtain ⟨-, hP, -, -, -, -, -, hdec⟩ := h
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← tangency_poly hP, quadP_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [hdec j]; ring

/-! ### Lemma 8.2 -/

/-- The type of row `lem_8_2_r1`. -/
abbrev R1Hyp : Prop :=
  ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (_h : Lem82Lift P 1 φ Ψ Cm), ∀ j, sqP 16 ∣ Ψ j

/-- The type of row `lem_8_2_r2`. -/
abbrev R2Hyp : Prop :=
  ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (_h : Lem82Lift P 2 φ Ψ Cm), ∀ j, Ψ j = 0

/-- The type of row `lem_8_2_r3`. -/
abbrev R3Hyp : Prop :=
  ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (_h : Lem82Lift P 3 φ Ψ Cm),
    (∃ ψ : Vec 16, ∀ j, Ψ j = MvPolynomial.C (ψ j)) ∧ sqP 16 ∣ ∑ j, Ψ j * X j ∧ ∀ j, Ψ j = 0

/-- **Lemma 8.2** (lem:cubic-gcd, lines 79-84; proof lines 86-136), row `lem_8_2`. -/
theorem lem_8_2_proved (h1 : R1Hyp) (h2 : R2Hyp) (h3 : R3Hyp) (P : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hP3 : ∀ j, (P j).IsHomogeneous 3) (hP : CubicIdentities P)
    (hdiv : ∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧ ∀ x : Vec 16, evalField P x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  have hq : ∀ j, sqP 16 ∣ P j := by
    by_contra hnd
    obtain ⟨r, φ, Ψ, Cm, hr1, hr3, hφ, hφq, hΨ, hdec, -, -⟩ := lem_8_2_lift_proved P hP3 hdiv hnd
    have hL : Lem82Lift P r φ Ψ Cm := ⟨hP3, hP, hr1, hr3, hφ, hφq, hΨ, hdec⟩
    refine hnd (lem_8_2_suffices_proved P r φ Ψ Cm hL ?_)
    interval_cases r
    · exact h1 P φ Ψ Cm hL
    · exact fun j => by rw [h2 P φ Ψ Cm hL j]; exact dvd_zero _
    · exact fun j => by rw [(h3 P φ Ψ Cm hL).2.2 j]; exact dvd_zero _
  obtain ⟨J, hJ, -, hJs, hJo⟩ := Lem82DivQ.lem_8_2_div_q_proved P hP3 hP hq
  exact ⟨J, hJs, hJo, Lem82DivQ.evalField_eq hJ⟩

/-! ### Non-vacuity -/

lemma not_dvd_X_pow (r : ℕ) : ¬ sqP 16 ∣ X 0 ^ r := fun h => by
  have hpr := QPrime.s8_q_prime_proved.2.1
  obtain ⟨g, hg⟩ := hpr.dvd_of_dvd_pow h
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hg
    exact X_ne_zero 0 hg
  have hdeg := congrArg totalDegree hg
  rw [totalDegree_X, totalDegree_mul_of_isDomain hpr.ne_zero hg0,
    Lem82DivQ.sqP_isHomogeneous.totalDegree hpr.ne_zero] at hdeg
  omega

/-- **Lemma 8.2, non-vacuity** (Lean-only row), row `lem_8_2_lift_nonvacuous`: `P(x) = qJ_0x` (`J_0 = Jcl 0`),
`φ = x_0^r`, `Ψ = 0`, `C = J_0`. -/
theorem lem_8_2_lift_nonvacuous_proved (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    ∃ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
      (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P r φ Ψ Cm :=
  ⟨S8Example.qfield (CorDNonvacuous.Jcl 0), X 0 ^ r, 0, CorDNonvacuous.Jcl 0, S8Example.qfield_homog _,
    S8Example.qfield_cubic (CorDNonvacuous.Jcl_skew 0) (S8Example.jcl_clifford.2 0), hr1, hr3,
    isHomogeneous_X_pow 0 r, not_dvd_X_pow r, fun _ => isHomogeneous_zero _ _ _,
    fun j => by rw [Pi.zero_apply, mul_zero, zero_add]; rfl⟩

/-- **Lemma 8.2, lift step, non-vacuity** (Lean-only row), row `lem_8_2_lift_hyp_nonvacuous`: `P = (x_0^3, 0, …, 0)`,
`d = π(x_0)`. -/
theorem lem_8_2_lift_hyp_nonvacuous_proved :
    ∃ P : Fin 16 → MvPolynomial (Fin 16) ℝ, (∀ j, (P j).IsHomogeneous 3) ∧
      (∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)) ∧ ¬ ∀ j, sqP 16 ∣ P j := by
  refine ⟨fun j => if j = 0 then X 0 ^ 3 else 0, fun j => ?_, ⟨piO (X 0), fun hu => ?_, fun j => ?_⟩,
    fun h => not_dvd_X_pow 3 (by simpa using h 0)⟩
  · dsimp only
    split_ifs
    · exact isHomogeneous_X_pow 0 3
    · exact isHomogeneous_zero _ _ _
  · -- `π(x_0) = π(c)` with `c ≠ 0` is false at `x = 0`
    obtain ⟨c, hc, he⟩ := (lem_8_2_units_proved _).mp hu
    obtain ⟨g, hg⟩ := (piO_eq_zero_iff (X 0 - C c)).mp (by rw [map_sub, he, sub_self])
    have h0 := congrArg (eval 0) hg
    rw [map_sub, eval_X, eval_C, map_mul, Lem82DivQ.eval_sqP, zero_dotProduct, zero_mul] at h0
    exact hc (by simpa using h0)
  · dsimp only
    split_ifs
    · rw [map_pow]
      exact dvd_pow_self _ (by norm_num)
    · rw [map_zero]
      exact dvd_zero _

end Osserman.Proofs.Lem82
