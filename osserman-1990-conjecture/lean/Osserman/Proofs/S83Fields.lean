/-
Osserman/Proofs/S83Fields.lean — §8.3 of paper 013, the fields and (eq:twocolumn): rows s8_3_fields, s8_3_twocolumn,
s8_3_same_sign, s8_3_mod_q, s8_3_linear_fields (statements copied verbatim from Osserman/Paper/Statements8.lean).
Premise rows (leading arguments with their exact types): s8_cubic_identities, s8_spectral_identity, lem_8_2_div_q.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. [Nik2006, Lemma 3.1] (k = 4, degree d odd ≤ 3) gives unit fields of the two simple eigenvalues; homogeneity
(`eigenfield_of_unit`) and the cubic identities row make them cubic eigenfields. Fields of distinct eigenvalues are
orthogonal, so the spectral-projector row gives (eq:twocolumn). Its entries give the congruence modulo `q`
(`spectral_dvd`); on the diagonal, equal signs and Lemma 3.11 give `q | P_ij` (`sos_dvd`); the off-diagonal form is
`s8_3_mod_q`. Divisible fields are `q` times skew orthogonal linear eigenfields (lem_8_2_div_q, `eigenfield_linP`).
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.S8Tools
import Osserman.Proofs.CorD
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.S83

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools

/-! ### The premise types (rows of Statements8.lean proved by other members) -/

/-- The type of row `s8_cubic_identities`. -/
abbrev CubicIdHyp : Prop :=
  ∀ (d : ℕ) (_hd : d = 1 ∨ d = 3) (E : Fin 16 → MvPolynomial (Fin 16) ℝ) (_hE : ∀ j, (E j).IsHomogeneous d)
    (_hunit : ∀ x : Vec 16, x ⬝ᵥ x = 1 → evalField E x ⬝ᵥ x = 0 ∧ evalField E x ⬝ᵥ evalField E x = 1 ∧
      evalField E (evalField E x) = -x),
    let P : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => sqP 16 ^ ((3 - d) / 2) * E j
    (∀ j, (P j).IsHomogeneous 3) ∧ CubicIdentities P

/-- The type of row `s8_spectral_identity`. -/
abbrev SpecIdHyp : Prop :=
  ∀ {k r : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (_hR : PatternEv R m ev) (_hsum : ∑ i, m i = 15) (i0 i1 : Fin k) (_h01 : i0 ≠ i1) (_h0 : ev i0 = 0)
    (P : Fin r → Fin 16 → MvPolynomial (Fin 16) ℝ) (μ : Fin r → ℝ) (_hP3 : ∀ j a, (P j a).IsHomogeneous 3)
    (_hPe : ∀ j, IsEigenfield R (μ j) (P j))
    (_hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ 3 else 0)
    (_hμ : ∀ j, ∃ i, i ≠ i0 ∧ i ≠ i1 ∧ μ j = ev i)
    (_hcount : ∀ i, i ≠ i0 → i ≠ i1 → (Finset.univ.filter fun j => μ j = ev i).card = m i),
    ∀ x : Vec 16, ∑ j, (μ j * (μ j - ev i1)) • vecMulVec (evalField (P j) x) (evalField (P j) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev i1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ)))

/-- The type of row `lem_8_2_div_q`. -/
abbrev DivQHyp : Prop :=
  ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (_hP3 : ∀ j, (P j).IsHomogeneous 3)
    (_hP : CubicIdentities P) (_hq : ∀ j, sqP 16 ∣ P j),
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, (∀ j, P j = sqP 16 * linP J j) ∧
      (∀ x : Vec 16, (J *ᵥ x) ⬝ᵥ x = 0 ∧ (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x) ∧ Jᵀ = -J ∧ Jᵀ * J = 1

/-! ### Simple eigenfields from [Nik2006, Lemma 3.1] -/

lemma pattern_facts {M N : ℕ} (hMN : (M = 7 ∧ N = 6) ∨ (M = 8 ∧ N = 5)) :
    ∑ i, (![M, N, 1, 1] : Fin 4 → ℕ) i = 15 ∧ ∀ i, 0 < (![M, N, 1, 1] : Fin 4 → ℕ) i := by
  rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by simp [Fin.sum_univ_succ], fun i => by fin_cases i <;> simp⟩

/-- A simple nonzero reduced eigenvalue of a pattern with at most four eigenvalues, one zero, has a cubic eigenfield
satisfying (8.1). -/
lemma simple_field {k : ℕ} (hcub : CubicIdHyp) (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15) (hpos : ∀ i, 0 < m i) (hk : k ≤ 4) (hzero : ∃ j, ev j = 0)
    (i₀ : Fin k) (hτ : ev i₀ ≠ 0) (hm1 : m i₀ = 1) :
    ∃ P : Fin 16 → MvPolynomial (Fin 16) ℝ, (∀ j, (P j).IsHomogeneous 3) ∧ CubicIdentities P ∧
      IsEigenfield R (ev i₀) P := by
  have hO := (CorD.hasPattern_osserman_proved R m (by omega) ⟨ev, hR.1, hR.2⟩).1
  obtain ⟨d, E, hodd, hdk, hhom, hunit⟩ :=
    Osserman.Cited.nik2006_lemma_3_1 R hO ev hR.1 m hpos hsum hR.2 hzero i₀ hτ (Or.inl hm1)
  have hd : d = 1 ∨ d = 3 := by
    obtain ⟨t, rfl⟩ := hodd
    omega
  let a0 : Fin (m i₀) := ⟨0, by omega⟩
  have heig : ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      evalField (E a0) x ∈ Module.End.eigenspace (R.jacobiMap x) (ev i₀) ⊓ perp x :=
    fun x hx => (hunit x hx).2.1 a0
  have hunit' : ∀ x : Vec 16, x ⬝ᵥ x = 1 → evalField (E a0) x ⬝ᵥ x = 0 ∧
      evalField (E a0) x ⬝ᵥ evalField (E a0) x = 1 ∧ evalField (E a0) (evalField (E a0) x) = -x := by
    intro x hx
    obtain ⟨h1, -, h3⟩ := hunit x hx
    have hp : x ⬝ᵥ evalField (E a0) x = 0 := (Submodule.mem_inf.mp (heig x hx)).2
    refine ⟨by rw [dotProduct_comm]; exact hp, by simpa using h1 a0 a0, h3 hm1 a0⟩
  have hc := hcub d hd (E a0) (hhom a0) hunit'
  obtain ⟨h3, hC⟩ := hc
  exact ⟨_, h3, hC, eigenfield_of_unit (hhom a0) (ev i₀) heig _⟩

/-- Row `s8_3_fields`. -/
theorem s8_3_fields_proved (hcub : CubicIdHyp) (R : CurvTensor 16) (M N : ℕ)
    (hMN : (M = 7 ∧ N = 6) ∨ (M = 8 ∧ N = 5)) (ev : Fin 4 → ℝ)
    (hR : PatternEv R ![M, N, 1, 1] ev) (h0 : ev 0 = 0) :
    ∃ P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ, Sec83Data R M N ev P := by
  obtain ⟨hsum, hpos⟩ := pattern_facts hMN
  have hne (i : Fin 4) (hi : i ≠ 0) : ev i ≠ 0 := fun h => hi (hR.1 (h.trans h0.symm))
  obtain ⟨P2, h2a, h2b, h2c⟩ :=
    simple_field hcub R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 2 (hne 2 (by decide)) (by simp)
  obtain ⟨P3, h3a, h3b, h3c⟩ :=
    simple_field hcub R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 3 (hne 3 (by decide)) (by simp)
  refine ⟨![P2, P3], hMN, hR, h0, fun i j => ?_, fun i => ?_, h2c, h3c⟩
  · fin_cases i
    · exact h2a j
    · exact h3a j
  · fin_cases i
    · exact h2b
    · exact h3b

/-! ### (eq:twocolumn) and its consequences modulo `q` -/

lemma sec83_ne {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ} {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ}
    (h : Sec83Data R M N ev P) : ev 2 ≠ ev 3 := fun e => absurd (h.2.1.1 e) (by decide)

lemma sec83_orth {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ} {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ}
    (h : Sec83Data R M N ev P) (x : Vec 16) (j l : Fin 2) :
    evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ 3 else 0 := by
  have h23 := sec83_ne h
  obtain ⟨-, -, -, h3, hC, he2, he3⟩ := h
  have o := eigenfield_orth h23 (by norm_num : (3 : ℕ) ≠ 0) (h3 0) he2 he3 x
  fin_cases j <;> fin_cases l
  · exact (hC 0 x).2.1
  · simpa using o
  · simpa [dotProduct_comm] using o
  · exact (hC 1 x).2.1

/-- (eq:twocolumn) as a sum over the two columns. -/
lemma twocolumn_sum (hSpec : SpecIdHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ}
    {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec83Data R M N ev P) (x : Vec 16) :
    ∑ j, (![ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)] j) • vecMulVec (evalField (P j) x) (evalField (P j) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) := by
  have h23 := sec83_ne h
  have horth := sec83_orth h
  obtain ⟨hMN, hR, h0, h3, -, he2, he3⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts hMN
  have key := hSpec R _ ev hR hsum 0 1 (by decide) h0 P ![ev 2, ev 3] h3
    (fun j => by fin_cases j; exacts [he2, he3]) horth
    (fun j => by fin_cases j; exacts [⟨2, by decide, by decide, rfl⟩, ⟨3, by decide, by decide, rfl⟩])
    (fun i hi0 hi1 => by
      fin_cases i
      · exact absurd rfl hi0
      · exact absurd rfl hi1
      · show (Finset.univ.filter fun j => (![ev 2, ev 3] : Fin 2 → ℝ) j = ev 2).card = 1
        rw [Finset.card_eq_one]
        exact ⟨0, by ext j; fin_cases j <;> simp [h23.symm]⟩
      · show (Finset.univ.filter fun j => (![ev 2, ev 3] : Fin 2 → ℝ) j = ev 3).card = 1
        rw [Finset.card_eq_one]
        exact ⟨1, by ext j; fin_cases j <;> simp [h23]⟩)
    x
  rw [Fin.sum_univ_two] at key ⊢
  simpa using key

/-- Row `s8_3_twocolumn`. -/
theorem s8_3_twocolumn_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) :
    ∀ x : Vec 16, (ev 2 * (ev 2 - ev 1)) • vecMulVec (evalField (P 0) x) (evalField (P 0) x) +
        (ev 3 * (ev 3 - ev 1)) • vecMulVec (evalField (P 1) x) (evalField (P 1) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) := by
  intro x
  have e := twocolumn_sum hSpec h x
  rw [Fin.sum_univ_two] at e
  simpa using e

/-- The entrywise congruence of (eq:twocolumn) modulo `q`. -/
lemma twocolumn_dvd (hSpec : SpecIdHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ}
    {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec83Data R M N ev P) (a b : Fin 16) :
    sqP 16 ∣ C (ev 2 * (ev 2 - ev 1)) * P 0 a * P 0 b + C (ev 3 * (ev 3 - ev 1)) * P 1 a * P 1 b := by
  have hd := spectral_dvd R P _ (ev 1) (twocolumn_sum hSpec h) a b
  rw [Fin.sum_univ_two] at hd
  simpa using hd

/-- Row `s8_3_same_sign`. -/
theorem s8_3_same_sign_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (hs : 0 < (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1))) :
    ∀ i j, sqP 16 ∣ P i j := by
  intro i j
  let w : Fin 2 → ℝ := ![ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)]
  have hdiag : sqP 16 ∣ ∑ r, C (w r) * (fun r => P r j) r ^ 2 := by
    have e := twocolumn_dvd hSpec h j j
    rw [Fin.sum_univ_two]
    convert e using 1
    simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hsign : (∀ r, 0 < w r) ∨ ∀ r, w r < 0 := by
    rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl fun r => by fin_cases r <;> simpa [w]
    · exact Or.inr fun r => by fin_cases r <;> simpa [w]
  exact sos_dvd (by norm_num) (fun r => P r j) w hsign hdiag i

/-- Row `s8_3_mod_q`. -/
theorem s8_3_mod_q_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) :
    ∀ j k : Fin 16, piO (MvPolynomial.C (ev 2 * (ev 2 - ev 1)) * P 0 j * P 0 k) =
      piO (MvPolynomial.C (-(ev 3 * (ev 3 - ev 1))) * P 1 j * P 1 k) := by
  intro j k
  have e := twocolumn_dvd hSpec h j k
  unfold piO
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  convert e using 1
  rw [map_neg]
  ring

/-- Row `s8_3_linear_fields`. -/
theorem s8_3_linear_fields_proved (hdiv : DivQHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (hq : ∀ i j, sqP 16 ∣ P i j) :
    ∃ J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ, (∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1) ∧
      (∀ i (x : Vec 16), evalField (P i) x = (x ⬝ᵥ x) • (J i *ᵥ x)) ∧
      IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1)) := by
  obtain ⟨-, -, -, h3, hC, he2, he3⟩ := h
  choose J hJP _ hJs hJo using fun i => hdiv (P i) (h3 i) (hC i) (hq i)
  have hev (i : Fin 2) (x : Vec 16) : evalField (P i) x = (x ⬝ᵥ x) • (J i *ᵥ x) := by
    funext j
    have e := congrFun (evalField_linP (J i) x) j
    simp only [evalField] at e ⊢
    rw [hJP i j, map_mul, Poly.eval_sqP, e, Pi.smul_apply, smul_eq_mul]
  exact ⟨J, fun i => ⟨hJs i, hJo i⟩, hev, eigenfield_linP he2 (J 0) (hev 0), eigenfield_linP he3 (J 1) (hev 1)⟩

end Osserman.Proofs.S83
