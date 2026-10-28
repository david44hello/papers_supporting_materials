/-
Osserman/Proofs/S84Fields.lean — §8.4 of paper 013, the fields and the spectral identity: rows s8_4_fields,
s8_4_identity, s8_4_same_sign, s8_4_three_col (statements copied verbatim from Osserman/Paper/Statements8.lean).
Premise rows (leading arguments with their exact types): s8_cubic_identities, s8_spectral_identity.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. [Nik2006, Lemma 3.1(2)] gives two orthonormal unit fields of the double eigenvalue; multiplying by
`q^((3-d)/2)` makes them cubic eigenfields with `⟨P_a, P_b⟩ = δ_ab q³` at every `x` (homogeneity). The simple field
is as in §8.3. The spectral-projector row gives the identity; its diagonal with equal signs gives `q | P_ij`
(Lemma 3.11, three terms); with opposite signs, the sign `ε` of the double weight makes the three-column hypotheses.
-/
import Osserman.Proofs.S83Fields

namespace Osserman.Proofs.S84

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.S83

lemma pattern_facts {M N : ℕ} (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) :
    ∑ i, (![M, N, 2, 1] : Fin 4 → ℕ) i = 15 ∧ ∀ i, 0 < (![M, N, 2, 1] : Fin 4 → ℕ) i := by
  rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by simp [Fin.sum_univ_succ], fun i => by fin_cases i <;> simp⟩

/-- Homogenized fields keep constant inner products: `⟨E(u), F(u)⟩ = c` on the unit sphere gives
`⟨q^k E(x), q^k F(x)⟩ = c q³` with `k = (3-d)/2`. -/
lemma homog_dot {E F : Fin 16 → MvPolynomial (Fin 16) ℝ} {d : ℕ} (hd : d = 1 ∨ d = 3)
    (hE : ∀ j, (E j).IsHomogeneous d) (hF : ∀ j, (F j).IsHomogeneous d) (c : ℝ)
    (hunit : ∀ u : Vec 16, u ⬝ᵥ u = 1 → evalField E u ⬝ᵥ evalField F u = c) (x : Vec 16) :
    evalField (fun j => sqP 16 ^ ((3 - d) / 2) * E j) x ⬝ᵥ evalField (fun j => sqP 16 ^ ((3 - d) / 2) * F j) x =
      c * (x ⬝ᵥ x) ^ 3 := by
  obtain ⟨s, u, hu, rfl⟩ := Spectral.exists_unit_scale x
  have hev (G : Fin 16 → MvPolynomial (Fin 16) ℝ) (hG : ∀ j, (G j).IsHomogeneous d) :
      evalField (fun j => sqP 16 ^ ((3 - d) / 2) * G j) (s • u) = ((s * s) ^ ((3 - d) / 2) * s ^ d) • evalField G u := by
    funext j
    simp only [evalField, map_mul, map_pow, Poly.eval_sqP, eval_smul_of_homogeneous (hG j), Pi.smul_apply,
      smul_eq_mul, smul_dotProduct, dotProduct_smul, hu]
    ring
  rw [hev E hE, hev F hF, smul_dotProduct, dotProduct_smul, hunit u hu, smul_dotProduct, dotProduct_smul, hu]
  simp only [smul_eq_mul]
  rcases hd with rfl | rfl <;> norm_num <;> ring

lemma homog_cubic {E : MvPolynomial (Fin 16) ℝ} {d : ℕ} (hd : d = 1 ∨ d = 3) (hE : E.IsHomogeneous d) :
    (sqP 16 ^ ((3 - d) / 2) * E).IsHomogeneous 3 := by
  have h := (Poly.sqP_isHomogeneous.pow ((3 - d) / 2)).mul hE
  rcases hd with rfl | rfl
  · simpa using h
  · simpa using h

/-- A double nonzero reduced eigenvalue has two cubic eigenfields, orthonormal up to `q³` at every `x`. -/
lemma double_fields {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15) (hpos : ∀ i, 0 < m i) (hk : k ≤ 4) (hzero : ∃ j, ev j = 0)
    (i₀ : Fin k) (hτ : ev i₀ ≠ 0) (hm2 : m i₀ = 2) :
    ∃ P0 P1 : Fin 16 → MvPolynomial (Fin 16) ℝ, (∀ j, (P0 j).IsHomogeneous 3) ∧ (∀ j, (P1 j).IsHomogeneous 3) ∧
      IsEigenfield R (ev i₀) P0 ∧ IsEigenfield R (ev i₀) P1 ∧
      ∀ x : Vec 16, evalField P0 x ⬝ᵥ evalField P0 x = (x ⬝ᵥ x) ^ 3 ∧
        evalField P1 x ⬝ᵥ evalField P1 x = (x ⬝ᵥ x) ^ 3 ∧ evalField P0 x ⬝ᵥ evalField P1 x = 0 := by
  have hO := (CorD.hasPattern_osserman_proved R m (by omega) ⟨ev, hR.1, hR.2⟩).1
  obtain ⟨d, E, hodd, hdk, hhom, hunit⟩ :=
    Osserman.Cited.nik2006_lemma_3_1 R hO ev hR.1 m hpos hsum hR.2 hzero i₀ hτ (Or.inr hm2)
  have hd : d = 1 ∨ d = 3 := by
    obtain ⟨t, rfl⟩ := hodd
    omega
  let a0 : Fin (m i₀) := ⟨0, by omega⟩
  let a1 : Fin (m i₀) := ⟨1, by omega⟩
  have h01 : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
  have heig (a : Fin (m i₀)) : ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      evalField (E a) x ∈ Module.End.eigenspace (R.jacobiMap x) (ev i₀) ⊓ perp x :=
    fun x hx => (hunit x hx).2.1 a
  have hdot (a b : Fin (m i₀)) (u : Vec 16) (hu : u ⬝ᵥ u = 1) :
      evalField (E a) u ⬝ᵥ evalField (E b) u = if a = b then 1 else 0 := (hunit u hu).1 a b
  refine ⟨_, _, fun j => homog_cubic hd (hhom a0 j), fun j => homog_cubic hd (hhom a1 j),
    eigenfield_of_unit (hhom a0) (ev i₀) (heig a0) _, eigenfield_of_unit (hhom a1) (ev i₀) (heig a1) _,
    fun x => ⟨?_, ?_, ?_⟩⟩
  · rw [homog_dot hd (hhom a0) (hhom a0) 1 (fun u hu => by simpa using hdot a0 a0 u hu) x, one_mul]
  · rw [homog_dot hd (hhom a1) (hhom a1) 1 (fun u hu => by simpa using hdot a1 a1 u hu) x, one_mul]
  · rw [homog_dot hd (hhom a0) (hhom a1) 0 (fun u hu => by simpa [h01] using hdot a0 a1 u hu) x, zero_mul]

/-- Row `s8_4_fields`. -/
theorem s8_4_fields_proved (hcub : CubicIdHyp) (R : CurvTensor 16) (M N : ℕ)
    (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) (ev : Fin 4 → ℝ)
    (hR : PatternEv R ![M, N, 2, 1] ev) (h0 : ev 0 = 0) :
    ∃ P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ, Sec84Data R M N ev P := by
  obtain ⟨hsum, hpos⟩ := pattern_facts hMN
  have hne (i : Fin 4) (hi : i ≠ 0) : ev i ≠ 0 := fun h => hi (hR.1 (h.trans h0.symm))
  have h23 : ev 2 ≠ ev 3 := fun e => absurd (hR.1 e) (by decide)
  obtain ⟨P0, P1, h0a, h1a, h0e, h1e, hdots⟩ :=
    double_fields R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 2 (hne 2 (by decide)) (by simp)
  obtain ⟨P2, h2a, h2b, h2e⟩ :=
    simple_field hcub R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 3 (hne 3 (by decide)) (by simp)
  have o0 := eigenfield_orth h23 (by norm_num : (3 : ℕ) ≠ 0) h0a h0e h2e
  have o1 := eigenfield_orth h23 (by norm_num : (3 : ℕ) ≠ 0) h1a h1e h2e
  refine ⟨![P0, P1, P2], hMN, hR, h0, fun i j => ?_, fun x i k => ?_, h0e, h1e, h2e, h2b⟩
  · fin_cases i
    · exact h0a j
    · exact h1a j
    · exact h2a j
  · obtain ⟨n0, n1, n01⟩ := hdots x
    fin_cases i <;> fin_cases k
    · simpa using n0
    · simpa using n01
    · simpa using o0 x
    · simpa [dotProduct_comm] using n01
    · simpa using n1
    · simpa using o1 x
    · simpa [dotProduct_comm] using o0 x
    · simpa [dotProduct_comm] using o1 x
    · simpa using (h2b x).2.1

/-! ### The spectral identity and its consequences modulo `q` -/

lemma identity_sum (hSpec : SpecIdHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ}
    {P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec84Data R M N ev P) (x : Vec 16) :
    ∑ j, (![ev 2 * (ev 2 - ev 1), ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)] j) •
        vecMulVec (evalField (P j) x) (evalField (P j) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) := by
  obtain ⟨hMN, hR, h0, h3, horth, he0, he1, he2, -⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts hMN
  have h23 : ev 2 ≠ ev 3 := fun e => absurd (hR.1 e) (by decide)
  have key := hSpec R _ ev hR hsum 0 1 (by decide) h0 P ![ev 2, ev 2, ev 3] h3
    (fun j => by fin_cases j; exacts [he0, he1, he2]) horth
    (fun j => by
      fin_cases j
      exacts [⟨2, by decide, by decide, rfl⟩, ⟨2, by decide, by decide, rfl⟩, ⟨3, by decide, by decide, rfl⟩])
    (fun i hi0 hi1 => by
      fin_cases i
      · exact absurd rfl hi0
      · exact absurd rfl hi1
      · show (Finset.univ.filter fun j => (![ev 2, ev 2, ev 3] : Fin 3 → ℝ) j = ev 2).card = 2
        rw [Finset.card_eq_two]
        exact ⟨0, 1, by decide, by ext j; fin_cases j <;> simp [h23.symm]⟩
      · show (Finset.univ.filter fun j => (![ev 2, ev 2, ev 3] : Fin 3 → ℝ) j = ev 3).card = 1
        rw [Finset.card_eq_one]
        exact ⟨2, by ext j; fin_cases j <;> simp [h23]⟩)
    x
  rw [Fin.sum_univ_three] at key ⊢
  simpa using key

/-- Row `s8_4_identity`. -/
theorem s8_4_identity_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec84Data R M N ev P) :
    ∀ x : Vec 16, (ev 2 * (ev 2 - ev 1)) • (vecMulVec (evalField (P 0) x) (evalField (P 0) x) +
          vecMulVec (evalField (P 1) x) (evalField (P 1) x)) +
        (ev 3 * (ev 3 - ev 1)) • vecMulVec (evalField (P 2) x) (evalField (P 2) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) := by
  intro x
  have e := identity_sum hSpec h x
  rw [Fin.sum_univ_three] at e
  rw [smul_add]
  simpa using e

/-- Row `s8_4_same_sign`. -/
theorem s8_4_same_sign_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) (hs : 0 < (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1))) :
    ∀ i j, sqP 16 ∣ P i j := by
  intro i j
  let w : Fin 3 → ℝ := ![ev 2 * (ev 2 - ev 1), ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)]
  have hd := spectral_dvd R P w (ev 1) (identity_sum hSpec h) j j
  have hdiag : sqP 16 ∣ ∑ r, C (w r) * (fun r => P r j) r ^ 2 := by
    convert hd using 1
    exact Finset.sum_congr rfl fun r _ => by ring
  have hsign : (∀ r, 0 < w r) ∨ ∀ r, w r < 0 := by
    rcases mul_pos_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl fun r => by fin_cases r <;> simpa [w]
    · exact Or.inr fun r => by fin_cases r <;> simpa [w]
  exact sos_dvd (by norm_num) (fun r => P r j) w hsign hdiag i

/-- Row `s8_4_three_col`. -/
theorem s8_4_three_col_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) (hs : (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1)) < 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ThreeColHyp R ![ev 2, ev 2, ev 3] P
      (ε • ![ev 2 * (ev 2 - ev 1), ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)]) := by
  let w : Fin 3 → ℝ := ![ev 2 * (ev 2 - ev 1), ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)]
  have hd := spectral_dvd R P w (ev 1) (identity_sum hSpec h)
  obtain ⟨-, -, -, h3, horth, he0, he1, he2, -⟩ := h
  have common (ε : ℝ) (h0 : 0 < ε * w 0) (h2 : ε * w 2 < 0) : ThreeColHyp R ![ev 2, ev 2, ev 3] P (ε • w) := by
    refine ⟨h3, fun i => by fin_cases i; exacts [he0, he1, he2], fun x i k hik => by simpa [hik] using horth x i k,
      fun x i => by simpa using horth x i i, by simpa using h0, by simpa [w] using h0, by simpa using h2,
      fun a b => ?_⟩
    have e : ∑ i, C ((ε • w) i) * P i a * P i b = C ε * ∑ i, C (w i) * P i a * P i b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, map_mul]; ring
    rw [e]
    exact Dvd.dvd.mul_left (hd a b) _
  rcases mul_neg_iff.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨1, Or.inl rfl, common 1 (by simpa [w] using h1) (by simpa [w] using h2)⟩
  · exact ⟨-1, Or.inr rfl, common (-1) (by simpa [w] using h1) (by simpa [w] using h2)⟩

end Osserman.Proofs.S84
