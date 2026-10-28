/-
S85Fields.lean — §8.5 of paper 013 (sec_small_roots.tex of the posting copy, lines 252-262): the three simple eigenfields and
the cubic spectral identity: rows s8_5_fields, s8_5_identity, s8_5_same_sign, s8_5_three_col.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Premise rows (leading arguments with their exact types, `CubicIdHyp` and `SpecIdHyp` of S83Fields.lean):
s8_cubic_identities, s8_spectral_identity.
Proof. After the shift there are five reduced eigenvalues `0, λ, μ_1, μ_2, μ_3`, so [Nik2006, Lemma 3.1] gives unit
fields of odd degree at most four, hence one or three; the cubic identities row makes them cubic eigenfields with
(8.1). Fields of distinct eigenvalues are orthogonal, so the spectral-projector row gives the identity with weights
`w_i = μ_i(μ_i - λ)`, all nonzero. Equal signs: its diagonal and Lemma 3.11 give `q | P_ij`. Mixed signs: two weights
share a sign and the third has the other; a permutation puts the odd one last and `ε = ±1` makes it negative.
-/
import Osserman.Proofs.S83Fields

namespace Osserman.Proofs.S85

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.S83

lemma pattern_facts5 {M N : ℕ} (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) :
    ∑ i, (![M, N, 1, 1, 1] : Fin 5 → ℕ) i = 15 ∧ ∀ i, 0 < (![M, N, 1, 1, 1] : Fin 5 → ℕ) i := by
  rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by simp [Fin.sum_univ_succ], fun i => by fin_cases i <;> simp⟩

/-- A simple nonzero reduced eigenvalue of a pattern with at most five eigenvalues, one zero, has a cubic eigenfield
satisfying (8.1) (the degree `d` of [Nik2006, Lemma 3.1] is odd and at most `k - 1 ≤ 4`, so `d = 1` or `d = 3`). -/
lemma simple_field5 {k : ℕ} (hcub : CubicIdHyp) (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15) (hpos : ∀ i, 0 < m i) (hk : k ≤ 5) (hzero : ∃ j, ev j = 0)
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
    exact ⟨by rw [dotProduct_comm]; exact hp, by simpa using h1 a0 a0, h3 hm1 a0⟩
  obtain ⟨h3, hC⟩ := hcub d hd (E a0) (hhom a0) hunit'
  exact ⟨_, h3, hC, eigenfield_of_unit (hhom a0) (ev i₀) heig _⟩

/-- **§8.5** (lines 254-256), row `s8_5_fields`: the three simple eigenvalues have cubic eigenfields satisfying (8.1). -/
theorem s8_5_fields_proved (hcub : CubicIdHyp) (R : CurvTensor 16) (M N : ℕ)
    (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) (ev : Fin 5 → ℝ)
    (hR : PatternEv R ![M, N, 1, 1, 1] ev) (h0 : ev 0 = 0) :
    ∃ P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ, Sec85Data R M N ev P := by
  obtain ⟨hsum, hpos⟩ := pattern_facts5 hMN
  have hne (i : Fin 5) (hi : i ≠ 0) : ev i ≠ 0 := fun h => hi (hR.1 (h.trans h0.symm))
  obtain ⟨P2, h2a, h2b, h2c⟩ :=
    simple_field5 hcub R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 2 (hne 2 (by decide)) (by simp)
  obtain ⟨P3, h3a, h3b, h3c⟩ :=
    simple_field5 hcub R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 3 (hne 3 (by decide)) (by simp)
  obtain ⟨P4, h4a, h4b, h4c⟩ :=
    simple_field5 hcub R _ ev hR hsum hpos le_rfl ⟨0, h0⟩ 4 (hne 4 (by decide)) (by simp)
  refine ⟨![P2, P3, P4], hMN, hR, h0, fun i j => ?_, fun i => ?_, h2c, h3c, h4c⟩
  · fin_cases i
    · exact h2a j
    · exact h3a j
    · exact h4a j
  · fin_cases i
    · exact h2b
    · exact h3b
    · exact h4b

/-! ### The spectral identity and its consequences modulo `q` -/

/-- The three fields are mutually orthogonal of squared norm `q³` (distinct eigenvalues, (8.1)). -/
lemma sec85_orth {R : CurvTensor 16} {M N : ℕ} {ev : Fin 5 → ℝ} {P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ}
    (h : Sec85Data R M N ev P) (x : Vec 16) (j l : Fin 3) :
    evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ 3 else 0 := by
  obtain ⟨-, hR, -, h3, hC, he2, he3, he4⟩ := h
  have hne (i k : Fin 5) (hik : i ≠ k) : ev i ≠ ev k := fun e => hik (hR.1 e)
  have o01 := eigenfield_orth (hne 2 3 (by decide)) (by norm_num : (3 : ℕ) ≠ 0) (h3 0) he2 he3 x
  have o02 := eigenfield_orth (hne 2 4 (by decide)) (by norm_num : (3 : ℕ) ≠ 0) (h3 0) he2 he4 x
  have o12 := eigenfield_orth (hne 3 4 (by decide)) (by norm_num : (3 : ℕ) ≠ 0) (h3 1) he3 he4 x
  fin_cases j <;> fin_cases l
  · simpa using (hC 0 x).2.1
  · simpa using o01
  · simpa using o02
  · rw [dotProduct_comm]
    simpa using o01
  · simpa using (hC 1 x).2.1
  · simpa using o12
  · rw [dotProduct_comm]
    simpa using o02
  · rw [dotProduct_comm]
    simpa using o12
  · simpa using (hC 2 x).2.1

/-- The cubic spectral identity with weights `μ_i(μ_i - λ)`, from the spectral-projector row. -/
lemma identity_sum5 (hSpec : SpecIdHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 5 → ℝ}
    {P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec85Data R M N ev P) (x : Vec 16) :
    ∑ i, ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1)) •
        vecMulVec (evalField (P i) x) (evalField (P i) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) := by
  have horth := sec85_orth h
  obtain ⟨hMN, hR, h0, h3, -, he2, he3, he4⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts5 hMN
  have hne (i k : Fin 5) (hik : i ≠ k) : ev i ≠ ev k := fun e => hik (hR.1 e)
  exact hSpec R _ ev hR hsum 0 1 (by decide) h0 P ![ev 2, ev 3, ev 4] h3
    (fun j => by fin_cases j; exacts [he2, he3, he4]) horth
    (fun j => by
      fin_cases j
      exacts [⟨2, by decide, by decide, rfl⟩, ⟨3, by decide, by decide, rfl⟩, ⟨4, by decide, by decide, rfl⟩])
    (fun i hi0 hi1 => by
      fin_cases i
      · exact absurd rfl hi0
      · exact absurd rfl hi1
      · show (Finset.univ.filter fun j => (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) j = ev 2).card = 1
        rw [Finset.card_eq_one]
        exact ⟨0, by ext j; fin_cases j <;> simp [hne 3 2 (by decide), hne 4 2 (by decide)]⟩
      · show (Finset.univ.filter fun j => (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) j = ev 3).card = 1
        rw [Finset.card_eq_one]
        exact ⟨1, by ext j; fin_cases j <;> simp [hne 2 3 (by decide), hne 4 3 (by decide)]⟩
      · show (Finset.univ.filter fun j => (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) j = ev 4).card = 1
        rw [Finset.card_eq_one]
        exact ⟨2, by ext j; fin_cases j <;> simp [hne 2 4 (by decide), hne 3 4 (by decide)]⟩)
    x

/-- **§8.5** (lines 256-258), row `s8_5_identity`. -/
theorem s8_5_identity_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) :
    let mus : Fin 3 → ℝ := ![ev 2, ev 3, ev 4]
    ∀ x : Vec 16, ∑ i, (mus i * (mus i - ev 1)) • vecMulVec (evalField (P i) x) (evalField (P i) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) :=
  fun x => identity_sum5 hSpec h x

/-- **§8.5** (lines 258-260), row `s8_5_same_sign`: equal signs give `q | P_ij` (diagonal entries, Lemma 3.11). -/
theorem s8_5_same_sign_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) :
    let mus : Fin 3 → ℝ := ![ev 2, ev 3, ev 4]
    ((∀ i, 0 < mus i * (mus i - ev 1)) ∨ ∀ i, mus i * (mus i - ev 1) < 0) → ∀ i j, sqP 16 ∣ P i j := by
  intro mus hsign i j
  have hd := spectral_dvd R P (fun r => mus r * (mus r - ev 1)) (ev 1) (identity_sum5 hSpec h) j j
  have hdiag : sqP 16 ∣ ∑ r, C (mus r * (mus r - ev 1)) * (fun r => P r j) r ^ 2 := by
    convert hd using 1
    exact Finset.sum_congr rfl fun r _ => by ring
  exact sos_dvd (by norm_num) (fun r => P r j) (fun r => mus r * (mus r - ev 1)) hsign hdiag i

/-- The transposition `(k 2)` puts the odd index `k` last. -/
lemma odd_last (w : Fin 3 → ℝ) (ε : ℝ) (k : Fin 3) (hpos : ∀ i, i ≠ k → 0 < ε * w i) (hneg : ε * w k < 0) :
    0 < ε * w (Equiv.swap k 2 0) ∧ 0 < ε * w (Equiv.swap k 2 1) ∧ ε * w (Equiv.swap k 2 2) < 0 := by
  refine ⟨hpos _ ?_, hpos _ ?_, by rwa [Equiv.swap_apply_right]⟩ <;>
    rw [Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] <;> decide

/-- Three nonzero reals not all of one sign: a permutation `sg` and a sign `ε = ±1` make the first two positive and
the third negative (the odd one goes last). -/
lemma sign_perm (w : Fin 3 → ℝ) (hw : ∀ i, w i ≠ 0) (hmix : ¬ ((∀ i, 0 < w i) ∨ ∀ i, w i < 0)) :
    ∃ (sg : Equiv.Perm (Fin 3)) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      0 < ε * w (sg 0) ∧ 0 < ε * w (sg 1) ∧ ε * w (sg 2) < 0 := by
  have all3 (p : ℝ → Prop) (h0 : p (w 0)) (h1 : p (w 1)) (h2 : p (w 2)) : ∀ i, p (w i) := fun i => by
    fin_cases i <;> assumption
  have mk (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k : Fin 3) (hpos : ∀ i, i ≠ k → 0 < ε * w i) (hneg : ε * w k < 0) :
      ∃ (sg : Equiv.Perm (Fin 3)) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
        0 < ε * w (sg 0) ∧ 0 < ε * w (sg 1) ∧ ε * w (sg 2) < 0 :=
    ⟨_, ε, hε, odd_last w ε k hpos hneg⟩
  rcases lt_or_gt_of_ne (hw 0) with a | a <;> rcases lt_or_gt_of_ne (hw 1) with b | b <;>
    rcases lt_or_gt_of_ne (hw 2) with c | c
  · exact absurd (Or.inr (all3 (· < 0) a b c)) hmix
  · exact mk (-1) (Or.inr rfl) 2 (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> linarith) (by simp; linarith)
  · exact mk (-1) (Or.inr rfl) 1 (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> linarith) (by simp; linarith)
  · exact mk 1 (Or.inl rfl) 0 (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> linarith) (by simp; linarith)
  · exact mk (-1) (Or.inr rfl) 0 (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> linarith) (by simp; linarith)
  · exact mk 1 (Or.inl rfl) 1 (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> linarith) (by simp; linarith)
  · exact mk 1 (Or.inl rfl) 2 (fun i hi => by fin_cases i <;> simp at hi ⊢ <;> linarith) (by simp; linarith)
  · exact absurd (Or.inl (all3 (0 < ·) a b c)) hmix

/-- **§8.5** (lines 260-262), row `s8_5_three_col`: mixed signs give the three-column hypotheses after a permutation
and a global sign. -/
theorem s8_5_three_col_proved (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) :
    let mus : Fin 3 → ℝ := ![ev 2, ev 3, ev 4]
    ¬ ((∀ i, 0 < mus i * (mus i - ev 1)) ∨ ∀ i, mus i * (mus i - ev 1) < 0) →
      ∃ (sg : Equiv.Perm (Fin 3)) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
        ThreeColHyp R (fun i => mus (sg i)) (fun i => P (sg i)) (fun i => ε * (mus (sg i) * (mus (sg i) - ev 1))) := by
  intro mus hmix
  have hd := spectral_dvd R P (fun r => mus r * (mus r - ev 1)) (ev 1) (identity_sum5 hSpec h)
  have horth := sec85_orth h
  obtain ⟨-, hR, h0, h3, -, he2, he3, he4⟩ := h
  have hz (i : Fin 5) (hi : i ≠ 0) : ev i ≠ 0 := fun e => hi (hR.1 (e.trans h0.symm))
  have hl (i : Fin 5) (hi : i ≠ 1) : ev i - ev 1 ≠ 0 := sub_ne_zero.mpr fun e => hi (hR.1 e)
  have hw : ∀ i, mus i * (mus i - ev 1) ≠ 0 := fun i => by
    fin_cases i
    · exact mul_ne_zero (hz 2 (by decide)) (hl 2 (by decide))
    · exact mul_ne_zero (hz 3 (by decide)) (hl 3 (by decide))
    · exact mul_ne_zero (hz 4 (by decide)) (hl 4 (by decide))
  have heig : ∀ i, IsEigenfield R (mus i) (P i) := fun i => by
    fin_cases i
    exacts [he2, he3, he4]
  obtain ⟨sg, ε, hε, p0, p1, n2⟩ := sign_perm (fun r => mus r * (mus r - ev 1)) hw hmix
  refine ⟨sg, ε, hε, fun i j => h3 _ _, fun i => heig _, fun x i k hik => ?_, fun x i => ?_, p0, p1, n2,
    fun a b => ?_⟩
  · simpa [hik] using horth x (sg i) (sg k)
  · simpa using horth x (sg i) (sg i)
  · have e : ∑ i, C (ε * (mus (sg i) * (mus (sg i) - ev 1))) * P (sg i) a * P (sg i) b =
        C ε * ∑ i, C (mus i * (mus i - ev 1)) * P i a * P i b := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv sg _ _ fun i => by simp only [map_mul]; ring
    exact (congrArg (sqP 16 ∣ ·) e).mpr (Dvd.dvd.mul_left (hd a b) _)

end Osserman.Proofs.S85
