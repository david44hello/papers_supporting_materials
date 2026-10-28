/-
S85Clif.lean — §8.5 of paper 013 (sec_small_roots.tex of the posting copy, lines 252-294): the conclusion: rows
s8_5_clifford and s8_5_pattern_clifford.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Premise rows (leading arguments with their exact types): s8_cubic_identities (`CubicIdHyp`), s8_spectral_identity
(`SpecIdHyp`), lem_8_2_div_q (`DivQHyp`), s8_tc_outcome (`S84.OutcomeHyp`), s8_move_eigenfield (`MoveHyp`),
s8_3_pattern_clifford (`Pat83Hyp`), s8_move_frame (`MoveFrameHyp`).
Proof (the paper's). Equal signs: every field is `q` times a linear eigenfield (`s8_5_same_sign`, Lemma 8.2's first
step), and the linear case applies. Mixed signs: the three-column reduction (`s8_5_three_col`) ends in a linear column
(linear case) or a constant combination `c_1P_a + c_2P_b = qJx` of two columns. Then, with the simple eigenvalues
relabelled so that `μ_a, μ_b` come first (the pattern does not see the order), `z` is chosen (`s8_5_choose_z`), the
endpoint `R - CR_J` has the multiplicities of `s8_5_endpoint_mult`, its pattern is in the table
(`s8_5_endpoint_table`), it is Clifford (`s8_5_endpoint_clifford`), and [Nik2006, Lemma 3.2(1)] restores `R`.
-/
import Osserman.Proofs.S85Mult
import Osserman.Proofs.S85Ends
import Osserman.Proofs.S84Move
import Osserman.Proofs.S8TCAlgebra

namespace Osserman.Proofs.S85

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.S83

/-! ### Relabelling the three simple eigenvalues -/

lemma idx_inj : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    Function.Injective (![0, 1, (![2, 3, 4] : Fin 3 → Fin 5) a, (![2, 3, 4] : Fin 3 → Fin 5) b,
      (![2, 3, 4] : Fin 3 → Fin 5) c] : Fin 5 → Fin 5) := by
  decide

/-- The pattern `(M,N,1,1,1)` does not see the order of the three simple eigenvalues (review a3 NIT-6). -/
lemma relabel {R : CurvTensor 16} {M N : ℕ} {ev : Fin 5 → ℝ} (hR : PatternEv R ![M, N, 1, 1, 1] ev)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    PatternEv R ![M, N, 1, 1, 1] ![ev 0, ev 1, (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) a,
      (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) b, (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) c] := by
  have hmus (i : Fin 3) : (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i = ev ((![2, 3, 4] : Fin 3 → Fin 5) i) := by
    fin_cases i <;> rfl
  have hone (i : Fin 3) (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
      R.redMult x ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i) = 1 := by
    rw [hmus i, hR.2 x hx]
    fin_cases i <;> rfl
  refine ⟨inj_comp hR.1 _ (idx_inj a b c hab hac hbc) ?_, fun x hx j => ?_⟩
  · funext j
    fin_cases j
    exacts [rfl, rfl, hmus a, hmus b, hmus c]
  · fin_cases j
    exacts [hR.2 x hx 0, hR.2 x hx 1, hone a x hx, hone b x hx, hone c x hx]

/-! ### The endpoints of the table are Clifford -/

/-- From the multiplicities of `s8_5_endpoint_mult` to a Clifford endpoint, cell by cell of the table. -/
lemma endpoints_clifford (h83 : Pat83Hyp) (R' : CurvTensor 16) (M N : ℕ) (lam mu3 z θ : ℝ)
    (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) (hdist : 0 ≠ lam ∧ 0 ≠ mu3 ∧ lam ≠ mu3) (hz : z = 0 ∨ z = lam)
    (hmult : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ ν : ℝ, R'.redMult x ν =
      (if ν = 0 then M else 0) + (if ν = lam then N else 0) + (if ν = mu3 then 1 else 0) +
        (if ν = z then 1 else 0) + (if ν = θ then 1 else 0)) :
    R'.IsClifford := by
  obtain ⟨T1, T2, T3, T4⟩ := s8_5_endpoint_table_proved R' M N lam mu3 z θ hdist hz hmult
  have E := s8_5_endpoint_clifford_proved h83 R'
  rcases hMN with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hz with hz | hz
  · obtain ⟨cn, cm, cl, c0⟩ := T1 ⟨rfl, rfl, hz⟩
    by_cases h1 : θ = mu3
    · exact E (by simp [cm h1])
    by_cases h2 : θ = 0
    · exact E (by simp [c0 h2])
    by_cases h3 : θ = lam
    · exact E (by simp [cl h3])
    exact E (by simp [cn h2 h3 h1])
  · obtain ⟨cn, cm, c0, cl⟩ := T2 ⟨rfl, rfl, hz⟩
    by_cases h1 : θ = mu3
    · exact E (by simp [cm h1])
    by_cases h2 : θ = 0
    · exact E (by simp [c0 h2])
    by_cases h3 : θ = lam
    · exact E (by simp [cl h3])
    exact E (by simp [cn h2 h3 h1])
  · obtain ⟨cn, cm, cl, c0⟩ := T3 ⟨rfl, rfl, hz⟩
    by_cases h1 : θ = mu3
    · exact E (by simp [cm h1])
    by_cases h2 : θ = 0
    · exact E (by simp [c0 h2])
    by_cases h3 : θ = lam
    · exact E (by simp [cl h3])
    exact E (by simp [cn h2 h3 h1])
  · obtain ⟨cn, cm, c0, cl⟩ := T4 ⟨rfl, rfl, hz⟩
    by_cases h1 : θ = mu3
    · exact E (by simp [cm h1])
    by_cases h2 : θ = 0
    · exact E (by simp [c0 h2])
    by_cases h3 : θ = lam
    · exact E (by simp [cl h3])
    exact E (by simp [cn h2 h3 h1])

/-! ### The mixed case: a combination of two columns -/

lemma mixed_endpoint (hFrame : MoveFrameHyp) (h83 : Pat83Hyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 5 → ℝ}
    {P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec85Data R M N ev P) (a b c : Fin 3) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ) (hc : c1 ^ 2 + c2 ^ 2 = 1)
    (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : ∀ x : Vec 16, c1 • evalField (P a) x + c2 • evalField (P b) x = (x ⬝ᵥ x) • (J *ᵥ x)) :
    R.IsClifford := by
  obtain ⟨hMN, hR, h0, -, hC, he2, he3, he4⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts5 hMN
  have hsum16 : ∑ i, (![M, N, 1, 1, 1] : Fin 5 → ℕ) i + 1 = 16 := by omega
  have hO : R.IsOsserman := (CorD.hasPattern_osserman_proved R _ hsum16 ⟨ev, hR⟩).1
  have heig (i : Fin 3) : IsEigenfield R ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i) (P i) := by
    fin_cases i
    exacts [he2, he3, he4]
  have hne (i j : Fin 5) (hij : i ≠ j) : ev i ≠ ev j := fun e => hij (hR.1 e)
  have hlam : ev 1 ≠ 0 := fun e => absurd (hR.1 (e.trans h0.symm)) (by decide)
  have hmz (i : Fin 3) : (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i ≠ 0 ∧ (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i ≠ ev 1 := by
    fin_cases i
    · exact ⟨h0 ▸ hne 2 0 (by decide), hne 2 1 (by decide)⟩
    · exact ⟨h0 ▸ hne 3 0 (by decide), hne 3 1 (by decide)⟩
    · exact ⟨h0 ▸ hne 4 0 (by decide), hne 4 1 (by decide)⟩
  obtain ⟨z, hz, hdz, hCc⟩ := s8_5_choose_z_proved (ev 1) ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) a)
    ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) b)
    ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) a * c2 ^ 2 + (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) b * c1 ^ 2) hlam (hmz a) (hmz b)
  obtain ⟨R', hop, hO', hdist, hmult⟩ := s8_5_endpoint_mult_proved hFrame R M N hMN _ (relabel hR a b c hab hac hbc)
    h0 ![P a, P b] (fun i x => by fin_cases i; exacts [(hC a x).2.1, (hC b x).2.1]) ⟨heig a, heig b⟩ c1 c2 hc J hJ
    z hz hdz
  have hC' := endpoints_clifford h83 R' M N _ _ z _ hMN hdist hz hmult
  exact Osserman.Proofs.Rem72c.lem_nik_3_2_1_proved R R' J hJs hJo _ hCc hop hO hO' hC'

/-! ### The rows -/

/-- **§8.5, conclusion** (lines 252-294), row `s8_5_clifford`. -/
theorem s8_5_clifford_proved (hSpec : SpecIdHyp) (hdiv : DivQHyp) (hOut : S84.OutcomeHyp) (hMove : MoveHyp)
    (h83 : Pat83Hyp) (hFrame : MoveFrameHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) : R.IsClifford := by
  by_cases hs : (∀ i, 0 < (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1)) ∨
      ∀ i, (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1) < 0
  · have hq := s8_5_same_sign_proved hSpec R M N ev P h hs
    obtain ⟨J, hJP, -, hJs, hJo⟩ := hdiv (P 0) (h.2.2.2.1 0) (h.2.2.2.2.1 0) (hq 0)
    exact s8_5_linear_case_proved hMove h83 R M N ev P h 0 J hJs hJo
      (eigenfield_linP h.2.2.2.2.2.1 J (evalField_of_eq hJP))
  · obtain ⟨sg, ε, -, hTC⟩ := s8_5_three_col_proved hSpec R M N ev P h hs
    rcases hOut R _ _ _ hTC (h.2.2.2.2.1 (sg 2)) with ⟨i, J, hJs, hJo, -, hJe⟩ | ⟨c1, c2, J, hc, hJs, hJo, hJ⟩
    · exact s8_5_linear_case_proved hMove h83 R M N ev P h (sg i) J hJs hJo hJe
    · exact mixed_endpoint hFrame h83 h (sg 0) (sg 1) (sg 2) (sg.injective.ne (by decide))
        (sg.injective.ne (by decide)) (sg.injective.ne (by decide)) c1 c2 J hc hJs hJo hJ

/-- **§8.5 = Theorem F for `(7,5,1,1,1)` and `(8,4,1,1,1)`** (lines 6-11 and 252-294), row
`s8_5_pattern_clifford`: shift the multiplicity-`M` eigenvalue to zero, take the fields, conclude. -/
theorem s8_5_pattern_clifford_proved (hcub : CubicIdHyp) (hSpec : SpecIdHyp) (hdiv : DivQHyp)
    (hOut : S84.OutcomeHyp) (hMove : MoveHyp) (h83 : Pat83Hyp) (hFrame : MoveFrameHyp) (R : CurvTensor 16)
    (h : HasPattern R ![7, 5, 1, 1, 1] ∨ HasPattern R ![8, 4, 1, 1, 1]) : R.IsClifford := by
  have main (M N : ℕ) (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) (hp : HasPattern R ![M, N, 1, 1, 1]) :
      R.IsClifford := by
    obtain ⟨ev, hev⟩ := hp
    obtain ⟨R0, -, -, hR0, -, -, hCl⟩ := S8TC.s8_shift_to_zero_proved R _ ev hev 0
    obtain ⟨P, hP⟩ := s8_5_fields_proved hcub R0 M N hMN _ hR0 (sub_self (ev 0))
    exact hCl.mp (s8_5_clifford_proved hSpec hdiv hOut hMove h83 hFrame R0 M N _ P hP)
  rcases h with h | h
  · exact main 7 5 (Or.inl ⟨rfl, rfl⟩) h
  · exact main 8 4 (Or.inr ⟨rfl, rfl⟩) h

end Osserman.Proofs.S85
