/-
S85Ends.lean — §8.5 of paper 013 (sec_small_roots.tex of the posting copy, lines 264-294): the linear case and the endpoints:
rows s8_5_linear_endpoint, s8_5_linear_case, s8_5_endpoint_clifford, s8_5_10_4_1, s8_5_cl8_endpoints.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Premise rows (leading arguments with their exact types): s8_move_eigenfield (`MoveHyp` of S83Move.lean),
s8_3_pattern_clifford (`Pat83Hyp` below).
Proof. A linear eigenfield of a simple eigenvalue moved into `0` (`s8_move_eigenfield`) gives `(M+1,N,1,1)`, that is
`(8,5,1,1)` (Subsection 8.3) or `(9,4,1,1)` ([Nik2006, Proposition 2.1]); [Nik2006, Lemma 3.2(1)]
(`lem_nik_3_2_1`) restores `R`. The ten endpoints of the table are Clifford by Subsection 8.3, Theorem E (thm:D),
Proposition 2.1, or [Nik2005, Proposition 1] for `(10,4,1)` (`m = 10`, `ν = 5`). A Clifford structure (all `η ≠ 0`)
has base multiplicity `15 - ν` and `ν ≤ 8` (Remark 7.2), so a pattern with all multiplicities `≤ 7` forces `ν = 8`.
-/
import Osserman.Proofs.S85Fields
import Osserman.Proofs.S85Alg
import Osserman.Proofs.S83Move
import Osserman.Proofs.ThmEClosed
import Osserman.Cited.Nik2005

namespace Osserman.Proofs.S85

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools Osserman.Proofs.S83

/-- The type of row `s8_3_pattern_clifford`. -/
abbrev Pat83Hyp : Prop :=
  ∀ (R : CurvTensor 16) (_h : HasPattern R ![7, 6, 1, 1] ∨ HasPattern R ![8, 5, 1, 1]), R.IsClifford

/-! ### `(10,4,1)` and `ν = 8` -/

/-- **§8.5** (lines 289-291), row `s8_5_10_4_1`: [Nik2005, Proposition 1] with `m = 10`, `ν = 5`. -/
theorem s8_5_10_4_1_proved (R' : CurvTensor 16) (hpat : HasPattern R' ![10, 4, 1]) : R'.IsClifford := by
  have hsum : ∑ i, (![10, 4, 1] : Fin 3 → ℕ) i + 1 = 16 := by simp [Fin.sum_univ_succ]
  obtain ⟨hO, -⟩ := CorD.hasPattern_osserman_proved R' _ hsum hpat
  obtain ⟨ev, hev, hm⟩ := hpat
  obtain ⟨-, h1, h2⟩ := s8_5_nik2005_arith_proved
  have hmax : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x (ev 0) = 10 ∧ ∀ μ : ℝ, R'.redMult x μ ≤ 10 := by
    intro x hx
    refine ⟨hm x hx 0, fun μ => ?_⟩
    by_cases hin : ∃ i, μ = ev i
    · obtain ⟨i, rfl⟩ := hin
      rw [hm x hx i]
      fin_cases i <;> simp
    · rw [CorD.redMult_other R' hev hsum hx (hm x hx) (fun i h => hin ⟨i, h⟩)]
      omega
  obtain ⟨J, hJ, l0, η, hjac⟩ :=
    Osserman.Cited.nik2005_prop_1 R' hO 10 (ev 0) hmax (by simpa using h1) (by simpa using h2)
  exact ⟨_, J, hJ, l0, η, hjac⟩

/-- A Clifford structure with all `η_α ≠ 0` on a tensor whose multiplicities are all at most seven has `ν = 8`: the
base eigenvalue has multiplicity `15 - ν` (`Rem72d.clifford_multiplicity`) and `ν ≤ 8` (Remark 7.2). -/
lemma nu_eq_8_of_pattern {k : ℕ} (R' : CurvTensor 16) (m : Fin k → ℕ) (hsum : ∑ i, m i + 1 = 16)
    (h7 : ∀ i, m i ≤ 7) (hpat : HasPattern R' m) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ) (hη : ∀ α, η α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν = 8 := by
  classical
  obtain ⟨ev, hev, hm⟩ := hpat
  let x : Vec 16 := Pi.single 0 1
  have hx : x ⬝ᵥ x = 1 := by simp [x, dotProduct, Pi.single_apply]
  have formula := Rem72d.clifford_multiplicity R' Jα hJ l0 η hjac x hx l0
  have empty : Fintype.card {a : Fin ν // l0 + η a = l0} = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun a => hη a.1 (by linarith [a.2])⟩
  simp only [empty, ite_true, zero_add] at formula
  have upper := HurwitzRadon.rem_7_2_nu_le_8_proved Jα hJ
  by_cases hin : ∃ i, l0 = ev i
  · obtain ⟨i, rfl⟩ := hin
    have := hm x hx i
    have := h7 i
    omega
  · have := CorD.redMult_other R' hev hsum hx (hm x hx) (fun i h => hin ⟨i, h⟩)
    omega

/-- **§8.5** (lines 291-294), row `s8_5_cl8_endpoints`. -/
theorem s8_5_cl8_endpoints_proved (R' : CurvTensor 16)
    (hpat : HasPattern R' ![7, 7, 1] ∨ HasPattern R' ![7, 6, 1, 1] ∨ HasPattern R' ![7, 6, 2])
    {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hη : ∀ α, η α ≠ 0) (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν = 8 := by
  rcases hpat with h | h | h
  · exact nu_eq_8_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac
  · exact nu_eq_8_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac
  · exact nu_eq_8_of_pattern R' _ (by simp [Fin.sum_univ_succ]) (by decide) h Jα hJ l0 η hη hjac

/-! ### The endpoints -/

/-- **§8.5** (lines 288-291), row `s8_5_endpoint_clifford`: Subsection 8.3 for `(8,5,1,1)`, `(7,6,1,1)`; Theorem E
(thm:D) for `(8,5,2)`, `(7,6,2)`, `(8,6,1)`, `(7,7,1)`; Proposition 2.1 for `(9,4,1,1)`, `(9,4,2)`, `(9,5,1)`;
[Nik2005, Proposition 1] for `(10,4,1)`. -/
theorem s8_5_endpoint_clifford_proved (h83 : Pat83Hyp) (R' : CurvTensor 16)
    (hpat : HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![7, 6, 1, 1] ∨ HasPattern R' ![9, 4, 1, 1] ∨
      HasPattern R' ![8, 5, 2] ∨ HasPattern R' ![7, 6, 2] ∨ HasPattern R' ![9, 4, 2] ∨ HasPattern R' ![8, 6, 1] ∨
      HasPattern R' ![9, 5, 1] ∨ HasPattern R' ![7, 7, 1] ∨ HasPattern R' ![10, 4, 1]) :
    R'.IsClifford := by
  have hE := Osserman.Proofs.ThmEClosed.thm_E_of_lem_nik_3_2_1 Osserman.Proofs.Rem72c.lem_nik_3_2_1_proved R'
  rcases hpat with h | h | h | h | h | h | h | h | h | h
  · exact h83 R' (Or.inr h)
  · exact h83 R' (Or.inl h)
  · exact s8_prop21_uses_proved R' (Or.inr (Or.inr (Or.inr h)))
  · exact hE (Or.inr (Or.inr (Or.inl h)))
  · exact hE (Or.inr (Or.inr (Or.inr h)))
  · exact s8_prop21_uses_proved R' (Or.inr (Or.inr (Or.inl h)))
  · exact hE (Or.inr (Or.inl h))
  · exact s8_prop21_uses_proved R' (Or.inr (Or.inl h))
  · exact hE (Or.inl h)
  · exact s8_5_10_4_1_proved R' h

/-! ### A linear eigenfield of a simple eigenvalue -/

/-- Moving the linear eigenfield of the simple eigenvalue `ev i1` into `0`; `a`, `b` are the other two simple ones. -/
lemma move_simple (hMove : MoveHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 5 → ℝ}
    {P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec85Data R M N ev P)
    {J : Matrix (Fin 16) (Fin 16) ℝ} (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) (i1 a b : Fin 5)
    (hf : Function.Injective ![(0 : Fin 5), 1, a, b]) (hi0 : i1 ≠ 0) (h1 : (1 : Fin 5) ≠ i1) (ha : a ≠ i1)
    (ha0 : a ≠ 0) (hb : b ≠ i1) (hb0 : b ≠ 0) (hma : (![M, N, 1, 1, 1] : Fin 5 → ℕ) a = 1)
    (hmb : (![M, N, 1, 1, 1] : Fin 5 → ℕ) b = 1) (hJe : IsEigenfield R (ev i1) (linP J)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - ev i1 • RJfun J u v z) ∧ R'.IsOsserman ∧
      HasPattern R' ![M + 1, N, 1, 1] := by
  obtain ⟨hMN, hR, h0, -⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts5 hMN
  obtain ⟨R', hop, -, hO', hm⟩ := hMove R _ ev hR hsum J hJs hJo i1 0 hi0 hJe
  refine ⟨R', by simpa [h0] using hop, hO', ![0, ev 1, ev a, ev b],
    inj_comp hR.1 ![0, 1, a, b] hf (by funext j; fin_cases j <;> simp [h0]), fun x hx j => ?_⟩
  obtain ⟨-, h2, h3⟩ := hm x hx
  fin_cases j
  · simpa [h0] using h2
  · simpa using h3 1 h1 (by decide)
  · simpa [hma] using h3 a ha ha0
  · simpa [hmb] using h3 b hb hb0

lemma linear_move (hMove : MoveHyp) {R : CurvTensor 16} {M N : ℕ} {ev : Fin 5 → ℝ}
    {P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec85Data R M N ev P)
    {J : Matrix (Fin 16) (Fin 16) ℝ} (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) (i : Fin 3)
    (hJ : IsEigenfield R (![ev 2, ev 3, ev 4] i) (linP J)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - ![ev 2, ev 3, ev 4] i • RJfun J u v z) ∧
      R'.IsOsserman ∧ HasPattern R' ![M + 1, N, 1, 1] := by
  fin_cases i
  · exact move_simple hMove h hJs hJo 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl hJ
  · exact move_simple hMove h hJs hJo 3 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl hJ
  · exact move_simple hMove h hJs hJo 4 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl rfl hJ

/-- **§8.5** (lines 264-266), row `s8_5_linear_endpoint`. -/
theorem s8_5_linear_endpoint_proved (hMove : MoveHyp) (h83 : Pat83Hyp) (R : CurvTensor 16) (M N : ℕ)
    (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) (i : Fin 3)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : IsEigenfield R (![ev 2, ev 3, ev 4] i) (linP J)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - ![ev 2, ev 3, ev 4] i • RJfun J u v z) ∧
      HasPattern R' ![M + 1, N, 1, 1] ∧ (HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 1, 1]) ∧
      R'.IsClifford := by
  obtain ⟨R', hop, -, hpat⟩ := linear_move hMove h hJs hJo i hJ
  have hpat' : HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 1, 1] := by
    rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hpat
    · exact Or.inr hpat
  refine ⟨R', hop, hpat, hpat', ?_⟩
  rcases hpat' with hp | hp
  · exact h83 R' (Or.inr hp)
  · exact s8_prop21_uses_proved R' (Or.inr (Or.inr (Or.inr hp)))

/-- **§8.5** (lines 264-267), row `s8_5_linear_case`: restore by [Nik2006, Lemma 3.2(1)]. -/
theorem s8_5_linear_case_proved (hMove : MoveHyp) (h83 : Pat83Hyp) (R : CurvTensor 16) (M N : ℕ)
    (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) (i : Fin 3)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : IsEigenfield R (![ev 2, ev 3, ev 4] i) (linP J)) : R.IsClifford := by
  obtain ⟨R', hop, -, -, hC'⟩ := s8_5_linear_endpoint_proved hMove h83 R M N ev P h i J hJs hJo hJ
  obtain ⟨hMN, hR, h0, -⟩ := h
  obtain ⟨hsum, -⟩ := pattern_facts5 hMN
  have hsum16 : ∑ i, (![M, N, 1, 1, 1] : Fin 5 → ℕ) i + 1 = 16 := by omega
  have hO : R.IsOsserman := (CorD.hasPattern_osserman_proved R _ hsum16 ⟨ev, hR⟩).1
  have hz (j : Fin 5) (hj : j ≠ 0) : ev j ≠ 0 := fun e => hj (hR.1 (e.trans h0.symm))
  have hc : (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i ≠ 0 := by
    fin_cases i
    exacts [hz 2 (by decide), hz 3 (by decide), hz 4 (by decide)]
  exact Osserman.Proofs.Rem72c.lem_nik_3_2_1_proved R R' J hJs hJo _ hc hop hO (clifford_osserman hC') hC'

end Osserman.Proofs.S85
