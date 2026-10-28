/-
Six4d.lean — Theorem G of paper 013 (§9.4, sec_polynomial_gram.tex of the posting copy, lines 237-267), batch 4:
row thm_G_conclude ("So the full Gram is $G(s)=(s^2+d)I$").
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Premise row of thm_G_conclude (leading argument with its exact type): thm_G_spectral_pencil (`PencilHyp` below).
Proof. The shift (thm_G_shift) gives `ν = 15 - m ≤ 8` and `Λ = diag(μ)` definite; the image condition it asks for
follows from `J'_X = M_XΛM_Xᵀ`, `M_XᵀM_X = I` and `Λ` invertible (`range_frame`). The field `𝔼 = 𝔽(α)`, `α² = -d`, is
`𝔽[s]/(s² + d)` (a field: `-d` is not a square in `𝔽`). Then thm_G_G_alpha_zero and thm_G_Phi_scalar give `Φ₁ = 0` and
`Φ₀ = dI`, so `G(s) = s²I + dI`.
-/
import Osserman.Proofs.Six4c

namespace Osserman.Proofs.Six4d

open Osserman Matrix

/-- The type of row `thm_G_spectral_pencil`. -/
abbrev PencilHyp : Prop :=
  ∀ (R : CurvTensor 16) (_hO : R.IsOsserman) (μ0 : ℝ) {ν : ℕ} (μ : Fin ν → ℝ) (_hμ : ∀ i, μ i ≠ 0) (Xa : Vec 16)
    (f : Fin 15 → Vec 16) (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15)
    (_hP : IsRationalPartner R μ0 (diagonal μ) Xa f MX MY), SpectralPencil μ (Phi1 MX MY) (Phi0 MY)

/-- `M_X` and `M_XΛM_Xᵀ` have the same image when `M_XᵀM_X = I` and `Λ` is invertible. -/
lemma range_frame {ν : ℕ} (MX : Matrix (Fin 16) (Fin ν) ℝ) (Λ : Matrix (Fin ν) (Fin ν) ℝ) (hMX : MXᵀ * MX = 1)
    (hΛ : IsUnit Λ.det) :
    LinearMap.range (Matrix.toLin' MX) = LinearMap.range (Matrix.toLin' (MX * Λ * MXᵀ)) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
    have h : MX * Λ * MXᵀ * MX * Λ⁻¹ = MX := by
      rw [Matrix.mul_assoc (MX * Λ) MXᵀ MX, hMX, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_nonsing_inv (h := hΛ),
        Matrix.mul_one]
    refine LinearMap.mem_range.2 ⟨MX *ᵥ (Λ⁻¹ *ᵥ v), ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  · intro y hy
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.1 hy
    refine LinearMap.mem_range.2 ⟨(Λ * MXᵀ) *ᵥ v, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc]

/-- "Let $\mathbb E=\mathbb F(\alpha)$ with $\alpha^2=-d$" (pg l. 252): such a field exists, `𝔽[s]/(s² + d)`. -/
lemma exists_field_alpha : ∃ (𝔼 : Type) (_ : Field 𝔼) (_ : Algebra RatF15 𝔼) (α : 𝔼),
    α ^ 2 = -algebraMap RatF15 𝔼 dF ∧ IntermediateField.adjoin RatF15 {α} = ⊤ := by
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Polynomial.natDegree_X_pow_add_C]
      decide
    · intro c hc
      rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hc
      exact Six4.dF_not_sq c (by linear_combination hc)
  have : Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15)) := ⟨hirr⟩
  refine ⟨AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15), inferInstance, inferInstance,
    AdjoinRoot.root _, ?_, IntermediateField.adjoin_root_eq_top _⟩
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15)
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ← AdjoinRoot.algebraMap_eq] at h
  linear_combination h

/-- **Theorem G, proof** (lines 265-267 of sec_polynomial_gram.tex), row `thm_G_conclude`: `Φ₁ = 0`, `Φ₀ = dI`, and
"the full Gram is $G(s)=(s^2+d)I$". -/
theorem thm_G_conclude_proved (hpencil : PencilHyp) (R : CurvTensor 16) (hO : R.IsOsserman) (μ0 : ℝ)
    (hext : IsExtremeSevenEight R μ0) {ν : ℕ} (μ : Fin ν → ℝ) (hμ : ∀ i, μ i ≠ 0) (Xa : Vec 16)
    (f : Fin 15 → Vec 16) (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15)
    (hP : IsRationalPartner R μ0 (diagonal μ) Xa f MX MY) :
    Phi1 MX MY = 0 ∧ Phi0 MY = dF • (1 : Matrix (Fin ν) (Fin ν) RatF15) ∧
      GramS (Phi1 MX MY) (Phi0 MY) =
        (Polynomial.X ^ 2 + Polynomial.C dF) • (1 : Matrix (Fin ν) (Fin ν) (Polynomial RatF15)) := by
  obtain ⟨⟨m, hm, hmult⟩, hsl⟩ := hext
  obtain ⟨hX, -, -, hMX, hJ, -⟩ := id hP
  -- the shift: `ν = 15 - m ≤ 8` and `Λ = diag(μ)` definite
  have hdet : IsUnit (diagonal μ).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hμ i
  have hrange := range_frame MX (diagonal μ) hMX hdet
  rw [← hJ] at hrange
  obtain ⟨hνm, hsm, hlg⟩ := (Six4.thm_G_shift_proved R hO μ0 m hm hmult).2.2.2 Xa hX ν MX (diagonal μ) hMX hrange hJ
  have hν : ν ≤ 8 := by omega
  have hdef : (∀ i, 0 < μ i) ∨ ∀ i, μ i < 0 := by
    rcases hsl with h | h
    · exact Or.inl (Matrix.posDef_diagonal_iff.1 (hsm h))
    · have h' := hlg h
      rw [Matrix.diagonal_neg, Matrix.posDef_diagonal_iff] at h'
      exact Or.inr fun i => neg_pos.1 (h' i)
  -- the anisotropy step over `𝔼 = 𝔽(α)`
  obtain ⟨-, h1s, h0s⟩ := Six4.thm_G_gram_pencil_proved MX MY hMX
  have hspec := hpencil R hO μ0 μ hμ Xa f MX MY hP
  obtain ⟨𝔼, _, _, α, hα, hgen⟩ := exists_field_alpha
  have hG := (Six4.thm_G_G_alpha_zero_proved hν μ hdef (Phi1 MX MY) (Phi0 MY) h1s h0s hspec 𝔼 α hα hgen).2
  obtain ⟨-, h1, h0⟩ := Six4.thm_G_Phi_scalar_proved (Phi1 MX MY) (Phi0 MY) 𝔼 α hα hgen hG
  -- "So the full Gram is G(s) = (s² + d)I"
  refine ⟨h1, h0, ?_⟩
  rw [h1, h0]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [GramS]
  · simp [GramS, hij]

end Osserman.Proofs.Six4d
