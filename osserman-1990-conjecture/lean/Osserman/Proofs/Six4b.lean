/-
Osserman/Proofs/Six4b.lean — Theorem G (paper 013, §9.4, sec_polynomial_gram.tex l. 237-267), batch 2: the eight-squares
lemma (from the cited `nik2006_lemma_3_11`), anisotropy of definite real forms over `𝔼`, and `G(α) = 0`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.Six4a
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.Six4

open Osserman Matrix

/-! ### thm_G_eight_squares (cited input: `nik2006_lemma_3_11`) -/

theorem thm_G_eight_squares_proved (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    ∀ k : ℕ, k ≤ 8 → ∀ v : Fin k → 𝔼, ∑ i, v i ^ 2 = 0 → ∀ i, v i = 0 := by
  intro k hk v hv
  obtain ⟨φ, -, hfrac⟩ := thm_G_fraction_field_proved 𝔼 α hα hgen
  let _ : Algebra (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 := φ.toAlgebra
  have hfr : IsFractionRing (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 := hfrac
  have : Nontrivial (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) := φ.domain_nontrivial
  classical
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16})) Finset.univ v
  choose P hP using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
  set B := algebraMap (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 b with hB
  have hb0 : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hP' : ∀ i, algebraMap (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 (P i) = B * v i :=
    fun i => by rw [hP i, Algebra.smul_def]
  have hsum : algebraMap (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 (∑ i, P i ^ 2) = 0 := by
    rw [map_sum]
    simp only [map_pow, hP', mul_pow, ← Finset.mul_sum, hv, mul_zero]
  have h0 : ∑ i, P i ^ 2 = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 (by rw [hsum, map_zero])
  choose Pt hPt using fun i => Ideal.Quotient.mk_surjective (I := Ideal.span {sqP 16}) (P i)
  have hdvd : sqP 16 ∣ ∑ i, Pt i ^ 2 := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
    simp only [map_pow, hPt]
    exact h0
  have hdi := Osserman.Cited.nik2006_lemma_3_11 k hk Pt hdvd
  intro i
  have hPi : P i = 0 := by
    rw [← hPt i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hdi i))
  have h1 := hP' i
  rw [hPi, map_zero] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hb0

/-! ### thm_G_anisotropic -/

/-- A positive definite real matrix is `BᵀB` with `det B ≠ 0` (spectral theorem, `B = diag(√λ)Uᵀ`). -/
lemma posDef_eq_transpose_mul {k : ℕ} (H : Matrix (Fin k) (Fin k) ℝ) (hH : H.PosDef) :
    ∃ B : Matrix (Fin k) (Fin k) ℝ, H = Bᵀ * B ∧ B.det ≠ 0 := by
  classical
  have hA := hH.1
  have hUm : (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) ∈ unitary (Matrix (Fin k) (Fin k) ℝ) :=
    hA.eigenvectorUnitary.2
  have hspec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U : Matrix (Fin k) (Fin k) ℝ := (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℝ) with hU
  have hpos : ∀ i, 0 < hA.eigenvalues i := hH.eigenvalues_pos
  set D : Matrix (Fin k) (Fin k) ℝ := diagonal fun i => Real.sqrt (hA.eigenvalues i) with hD
  have hstar : star U = Uᵀ := by rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hDD : D * D = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [hD, diagonal_mul_diagonal]
    congr 1
    funext i
    simp [Real.mul_self_sqrt (hpos i).le]
  refine ⟨D * Uᵀ, ?_, ?_⟩
  · rw [transpose_mul, transpose_transpose, hD, diagonal_transpose, ← hD, ← hstar,
      show U * D * (D * star U) = U * (D * D) * star U by simp only [Matrix.mul_assoc], hDD]
    exact hspec
  · rw [det_mul, det_transpose, hD, det_diagonal]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => (Real.sqrt_pos.2 (hpos i)).ne') ?_
    have h1 := congrArg det (Unitary.mul_star_self_of_mem hUm)
    rw [det_mul, det_one] at h1
    exact left_ne_zero_of_mul_eq_one h1

theorem thm_G_anisotropic_proved (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    ∀ k : ℕ, k ≤ 8 → ∀ H : Matrix (Fin k) (Fin k) ℝ, (H.PosDef ∨ (-H).PosDef) →
      ∀ v : Fin k → 𝔼, v ⬝ᵥ (H.map ((algebraMap RatF15 𝔼).comp ofRealF) *ᵥ v) = 0 → v = 0 := by
  intro k hk H hH v hv
  have h8 := thm_G_eight_squares_proved 𝔼 α hα hgen k hk
  set ρ := (algebraMap RatF15 𝔼).comp ofRealF
  have key : ∀ G : Matrix (Fin k) (Fin k) ℝ, G.PosDef → v ⬝ᵥ (G.map ρ *ᵥ v) = 0 → v = 0 := by
    intro G hG hGv
    obtain ⟨B, rfl, hB⟩ := posDef_eq_transpose_mul G hG
    have e : v ⬝ᵥ ((Bᵀ * B).map ρ *ᵥ v) = ∑ i, ((B.map ρ) *ᵥ v) i ^ 2 := by
      rw [Matrix.map_mul, transpose_map, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      simp only [dotProduct, sq]
    have hBv : (B.map ρ) *ᵥ v = 0 := funext fun i => h8 _ (e ▸ hGv) i
    have hdet : (B.map ρ).det = ρ B.det := (RingHom.map_det ρ B).symm
    exact Matrix.eq_zero_of_mulVec_eq_zero (by rw [hdet]; exact (map_ne_zero ρ).2 hB) hBv
  rcases hH with h | h
  · exact key H h hv
  · have hneg : (-H).map ρ = -(H.map ρ) := by
      ext i j
      simp
    exact key (-H) h (by rw [hneg, neg_mulVec, dotProduct_neg, hv, neg_zero])

/-! ### thm_G_G_alpha_zero -/

theorem thm_G_G_alpha_zero_proved {ν : ℕ} (hν : ν ≤ 8) (μ : Fin ν → ℝ) (hdef : (∀ i, 0 < μ i) ∨ ∀ i, μ i < 0)
    (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) (h1 : Φ1ᵀ = Φ1) (h0 : Φ0ᵀ = Φ0) (hspec : SpectralPencil μ Φ1 Φ0)
    (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF)
    (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    (diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0 = 0 ∧
      Φ0.map (algebraMap RatF15 𝔼) - algebraMap RatF15 𝔼 dF • (1 : Matrix (Fin ν) (Fin ν) 𝔼) +
        α • Φ1.map (algebraMap RatF15 𝔼) = 0 := by
  have hμ : ∀ i, μ i ≠ 0 := fun i => hdef.elim (fun h => (h i).ne') (fun h => (h i).ne)
  obtain ⟨hinv, -, hadj⟩ := thm_G_self_adjoint_proved μ hμ Φ1 Φ0 h1 h0 𝔼 α
  have hnil := (thm_G_nilpotent_proved μ Φ1 Φ0 hspec 𝔼 α hα).2
  set ρ := (algebraMap RatF15 𝔼).comp ofRealF
  have hΛinv : ((diagonal μ).map ρ)⁻¹ = (diagonal fun i => (μ i)⁻¹).map ρ := by
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, diagonal_mul_diagonal]
    have hone : (fun i => (μ i)⁻¹ * μ i) = fun _ => (1 : ℝ) := funext fun i => inv_mul_cancel₀ (hμ i)
    rw [hone, diagonal_one, Matrix.map_one _ (map_zero ρ) (map_one ρ)]
  have hanis : ∀ v : Fin ν → 𝔼, v ⬝ᵥ (((diagonal μ).map ρ)⁻¹ *ᵥ v) = 0 → v = 0 := by
    rw [hΛinv]
    refine thm_G_anisotropic_proved 𝔼 α hα hgen ν hν _ ?_
    rcases hdef with h | h
    · left
      exact Matrix.posDef_diagonal_iff.2 fun i => inv_pos.2 (h i)
    · right
      rw [diagonal_neg]
      exact Matrix.posDef_diagonal_iff.2 fun i => neg_pos.2 (inv_lt_zero.2 (h i))
  have hN := thm_G_nilpotent_self_adjoint_zero_proved _ _ hanis hadj hnil
  refine ⟨hN, ?_⟩
  have hG : GramAt α Φ1 Φ0 = 0 := by rw [← hinv, hN, Matrix.mul_zero]
  rw [GramAt, hα, neg_smul] at hG
  rw [← hG]
  abel

end Osserman.Proofs.Six4
