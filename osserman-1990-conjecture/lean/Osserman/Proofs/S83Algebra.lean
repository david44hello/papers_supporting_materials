/-
Osserman/Proofs/S83Algebra.lean — §8.3 of paper 013, opposite signs: the real algebra of the constant `C` and of the
changed 2×2 block (rows s8_3_C_ne_zero, s8_3_block_algebra; statements copied verbatim from
Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. With `a² = μ(μ-λ)` and `b² = -σ(σ-λ)`: `a² + b² = μ² - σ² - λ(μ-σ) = (μ-σ)(μ+σ-λ)`, and `a² + b² > 0`, so
`C = μ+σ-λ ≠ 0`. The block `B = diag(μ,σ) - (C/S)·(a,-b)(a,-b)ᵀ`, `S = a² + b²`, is symmetric with trace
`μ + σ - C = λ` and determinant `(μ - Ca²/S)(σ - Cb²/S) - C²a²b²/S² = μσ - C(σa² + μb²)/S`; and
`σa² + μb² = μσ(μ-σ)`, so the determinant is `μσ - μσ(μ-σ)C/((μ-σ)C) = 0`.
-/
import Osserman.Defs.SmallRoots

namespace Osserman.Proofs.S83

open Matrix

/-- Row `s8_3_C_ne_zero`. -/
theorem s8_3_C_ne_zero_proved (lam mu sig a b : ℝ) (hms : mu ≠ sig) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = mu * (mu - lam)) (hb2 : b ^ 2 = -(sig * (sig - lam))) :
    a ^ 2 + b ^ 2 = (mu - sig) * (mu + sig - lam) ∧ mu + sig - lam ≠ 0 := by
  clear hms
  have hsum : a ^ 2 + b ^ 2 = (mu - sig) * (mu + sig - lam) := by rw [ha2, hb2]; ring
  refine ⟨hsum, fun hC => ?_⟩
  have hpos : 0 < a ^ 2 + b ^ 2 := by positivity
  rw [hsum, hC, mul_zero] at hpos
  exact lt_irrefl 0 hpos

/-- Row `s8_3_block_algebra`. -/
theorem s8_3_block_algebra_proved (lam mu sig a b : ℝ) (hms : mu ≠ sig) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = mu * (mu - lam)) (hb2 : b ^ 2 = -(sig * (sig - lam))) :
    let Cc := mu + sig - lam
    let B2 : Matrix (Fin 2) (Fin 2) ℝ := !![mu, 0; 0, sig] - (Cc / (a ^ 2 + b ^ 2)) • vecMulVec ![a, -b] ![a, -b]
    B2ᵀ = B2 ∧ B2.trace = lam ∧ B2.det = mu * sig - Cc * (sig * a ^ 2 + mu * b ^ 2) / (a ^ 2 + b ^ 2) ∧
      sig * a ^ 2 + mu * b ^ 2 = mu * sig * (mu - sig) ∧ B2.det = 0 := by
  intro Cc B2
  obtain ⟨hsum, hC⟩ := s8_3_C_ne_zero_proved lam mu sig a b hms ha hb ha2 hb2
  have hS : a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hms' : mu - sig ≠ 0 := sub_ne_zero.mpr hms
  have hsa : sig * a ^ 2 + mu * b ^ 2 = mu * sig * (mu - sig) := by rw [ha2, hb2]; ring
  have hdet : B2.det = mu * sig - Cc * (sig * a ^ 2 + mu * b ^ 2) / (a ^ 2 + b ^ 2) := by
    simp only [B2, Cc, Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    simp
    field_simp
    ring
  refine ⟨?_, ?_, hdet, hsa, ?_⟩
  · ext i j
    simp only [B2, Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [mul_comm]
  · simp only [B2, Cc, Matrix.trace_fin_two, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    simp
    field_simp
    ring
  · rw [hdet, hsa, hsum]
    field_simp
    ring

end Osserman.Proofs.S83
