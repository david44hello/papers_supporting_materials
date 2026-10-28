/-
Matsaev/Assembly/Basic.lean — small glue facts for assembling Theorem A (real ↔ complex, transpose of J).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import Matsaev.Defs.Spaces
import Matsaev.Bridge.Basic

namespace Matsaev.Assembly

open Matsaev
open scoped ENNReal Matrix
open Polynomial

/-- `P_a` over `ℝ`, mapped to `ℂ`, is `P_a` with the same (real) coefficients over `ℂ`. -/
theorem Pa_map (a B : ℝ) : (Pa a B).map (algebraMap ℝ ℂ) = Pa (a : ℂ) (B : ℂ) := by
  simp [Pa, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

/-- Mapping a real matrix to `ℂ` commutes with evaluating a real polynomial. -/
theorem aeval_map_complex {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℝ) (P : ℝ[X]) :
    aeval (T.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) = (aeval T P).map (algebraMap ℝ ℂ) := by
  rw [Polynomial.aeval_map_algebraMap]
  exact Polynomial.aeval_algHom_apply ((Algebra.ofId ℝ ℂ).mapMatrix : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℂ) T P

/-- `Jᵀ = -J`. -/
theorem Jmat_transpose (𝕜 : Type*) [CommRing 𝕜] : (Jmat : Matrix (Fin 2) (Fin 2) 𝕜)ᵀ = -Jmat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat]

/-- `P_a(Jᵀ) = (1 + B) I - a J`. -/
theorem aeval_Jmat_transpose_Pa (a B : ℝ) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ)ᵀ (Pa a B) = (1 + B) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - a • Jmat := by
  rw [Jmat_transpose]
  have hJJ : (-(Jmat : Matrix (Fin 2) (Fin 2) ℝ)) * -Jmat = -1 := by rw [neg_mul_neg, Jmat_mul_Jmat]
  simp only [Pa, map_add, map_sub, map_one, map_mul, aeval_C, aeval_X, sq, hJJ,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_neg]
  module

/-- `D = diag(1, -1)`. -/
def Dmat : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

theorem Dmat_mul_Dmat : Dmat * Dmat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dmat]

/-- `D` is an isometry of `ℓ^p_2` (`p < ∞`). -/
theorem norm_toLp_Dmat (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (x : Fin 2 → ℝ) :
    ‖WithLp.toLp p (Dmat *ᵥ x)‖ = ‖WithLp.toLp p x‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have h : ‖WithLp.toLp p (Dmat *ᵥ x)‖ ^ p.toReal = ‖WithLp.toLp p x‖ ^ p.toReal := by
    rw [norm_toLp_rpow p hptop, norm_toLp_rpow p hptop]
    simp [Dmat, Matrix.mulVec_diagonal, Fin.sum_univ_two]
  exact (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp.ne').mp h

/-- Conjugating by `D` does not change the `ℓ^p_2` operator norm (`p < ∞`). -/
theorem matNorm_Dmat_conj (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    matNorm p (Dmat * A * Dmat) = matNorm p A := by
  have key : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, matNorm p (Dmat * M * Dmat) ≤ matNorm p M := by
    intro M
    refine (matNorm_le_iff p _ (matNorm_nonneg p M)).mpr fun x => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, norm_toLp_Dmat p hptop, ← norm_toLp_Dmat p hptop x]
    exact norm_mulVec_le_matNorm p M (Dmat *ᵥ x)
  refine le_antisymm (key A) ?_
  have h := key (Dmat * A * Dmat)
  rwa [show Dmat * (Dmat * A * Dmat) * Dmat = A by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Dmat_mul_Dmat, Matrix.one_mul, Matrix.mul_assoc, Dmat_mul_Dmat,
      Matrix.mul_one]] at h

/-- `‖P_a(Jᵀ)‖_p = ‖P_a(J)‖_p` (`Jᵀ = -J = V J V`, `V = diag(1, -1)`; proof of Theorem 3.6, "The case 1 < p < 2"). -/
theorem matNorm_aeval_Jmat_transpose_Pa (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (a B : ℝ) :
    matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ)ᵀ (Pa a B)) =
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) := by
  rw [aeval_Jmat_transpose_Pa, aeval_Jmat_Pa_proved, ← matNorm_Dmat_conj p hptop ((1 + B) • 1 + a • Jmat)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dmat, Jmat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `2 < p` and `p < ∞` give `2 < p.toReal`. -/
theorem two_lt_toReal {p : ℝ≥0∞} (hp : 2 < p) (hptop : p ≠ ⊤) : 2 < p.toReal := by
  simpa using (ENNReal.toReal_lt_toReal (by simp) hptop).mpr hp

/-- `1 < p` and `p < ∞` give `1 < p.toReal`. -/
theorem one_lt_toReal {p : ℝ≥0∞} (hp : 1 < p) (hptop : p ≠ ⊤) : 1 < p.toReal := by
  simpa using (ENNReal.toReal_lt_toReal (by simp) hptop).mpr hp

/-- For `1 < p < ∞` the conjugate exponent `q = p/(p-1)` as an element of `ℝ≥0∞`. -/
theorem exists_conj (p : ℝ≥0∞) (hp : 1 < p) (hptop : p ≠ ⊤) :
    ∃ q : ℝ≥0∞, 1 ≤ q ∧ q ≠ ⊤ ∧ p.toReal.HolderConjugate q.toReal := by
  have h := Real.HolderConjugate.conjExponent (one_lt_toReal hp hptop)
  have hq : 0 ≤ Real.conjExponent p.toReal := h.symm.nonneg
  refine ⟨ENNReal.ofReal (Real.conjExponent p.toReal), ?_, ENNReal.ofReal_ne_top, ?_⟩
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h.symm.lt.le
  · rwa [ENNReal.toReal_ofReal hq]

/-- For conjugate exponents with `p < 2`: `2 < q` and `q < ∞`. -/
theorem conj_gt_two {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal) (hp : p < 2) :
    2 < q ∧ q ≠ ⊤ := by
  have hq1 : 1 < q.toReal := hpq.symm.lt
  have hqtop : q ≠ ⊤ := fun h => by rw [h, ENNReal.toReal_top] at hq1; linarith
  have hptop : p ≠ ⊤ := fun h => by simp [h] at hp
  have hp2 : p.toReal < 2 := by simpa using (ENNReal.toReal_lt_toReal hptop (by simp)).mpr hp
  have hp1 : 0 < p.toReal := hpq.pos
  have hsum := hpq.inv_add_inv_eq_one
  have hq2 : 2 < q.toReal := by
    have hpinv : 1 / 2 < p.toReal⁻¹ := by
      rw [one_div]; exact inv_strictAnti₀ hp1 hp2
    have hqinv : q.toReal⁻¹ < 1 / 2 := by linarith
    have hqpos : 0 < q.toReal := by linarith
    by_contra hcon
    have : 1 / 2 ≤ q.toReal⁻¹ := by
      rw [one_div]; exact inv_anti₀ hqpos (not_lt.mp hcon)
    linarith
  refine ⟨?_, hqtop⟩
  have h2 : (2 : ℝ≥0∞).toReal < q.toReal := by rw [ENNReal.toReal_ofNat]; exact hq2
  exact (ENNReal.toReal_lt_toReal (by simp) hqtop).mp h2

end Matsaev.Assembly
