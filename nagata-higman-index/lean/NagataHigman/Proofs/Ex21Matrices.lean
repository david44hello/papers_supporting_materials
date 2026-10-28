/-
  NagataHigman/Proofs/Ex21Matrices.lean - the explicit 2x2 matrix facts of the Example λ = (2,1) (paper 011 v1.10
  FINAL, md5 23b0bd3e, v1.10 l. 500-514; claim N11). The link to the Young system is NagataHigman/Proofs/Ex21Link.lean.
  Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

  s = √3. rho12 = diag(1,-1), rho23 = [[-1/2, s/2], [s/2, 1/2]], Gamma0 = [[0,1],[-1,0]].
  (1) Coxeter relations: entrywise, with s² = 3 (rho12·rho23 is the rotation by 2π/3).
  (2) G anticommutes with rho12 ⇔ G is off-diagonal; then anticommuting with rho23 ⇔ G₁₀ = -G₀₁ (as s ≠ 0), i.e. G = G₀₁·Gamma0.
  (3) Gamma0² = -1.  (4) (c·Gamma0)² = -c²·1, so G² = 1 ⇔ c² = -1 ⇔ c = ±i.
  (5) Over ℝ the same computation gives G = c·Gamma0 with c real and G² = -c² ≠ 1.
  (6) The six traces, entrywise.
-/
import Mathlib

open Matrix Complex

namespace NagataHigman.Proofs.Ex21

noncomputable def rho12 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
noncomputable def rho23 : Matrix (Fin 2) (Fin 2) ℂ := !![-1/2, (Real.sqrt 3 : ℂ) / 2; (Real.sqrt 3 : ℂ) / 2, 1/2]
def Gamma0 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem sqrt3_sq : ((Real.sqrt 3 : ℂ)) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem sqrt3_cube : ((Real.sqrt 3 : ℂ)) ^ 3 = 3 * (Real.sqrt 3 : ℂ) := by
  rw [pow_succ, sqrt3_sq]

theorem sqrt3_ne : ((Real.sqrt 3 : ℂ)) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))

/-- (1) The Coxeter relations of `S_3`. -/
theorem ex21_coxeter : rho12 * rho12 = 1 ∧ rho23 * rho23 = 1 ∧ (rho12 * rho23) ^ 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rho12, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rho23, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
      simp only [sqrt3_sq] <;> norm_num
  · ext i j
    rw [pow_three]
    fin_cases i <;> fin_cases j <;> simp [rho12, rho23, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
      simp only [sqrt3_sq, sqrt3_cube] <;> ring_nf

/-- Entries of `G` from the two anticommutation relations: `G = G₀₁ • Gamma0`. -/
theorem anticomm_entries {G : Matrix (Fin 2) (Fin 2) ℂ} (h1 : G * rho12 = -(rho12 * G))
    (h2 : G * rho23 = -(rho23 * G)) : G = G 0 1 • Gamma0 := by
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have f00 := congrFun (congrFun h2 0) 0
  simp [rho12, rho23, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e00 e11 f00
  have a00 : G 0 0 = 0 := by linear_combination (1/2 : ℂ) * e00
  have a11 : G 1 1 = 0 := by linear_combination (-1/2 : ℂ) * e11
  have h10 : G 1 0 = -G 0 1 := by
    have hs := sqrt3_ne
    have key : (Real.sqrt 3 : ℂ) * (G 1 0 + G 0 1) = 0 := by linear_combination 2 * f00 + 2 * a00
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hs
    · linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gamma0, a00, a11, h10]

/-- (2) The anticommutant of `rho12` and `rho23` is `ℂ · Gamma0`. -/
theorem ex21_anticommutant (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (G * rho12 = -(rho12 * G) ∧ G * rho23 = -(rho23 * G)) ↔ ∃ c : ℂ, G = c • Gamma0 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨G 0 1, anticomm_entries h1 h2⟩
  · rintro ⟨c, rfl⟩
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [rho12, rho23, Gamma0, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- (3) `Gamma0² = -1`. -/
theorem ex21_Gamma0_sq : Gamma0 * Gamma0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gamma0, Matrix.mul_apply, Fin.sum_univ_two]

/-- (4) The anticommuting `G` with `G² = 1` are exactly `± i Gamma0`. -/
theorem ex21_Gamma (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (G * rho12 = -(rho12 * G) ∧ G * rho23 = -(rho23 * G) ∧ G * G = 1) ↔ (G = I • Gamma0 ∨ G = -I • Gamma0) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hG := anticomm_entries h1 h2
    set c := G 0 1 with hc
    rw [hG] at h3
    have e := congrFun (congrFun h3 0) 0
    simp [Gamma0, Matrix.mul_apply, Fin.sum_univ_two] at e
    have key : (c - I) * (c + I) = 0 := by linear_combination (-1 : ℂ) * e - Complex.I_sq
    rcases mul_eq_zero.mp key with h | h
    · left; rw [hG, sub_eq_zero.mp h]
    · right; rw [hG, eq_neg_of_add_eq_zero_left h]
  · rintro (rfl | rfl) <;> refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [rho12, rho23, Gamma0, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- (5) Over `ℝ` no `G` anticommutes with both real matrices and squares to `1`. -/
theorem ex21_needs_C (G : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ (G * !![1, 0; 0, -1] = -(!![1, 0; 0, -1] * G) ∧
       G * !![-1/2, Real.sqrt 3 / 2; Real.sqrt 3 / 2, 1/2] = -(!![-1/2, Real.sqrt 3 / 2; Real.sqrt 3 / 2, 1/2] * G) ∧
       G * G = 1) := by
  rintro ⟨h1, h2, h3⟩
  have e00 := congrFun (congrFun h1 0) 0
  have e11 := congrFun (congrFun h1 1) 1
  have f00 := congrFun (congrFun h2 0) 0
  have g00 := congrFun (congrFun h3 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at e00 e11 f00 g00
  have a00 : G 0 0 = 0 := by linarith
  have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have key : Real.sqrt 3 * (G 1 0 + G 0 1) = 0 := by linear_combination 2 * f00 + 2 * a00
  have h10 : G 1 0 = -G 0 1 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h hs
    · linear_combination h
  rw [a00, h10] at g00
  nlinarith [sq_nonneg (G 0 1)]

/-- (6) The character values of `ψ(σ) = tr(ρ(σ) Γ)`, `Γ = i Gamma0`. -/
theorem ex21_psi :
    trace (I • Gamma0) = 0 ∧ trace (rho12 * (I • Gamma0)) = 0 ∧ trace (rho23 * (I • Gamma0)) = 0 ∧
    trace (rho12 * rho23 * rho12 * (I • Gamma0)) = 0 ∧
    trace (rho12 * rho23 * (I • Gamma0)) = -I * (Real.sqrt 3 : ℂ) ∧
    trace (rho23 * rho12 * (I • Gamma0)) = I * (Real.sqrt 3 : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.trace, Fin.sum_univ_two, rho12, rho23, Gamma0] <;> ring

end NagataHigman.Proofs.Ex21
