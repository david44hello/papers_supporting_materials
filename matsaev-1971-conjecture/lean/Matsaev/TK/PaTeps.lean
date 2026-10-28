-- Matsaev/TK/PaTeps.lean — P_a(T_ε) = X(ε)·I + Y(ε)·J in closed form (Lemma 4.1, `lem:TK`), plus X, Y at ε = 0.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Spaces

/-!
`T_ε = e^(-εD/2) R_(ε/2) J` acts like the complex number `z = e^(-εD/2) e^(iε/2) i`, since `J² = -1`.
So `P_a(T_ε) = 1 + a z - B z²` with `z² = -e^(-εD) e^(iε)`; its real part is `Xe` and its imaginary part is `Ye`.
Here `D` is a free real parameter; in `aeval_Teps_Pa` it is `D_* = Dstar p`.
-/

namespace Matsaev
namespace TK

open Polynomial
open scoped Matrix

/-- The `I`-coefficient of `P_a(T_ε)`: `1 - a e^(-εD/2) sin(ε/2) + B e^(-εD) cos ε`. -/
noncomputable def Xe (D a B ε : ℝ) : ℝ :=
  1 - a * Real.exp (-(ε * D / 2)) * Real.sin (ε / 2) + B * Real.exp (-(ε * D)) * Real.cos ε

/-- The `J`-coefficient of `P_a(T_ε)`: `a e^(-εD/2) cos(ε/2) + B e^(-εD) sin ε`. -/
noncomputable def Ye (D a B ε : ℝ) : ℝ :=
  a * Real.exp (-(ε * D / 2)) * Real.cos (ε / 2) + B * Real.exp (-(ε * D)) * Real.sin ε

/-- `e^(-εD) = e^(-εD/2) · e^(-εD/2)`. -/
private theorem exp_neg_mul_eq (D ε : ℝ) :
    Real.exp (-(ε * D)) = Real.exp (-(ε * D / 2)) * Real.exp (-(ε * D / 2)) := by
  rw [← Real.exp_add]
  ring_nf

/-- `cos ε = cos²(ε/2) - sin²(ε/2)`. -/
private theorem cos_eq_half (ε : ℝ) : Real.cos ε = Real.cos (ε / 2) ^ 2 - Real.sin (ε / 2) ^ 2 := by
  have h := Real.cos_two_mul (ε / 2)
  rw [show 2 * (ε / 2) = ε by ring] at h
  linear_combination h + Real.sin_sq_add_cos_sq (ε / 2)

/-- `sin ε = 2 sin(ε/2) cos(ε/2)`. -/
private theorem sin_eq_half (ε : ℝ) : Real.sin ε = 2 * Real.sin (ε / 2) * Real.cos (ε / 2) := by
  have h := Real.sin_two_mul (ε / 2)
  rwa [show 2 * (ε / 2) = ε by ring] at h

/-- `P_a(T_ε) = X(ε) I + Y(ε) J` with `D = D_*`. -/
theorem aeval_Teps_Pa (p a B ε : ℝ) :
    Polynomial.aeval (Teps p ε) (Pa a B) =
      Xe (Dstar p) a B ε • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Ye (Dstar p) a B ε • Jmat := by
  simp only [Pa, map_add, map_sub, map_one, map_mul, aeval_C, aeval_X, sq,
    Algebra.algebraMap_eq_smul_one]
  ext i j
  -- The ε-specific instances only rewrite `e^(-εD)`, `cos ε`, `sin ε` (the general lemmas would loop on `ε/2`).
  fin_cases i <;> fin_cases j <;>
    simp [Teps, Rot, Jmat, Matrix.mul_apply, Fin.sum_univ_two, Xe, Ye, exp_neg_mul_eq (Dstar p) ε,
      cos_eq_half ε, sin_eq_half ε] <;>
    ring

/-- `(x I + y J)(u, v) = (x u + y v, x v - y u)`. -/
theorem smul_one_add_smul_J_mulVec (x y u v : ℝ) :
    (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) + y • Jmat) *ᵥ ![u, v] = ![x * u + y * v, x * v - y * u] := by
  ext i
  fin_cases i <;> simp [Jmat, Matrix.add_mulVec, Matrix.smul_mulVec] <;> ring

theorem Xe_zero (D a B : ℝ) : Xe D a B 0 = 1 + B := by
  simp [Xe]

theorem Ye_zero (D a B : ℝ) : Ye D a B 0 = a := by
  simp [Ye]

/-- `X'(0) = -(a/2 + B D)`: product and chain rules on each term of `Xe`. -/
theorem hasDerivAt_Xe (D a B : ℝ) : HasDerivAt (Xe D a B) (-(a / 2 + B * D)) 0 := by
  have hh := (hasDerivAt_id (0 : ℝ)).div_const 2
  have hE1 := (((hasDerivAt_id (0 : ℝ)).mul_const D).div_const 2).neg.exp
  have hE2 := ((hasDerivAt_id (0 : ℝ)).mul_const D).neg.exp
  have H := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hE1.const_mul a).mul hh.sin)).add
    ((hE2.const_mul B).mul (hasDerivAt_id (0 : ℝ)).cos)
  convert H using 1
  · funext x
    simp [Xe]
  · simp
    ring

/-- `Y'(0) = B - a D / 2`: product and chain rules on each term of `Ye`. -/
theorem hasDerivAt_Ye (D a B : ℝ) : HasDerivAt (Ye D a B) (B - a * D / 2) 0 := by
  have hh := (hasDerivAt_id (0 : ℝ)).div_const 2
  have hE1 := (((hasDerivAt_id (0 : ℝ)).mul_const D).div_const 2).neg.exp
  have hE2 := ((hasDerivAt_id (0 : ℝ)).mul_const D).neg.exp
  have H := ((hE1.const_mul a).mul hh.cos).add ((hE2.const_mul B).mul (hasDerivAt_id (0 : ℝ)).sin)
  convert H using 1
  · funext x
    simp [Ye]
  · simp
    ring

end TK
end Matsaev
