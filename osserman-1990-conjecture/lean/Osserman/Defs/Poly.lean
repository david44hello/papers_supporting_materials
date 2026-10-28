/-
Osserman/Defs/Poly.lean — polynomials on ℝ^N: |z|², gradient and Laplacian (by MvPolynomial.pderiv, i.e. exact
algebraic derivatives), quadratic forms ⟨Mz,z⟩, the FKM quartic F_P, and the paper's quartic F(z) = s² - 8b(x,y)
on ℝ^32 = ℝ^16 ⊕ ℝ^16 (paper 013, §2 l. 383-387, §3 l. 447-452).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE. `gradSqP F = ∑_i (∂_i F)²` is `|∇F|²` and `lapP F = ∑_i ∂_i∂_i F` is `ΔF`. `FKMP P` is
`F_P(z) = |z|⁴ - 2∑_i ⟨P_iz,z⟩²` (eq:FKM). `quarticP R μ κ` is the paper's `F` built from `A(x) = (J_x - μΠ(x))/κ`,
`Q(x) = A(x) + xxᵀ`, `b(x,y) = ⟨Q(x)y,y⟩` (l. 339, 367, 378, 386), with `x = (z_0..z_15)`, `y = (z_16..z_31)`; the entries
of `J_x` are the quadratic polynomials `(J_x)_{jk} = ∑_{a,b} x_a x_b R(e_k,e_a,e_b)_j` (since `J_x e_k = R(e_k,x,x)`).
-/
import Osserman.Defs.Curvature

namespace Osserman

open MvPolynomial Matrix

/-- `s = |z|² = ∑ z_i²`. -/
noncomputable def sqP (N : ℕ) : MvPolynomial (Fin N) ℝ := ∑ i, X i ^ 2

/-- `|∇F|² = ∑_i (∂_i F)²`. -/
noncomputable def gradSqP {N : ℕ} (F : MvPolynomial (Fin N) ℝ) : MvPolynomial (Fin N) ℝ := ∑ i, (pderiv i F) ^ 2

/-- `ΔF = ∑_i ∂_i ∂_i F`. -/
noncomputable def lapP {N : ℕ} (F : MvPolynomial (Fin N) ℝ) : MvPolynomial (Fin N) ℝ := ∑ i, pderiv i (pderiv i F)

/-- `⟨Mz, z⟩` as a polynomial. -/
noncomputable def quadP {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) : MvPolynomial (Fin N) ℝ :=
  ∑ a, ∑ b, C (M a b) * X a * X b

/-- The FKM quartic `F_P(z) = |z|⁴ - 2 ∑_{i} ⟨P_i z, z⟩²` (eq:FKM, l. 450). -/
noncomputable def FKMP {N k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) : MvPolynomial (Fin N) ℝ :=
  sqP N ^ 2 - 2 * ∑ i, quadP (P i) ^ 2

/-- The `x`-variables `z_0, …, z_15` of `ℝ^32`. -/
noncomputable def xP (a : Fin 16) : MvPolynomial (Fin 32) ℝ := X (Fin.castAdd 16 a)

/-- The `y`-variables `z_16, …, z_31` of `ℝ^32`. -/
noncomputable def yP (a : Fin 16) : MvPolynomial (Fin 32) ℝ := X (Fin.natAdd 16 a)

/-- The entry `(J_x)_{jk} = ∑_{a,b} x_a x_b R(e_k, e_a, e_b)_j`, a quadratic polynomial in `x`. -/
noncomputable def jacEntryP (R : CurvTensor 16) (j k : Fin 16) : MvPolynomial (Fin 32) ℝ :=
  ∑ a, ∑ b, C (R.op (Pi.single k 1) (Pi.single a 1) (Pi.single b 1) j) * xP a * xP b

/-- The entry `Π(x)_{jk} = |x|²δ_jk - x_j x_k`. -/
noncomputable def piEntryP (j k : Fin 16) : MvPolynomial (Fin 32) ℝ :=
  (if j = k then ∑ a, xP a ^ 2 else 0) - xP j * xP k

/-- The entry `Q(x)_{jk} = A(x)_{jk} + x_j x_k` with `A(x) = (J_x - μΠ(x))/κ` (l. 339, 367). -/
noncomputable def qEntryP (R : CurvTensor 16) (μ κ : ℝ) (j k : Fin 16) : MvPolynomial (Fin 32) ℝ :=
  C κ⁻¹ * (jacEntryP R j k - C μ * piEntryP j k) + xP j * xP k

/-- `b(x,y) = ⟨Q(x)y, y⟩` (eq:b, l. 378). -/
noncomputable def bP (R : CurvTensor 16) (μ κ : ℝ) : MvPolynomial (Fin 32) ℝ :=
  ∑ j, ∑ k, qEntryP R μ κ j k * yP j * yP k

/-- The paper's quartic `F(z) = s² - 8 b(x,y)` on `ℝ^32` (eq:F, l. 386). -/
noncomputable def quarticP (R : CurvTensor 16) (μ κ : ℝ) : MvPolynomial (Fin 32) ℝ :=
  sqP 32 ^ 2 - 8 * bP R μ κ

end Osserman
