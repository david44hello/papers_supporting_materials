/-
Smale/Proofs/DataGUnique.lean — `sec5_G_unique`: `(g₀, g₁)` is the unique solution of `∫_b^{a₁} G L = ∫_b^{a₂} G L = 0`,
a 2×2 linear system with nonzero determinant. The integrals `I_k(a) = ∫_b^a z^k L` are exact Gaussian rationals:
the kernel computes an antiderivative list `F_k`, checks `F_k' = z^k L`, and evaluates.
-/
import Smale.Proofs.DataSec5

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

def pantiAux : ℕ → GP → GP
  | _, [] => []
  | k, c :: p => GQ.mul (GQ.ofQ (1 / ((k : ℚ) + 1))) c :: pantiAux (k + 1) p

/-- A candidate antiderivative (checked by `pderiv` before use). -/
def pantideriv (p : GP) : GP := GQ.zero :: pantiAux 0 p

/-- `z^k`. -/
def xpow : ℕ → GP
  | 0 => [one]
  | k + 1 => GQ.zero :: xpow k

theorem toPoly_xpow (k : ℕ) : toPoly (xpow k) = X ^ k := by
  induction k with
  | zero => exact toPoly_one
  | succ k ih => rw [xpow, toPoly_cons, ih, GQ.toC_zero, map_zero, zero_add, pow_succ, mul_comm]

/-- The antiderivative of `z^k L`. -/
def antiL (k : ℕ) : GP := pantideriv (pmul (xpow k) lGQ)

/-- `∫_b^a z^k L`. -/
def intL (k : ℕ) (a : GQ) : GQ := GQ.add (peval (antiL k) a) (GQ.neg (peval (antiL k) bGQ))

theorem check_antiL : peq (pderiv (antiL 0)) (pmul (xpow 0) lGQ) = true ∧
    peq (pderiv (antiL 1)) (pmul (xpow 1) lGQ) = true ∧ peq (pderiv (antiL 2)) (pmul (xpow 2) lGQ) = true := by
  decide +kernel

theorem derivative_antiL {k : ℕ} (h : peq (pderiv (antiL k)) (pmul (xpow k) lGQ) = true) :
    derivative (toPoly (antiL k)) = X ^ k * Lpoly := by
  rw [← toPoly_pderiv, toPoly_eq_of_peq h, toPoly_pmul, toPoly_xpow, Lpoly_eq]

theorem polyInt_XL {k : ℕ} (h : peq (pderiv (antiL k)) (pmul (xpow k) lGQ) = true) (a : GQ) :
    polyInt (X ^ k * Lpoly) bD a.toC = (intL k a).toC := by
  rw [polyInt_eq (derivative_antiL h), bD_eq, eval_toPoly, eval_toPoly, intL, GQ.toC_add, GQ.toC_neg]; ring

/-- The integral of `(z² + y z + x) L` is linear in `(x, y)`. -/
theorem polyInt_GL (x y : ℂ) (a : GQ) :
    polyInt ((X ^ 2 + C y * X + C x) * Lpoly) bD a.toC =
      (intL 2 a).toC + y * (intL 1 a).toC + x * (intL 0 a).toC := by
  obtain ⟨h0, h1, h2⟩ := check_antiL
  have hF : derivative (toPoly (antiL 2) + C y * toPoly (antiL 1) + C x * toPoly (antiL 0)) =
      (X ^ 2 + C y * X + C x) * Lpoly := by
    rw [derivative_add, derivative_add, derivative_C_mul, derivative_C_mul, derivative_antiL h0, derivative_antiL h1,
      derivative_antiL h2]
    ring
  rw [polyInt_eq hF, intL, intL, intL]
  simp only [eval_add, eval_mul, eval_C, GQ.toC_add, GQ.toC_neg, ← eval_toPoly, bD_eq]
  ring

/-- The exact checks: `(g₀, g₁)` solves the system, and its determinant is nonzero. -/
theorem check_system :
    GQ.add (GQ.add (intL 2 a1GQ) (GQ.mul g1GQ (intL 1 a1GQ))) (GQ.mul g0GQ (intL 0 a1GQ)) = GQ.zero ∧
    GQ.add (GQ.add (intL 2 a2GQ) (GQ.mul g1GQ (intL 1 a2GQ))) (GQ.mul g0GQ (intL 0 a2GQ)) = GQ.zero ∧
    GQ.add (GQ.mul (intL 0 a1GQ) (intL 1 a2GQ)) (GQ.neg (GQ.mul (intL 1 a1GQ) (intL 0 a2GQ))) ≠ GQ.zero := by
  decide +kernel

/-- `sec5_G_unique`, proved. -/
theorem sec5_G_unique_proved :
    (∀ g : ℂ × ℂ, (polyInt ((X ^ 2 + C g.2 * X + C g.1) * Lpoly) bD a1D = 0 ∧
        polyInt ((X ^ 2 + C g.2 * X + C g.1) * Lpoly) bD a2D = 0) ↔ g = (g0D, g1D)) ∧
      polyInt (1 * Lpoly) bD a1D * polyInt (X * Lpoly) bD a2D - polyInt (X * Lpoly) bD a1D * polyInt (1 * Lpoly) bD a2D
        ≠ 0 := by
  obtain ⟨h0, h1, _⟩ := check_antiL
  obtain ⟨s1, s2, hdet⟩ := check_system
  have e1 := congrArg GQ.toC s1
  have e2 := congrArg GQ.toC s2
  simp only [GQ.toC_add, GQ.toC_mul, GQ.toC_zero] at e1 e2
  have hD : (intL 0 a1GQ).toC * (intL 1 a2GQ).toC - (intL 1 a1GQ).toC * (intL 0 a2GQ).toC ≠ 0 := by
    intro hz
    apply hdet
    rw [← GQ.toC_eq_zero_iff, GQ.toC_add, GQ.toC_mul, GQ.toC_neg, GQ.toC_mul, ← sub_eq_add_neg]
    exact hz
  have hI0 : ∀ a : GQ, polyInt (1 * Lpoly) bD a.toC = (intL 0 a).toC := fun a => by
    rw [← polyInt_XL h0 a, pow_zero]
  have hI1 : ∀ a : GQ, polyInt (X * Lpoly) bD a.toC = (intL 1 a).toC := fun a => by
    rw [← polyInt_XL h1 a, pow_one]
  refine ⟨fun g => ?_, ?_⟩
  · rw [a1D_eq, a2D_eq, polyInt_GL, polyInt_GL, g0D_eq, g1D_eq]
    constructor
    · rintro ⟨q1, q2⟩
      have hx : (g.1 - g0GQ.toC) * ((intL 0 a1GQ).toC * (intL 1 a2GQ).toC - (intL 1 a1GQ).toC * (intL 0 a2GQ).toC)
          = 0 := by linear_combination (intL 1 a2GQ).toC * (q1 - e1) - (intL 1 a1GQ).toC * (q2 - e2)
      have hy : (g.2 - g1GQ.toC) * ((intL 0 a1GQ).toC * (intL 1 a2GQ).toC - (intL 1 a1GQ).toC * (intL 0 a2GQ).toC)
          = 0 := by linear_combination (intL 0 a1GQ).toC * (q2 - e2) - (intL 0 a2GQ).toC * (q1 - e1)
      have hx' := sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hD)
      have hy' := sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_right hD)
      exact Prod.ext hx' hy'
    · rintro rfl
      dsimp only
      exact ⟨by linear_combination e1, by linear_combination e2⟩
  · rw [a1D_eq, a2D_eq, hI0, hI0, hI1, hI1]; exact hD

end Smale.Exact
