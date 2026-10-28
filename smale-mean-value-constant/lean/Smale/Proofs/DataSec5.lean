/-
Smale/Proofs/DataSec5.lean — the exact claims of Section 5 about Q, V, H: `sec5_Q` (Q = 18 ∫_b G L, Q' = 18(z-1)⁵G∏(z-ρ_j),
Q monic of degree 18 vanishing at b, a₁, a₂, deg V = 12, H(z - a₁)(z - a₂) = Q(1 - ā₁z)(1 - ā₂z), deg H = 18).
-/
import Smale.Proofs.DataFacts

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

theorem derivative_antideriv (P : ℂ[X]) : derivative (antideriv P) = P := by
  rw [antideriv, derivative_sum]
  conv_rhs => rw [P.as_sum_range' (P.natDegree + 1) (Nat.lt_succ_self _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul_X_pow, ← C_mul_X_pow_eq_monomial, Nat.add_sub_cancel]
  congr 1
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

/-- A polynomial with zero derivative is constant (over `ℂ`). -/
theorem eq_of_derivative_eq {F G : ℂ[X]} (h : derivative F = derivative G) (u : ℂ) (hu : F.eval u = G.eval u) :
    F = G := by
  have hd : derivative (F - G) = 0 := by rw [derivative_sub, h, sub_self]
  have hc := eq_C_of_derivative_eq_zero hd
  have h0 : (F - G).coeff 0 = 0 := by
    have := congrArg (eval u) hc
    rw [eval_sub, hu, sub_self, eval_C] at this
    exact this.symm
  rw [h0, map_zero] at hc
  exact sub_eq_zero.mp hc

/-- `∫_u^v P = F(v) - F(u)` for any antiderivative `F` of `P`. -/
theorem polyInt_eq {P F : ℂ[X]} (hF : derivative F = P) (u v : ℂ) : polyInt P u v = F.eval v - F.eval u := by
  have h : antideriv P = F + C ((antideriv P).eval u - F.eval u) := by
    apply eq_of_derivative_eq _ u
    · simp
    · rw [derivative_add, derivative_C, add_zero, hF, derivative_antideriv]
  rw [polyInt, h]; simp; ring

theorem Qdata_monic_deg : Qdata.Monic ∧ Qdata.natDegree = 18 := by
  have hdeg : Qdata.natDegree = 18 := by
    rw [Qdata_eq]; exact natDegree_toPoly rfl (by decide +kernel)
  refine ⟨?_, hdeg⟩
  rw [Monic, leadingCoeff, hdeg, Qdata_eq, coeff_toPoly]
  have h : qGQ.getD 18 GQ.zero = one := by decide +kernel
  rw [h, toC_one]

theorem Vdata_natDegree : Vdata.natDegree = 12 := by
  rw [Vdata_eq]; exact natDegree_toPoly (by decide +kernel) (by decide +kernel)

theorem Hdata_natDegree : Hdata.natDegree = 18 := by
  rw [Hdata_eq]; exact natDegree_toPoly rfl (by decide +kernel)

theorem Qdata_eq_integral (z : ℂ) : Qdata.eval z = 18 * polyInt (Gpoly * Lpoly) bD z := by
  have hF : derivative (C (1 / 18 : ℂ) * Qdata) = Gpoly * Lpoly := by
    rw [derivative_C_mul, Qdata_derivative, Lpoly]
    have h18 : C (1 / 18 : ℂ) * (18 : ℂ[X]) = 1 := by
      rw [← map_ofNat C 18, ← C_mul]; norm_num
    linear_combination ((X - 1) ^ 5 * Gpoly * ∏ j : Fin 10, (X - C (rho j))) * h18
  have hb : Qdata.eval bD = 0 := data_D.2.2 bD (by simp)
  rw [polyInt_eq hF, eval_mul, eval_mul, eval_C, hb]
  ring

/-- `sec5_Q`, proved. -/
theorem sec5_Q_proved :
    (∀ z : ℂ, Qdata.eval z = 18 * polyInt (Gpoly * Lpoly) bD z) ∧
      Qdata.derivative = 18 * (X - 1) ^ 5 * Gpoly * ∏ j : Fin 10, (X - C (rho j)) ∧
      Qdata.Monic ∧ Qdata.natDegree = 18 ∧ Qdata.eval bD = 0 ∧ Qdata.eval a1D = 0 ∧ Qdata.eval a2D = 0 ∧
      Vdata.natDegree = 12 ∧ Hdata * zerosPoly [a1D, a2D] = Qdata * reflPoly [a1D, a2D] ∧ Hdata.natDegree = 18 :=
  ⟨Qdata_eq_integral, Qdata_derivative, Qdata_monic_deg.1, Qdata_monic_deg.2, data_D.2.2 bD (by simp),
    data_D.2.2 a1D (by simp), data_D.2.2 a2D (by simp), Vdata_natDegree, Hdata_mul_zeros, Hdata_natDegree⟩

end Smale.Exact
