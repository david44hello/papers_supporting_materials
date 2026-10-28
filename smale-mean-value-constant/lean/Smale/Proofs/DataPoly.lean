/-
Smale/Proofs/DataPoly.lean — the polynomials of Section 5 (Q, G, L, V, H) as `toPoly` of coefficient lists, and the
exact identities between them, each checked by the kernel on lists of rationals.
-/
import Smale.Proofs.DataGQ

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

def one : GQ := ⟨1, 0⟩

theorem toC_one : one.toC = 1 := by
  apply Complex.ext <;> simp [GQ.toC_re, GQ.toC_im, one]

/-- `X - a`. -/
def lin (a : GQ) : GP := [GQ.neg a, one]

def pprod : List GP → GP
  | [] => [one]
  | p :: ps => pmul p (pprod ps)

def ppow (p : GP) : ℕ → GP
  | 0 => [one]
  | n + 1 => pmul p (ppow p n)

theorem toPoly_lin (a : GQ) : toPoly (lin a) = X - C a.toC := by
  simp [lin, toPoly, GQ.toC_neg, toC_one]; ring

theorem toPoly_one : toPoly [one] = 1 := by simp [toPoly, toC_one]

theorem toPoly_pprod (ps : List GP) : toPoly (pprod ps) = (ps.map toPoly).prod := by
  induction ps with
  | nil => simp [pprod, toPoly_one]
  | cons p ps ih => simp [pprod, toPoly_pmul, ih]

theorem toPoly_ppow (p : GP) (n : ℕ) : toPoly (ppow p n) = toPoly p ^ n := by
  induction n with
  | zero => simp [ppow, toPoly_one]
  | succ n ih => rw [ppow, toPoly_pmul, ih, pow_succ, mul_comm]

/-- `Q`'s coefficients. -/
def qGQ : GP := QcoeffData.map fun c => (⟨c.1, c.2⟩ : GQ)

theorem Qdata_eq : Qdata = toPoly qGQ := by
  rw [toPoly_eq_sum, Qdata]
  have hlen : qGQ.length = 19 := rfl
  rw [hlen]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hget : qGQ.getD k GQ.zero = ⟨(QcoeffData.getD k (0, 0)).1, (QcoeffData.getD k (0, 0)).2⟩ := by
    rw [qGQ, show GQ.zero = (fun c : ℚ × ℚ => (⟨c.1, c.2⟩ : GQ)) (0, 0) from rfl, List.getD_map]
  rw [hget]; rfl

/-- `G = z² + g₁z + g₀`. -/
def gGQ : GP := [g0GQ, g1GQ, one]

theorem Gpoly_eq : Gpoly = toPoly gGQ := by
  simp [Gpoly, gGQ, toPoly, g0D_eq, g1D_eq, toC_one]; ring

/-- `∏_j (z - ρ_j)`. -/
def rhoProd : GP := pprod (rhoGQ.map lin)

theorem prod_rho_eq : ∏ j : Fin 10, (X - C (rho j)) = toPoly rhoProd := by
  simp only [rhoProd, toPoly_pprod, List.map_map, Fin.prod_univ_succ, Fin.prod_univ_zero, rho_eq]
  simp [rhoGQ, Function.comp, toPoly_lin]

/-- `L = (z - 1)⁵ ∏_j (z - ρ_j)`. -/
def lGQ : GP := pmul (ppow (lin one) 5) rhoProd

theorem Lpoly_eq : Lpoly = toPoly lGQ := by
  rw [Lpoly, prod_rho_eq, lGQ, toPoly_pmul, toPoly_ppow, toPoly_lin, toC_one, map_one]

/-- `V = 18 G ∏_j (z - ρ_j)`. -/
def vGQ : GP := pmul [GQ.ofQ 18] (pmul gGQ rhoProd)

theorem Vdata_eq : Vdata = toPoly vGQ := by
  rw [Vdata, Gpoly_eq, prod_rho_eq, vGQ, toPoly_pmul, toPoly_pmul]
  simp [toPoly, GQ.toC_ofQ, map_ofNat]; ring

/-- `∏_j (z - a_j)` and `∏_j (1 - ā_j z)` for `[a₁, a₂]`. -/
def zerosGQ : GP := pmul (lin a1GQ) (lin a2GQ)
def reflGQ : GP := pmul [one, GQ.neg (GQ.cnj a1GQ)] [one, GQ.neg (GQ.cnj a2GQ)]

theorem zerosPoly_eq : zerosPoly [a1D, a2D] = toPoly zerosGQ := by
  simp [zerosPoly, zerosGQ, toPoly_pmul, toPoly_lin, a1D_eq, a2D_eq]

theorem reflPoly_eq : reflPoly [a1D, a2D] = toPoly reflGQ := by
  simp [reflPoly, reflGQ, toPoly_pmul, toPoly, toC_one, GQ.toC_neg, GQ.toC_cnj, a1D_eq, a2D_eq]; ring

/-! ### Kernel identities -/

/-- `Q · ∏(1 - ā_j z) = H · ∏(z - a_j)` for the computed `H`. -/
theorem check_H : peq (pmul qGQ reflGQ) (pmul hGQ zerosGQ) = true := by decide +kernel

/-- `Q' = 18 (z - 1)⁵ G ∏_j (z - ρ_j)`. -/
theorem check_Qderiv : peq (pderiv qGQ) (pmul [GQ.ofQ 18] (pmul (ppow (lin one) 5) (pmul gGQ rhoProd))) = true := by
  decide +kernel

theorem zerosPoly_a12_monic : (zerosPoly [a1D, a2D]).Monic := by
  simp only [zerosPoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact (monic_X_sub_C _).mul (monic_X_sub_C _)

theorem Hdata_eq : Hdata = toPoly hGQ := by
  have h := toPoly_eq_of_peq check_H
  rw [toPoly_pmul, toPoly_pmul, ← Qdata_eq, ← reflPoly_eq, ← zerosPoly_eq] at h
  rw [Hdata, Hpoly, h, mul_comm]
  exact mul_divByMonic_cancel_left _ zerosPoly_a12_monic

theorem Hdata_mul_zeros : Hdata * zerosPoly [a1D, a2D] = Qdata * reflPoly [a1D, a2D] := by
  have h := toPoly_eq_of_peq check_H
  rw [toPoly_pmul, toPoly_pmul, ← Qdata_eq, ← reflPoly_eq, ← zerosPoly_eq, ← Hdata_eq] at h
  exact h.symm

theorem Qdata_derivative : Qdata.derivative = 18 * (X - 1) ^ 5 * Gpoly * ∏ j : Fin 10, (X - C (rho j)) := by
  have h := toPoly_eq_of_peq check_Qderiv
  rw [toPoly_pderiv, ← Qdata_eq] at h
  rw [h, Gpoly_eq, prod_rho_eq]
  simp [toPoly_pmul, toPoly_ppow, toPoly_lin, toC_one, toPoly, GQ.toC_ofQ, map_ofNat]; ring

theorem Qdata_derivative_eq_V : Qdata.derivative = (X - 1) ^ 5 * Vdata := by
  rw [Qdata_derivative, Vdata]; ring

end Smale.Exact
