/-
Smale/Proofs/Sec1Best.lean — paper 009, Section 1 (tex l.52-63): the normalization `p(u) = (P(z+u) - P(z))/P'(z)`
of a polynomial `P` of degree `d` at a point `z` with `P'(z) ≠ 0` lies in `𝓟_d` and has the critical points `ζ - z`;
hence `K(d)` is the best constant in Smale's inequality (1.1).
Helpers live in namespace `Smale.Sec1`.
-/
import Smale.Proofs.Lemma53

namespace Smale

namespace Sec1

open Polynomial Complex

/-- The derivative of the normalized polynomial `p(u) = (P(z+u) - P(z))/P'(z)`. -/
theorem derivative_normalizeAt (P : ℂ[X]) (z : ℂ) :
    (normalizeAt P z).derivative = C (P.derivative.eval z)⁻¹ * P.derivative.comp (X + C z) := by
  simp [normalizeAt, derivative_comp]

/-- `p(u) = (P(z+u) - P(z))/P'(z)` at a point `u`. -/
theorem eval_normalizeAt (P : ℂ[X]) (z u : ℂ) :
    (normalizeAt P z).eval u = (P.derivative.eval z)⁻¹ * (P.eval (z + u) - P.eval z) := by
  simp [normalizeAt, eval_comp, add_comm]

/-- `sec1_normalize` (tex l.57-58): for `P` of degree `d ≥ 2` and `P'(z) ≠ 0`, `p(u) = (P(z+u) - P(z))/P'(z)` lies
in `𝓟_d`, and its critical points are the points `ζ - z` with `ζ` a critical point of `P`. -/
theorem sec1_normalize_proved (d : ℕ) (_hd : 2 ≤ d) (P : ℂ[X]) (hP : P.natDegree = d) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    IsPd d (normalizeAt P z) ∧ ∀ β : ℂ, (normalizeAt P z).derivative.eval β = 0 ↔ P.derivative.eval (z + β) = 0 := by
  have hcomp : (P.comp (X + C z)).natDegree = d := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one, hP]
  refine ⟨⟨?_, ?_, ?_⟩, fun β => ?_⟩
  · unfold normalizeAt
    rw [natDegree_C_mul (inv_ne_zero hz), natDegree_sub_C, hcomp]
  · rw [eval_normalizeAt, add_zero, sub_self, mul_zero]
  · rw [derivative_normalizeAt]
    simp [eval_comp, hz]
  · rw [derivative_normalizeAt]
    simp [eval_comp, hz, add_comm]

/-- `sec1_best_constant` (tex l.58-63): `K(d)` is the best constant `K` in (1.1) over all polynomials `P` of degree
`d` and all `z` with `P'(z) ≠ 0`. Given (1.1) with `K`, take `P = p ∈ 𝓟_d` and `z = 0`; conversely normalize `P` at
`z` and use a critical point where `m(p)` is attained. -/
theorem sec1_best_constant_proved (d : ℕ) (hd : 2 ≤ d) (K : ℝ) :
    (∀ P : ℂ[X], P.natDegree = d → ∀ z : ℂ, P.derivative.eval z ≠ 0 →
      ∃ ζ : ℂ, P.derivative.eval ζ = 0 ∧ ‖(P.eval z - P.eval ζ) / (z - ζ)‖ ≤ K * ‖P.derivative.eval z‖) ↔
    Kd d ≤ (K : EReal) := by
  constructor
  · intro h
    unfold Kd
    apply iSup_le
    rintro ⟨p, hp⟩
    obtain ⟨ζ, hζ, hle⟩ := h p hp.1 0 (by rw [hp.2.2]; exact one_ne_zero)
    rw [hp.2.2, norm_one, mul_one, hp.2.1, zero_sub, zero_sub, neg_div_neg_eq, norm_div] at hle
    exact EReal.coe_le_coe_iff.2 ((mval_le hζ).trans hle)
  · intro h P hP z hz
    have hn := sec1_normalize_proved d hd P hP z hz
    obtain ⟨-, ⟨β, hβ, hm⟩, -⟩ := sec1_m_attained_proved d hd _ hn.1
    have hmK : mval (normalizeAt P z) ≤ K :=
      EReal.coe_le_coe_iff.1
        ((le_iSup (fun p : {p : ℂ[X] // IsPd d p} => ((mval p.1 : ℝ) : EReal)) ⟨_, hn.1⟩).trans h)
    have hn0 : ‖P.derivative.eval z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    have heq : ‖(P.eval z - P.eval (z + β)) / (z - (z + β))‖ =
        ‖(normalizeAt P z).eval β‖ / ‖β‖ * ‖P.derivative.eval z‖ := by
      have hzz : z - (z + β) = -β := by ring
      have hnum : P.eval z - P.eval (z + β) = -(P.eval (z + β) - P.eval z) := by ring
      rw [eval_normalizeAt, hzz, hnum, neg_div_neg_eq, norm_div, norm_mul, norm_inv,
        mul_comm _ ‖P.derivative.eval z‖, ← mul_div_assoc, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
    refine ⟨z + β, (hn.2 β).1 hβ, ?_⟩
    rw [heq, ← hm]
    exact mul_le_mul_of_nonneg_right hmK (norm_nonneg _)

end Sec1

end Smale
