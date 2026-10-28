/-
Matsaev/Angle/Defs.lean — shared definitions for the proofs of Theorem 3.6 and Lemma 4.1 (angle form).
TRUST SURFACE for `Matsaev.Paper.lemma_3_5_angle_form`: `IsThetaStar`, `SigmaAng`, `angDist`, `Nang`, `qang` (FROZEN: a
change needs a trust review). `ev`, `Wmov`: internal.

`q` is the real exponent (the paper's p, > 2 where it matters). e(θ) = (cos θ, sin θ).
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Matsaev.Defs.Scalar

namespace Matsaev.Angle

open Real

/-- `e(θ) = (cos θ, sin θ)`. -/
noncomputable def ev (θ : ℝ) : Fin 2 → ℝ := ![Real.cos θ, Real.sin θ]

/-- `N(θ) = ‖e(θ)‖_q^q = |cos θ|^q + |sin θ|^q`. -/
noncomputable def Nang (q θ : ℝ) : ℝ := |Real.cos θ| ^ q + |Real.sin θ| ^ q

/-- `q(θ) = Q(e(θ))`, the paper's `Q` on the unit circle. -/
noncomputable def qang (q θ : ℝ) : ℝ := Qf q (Real.cos θ) (Real.sin θ)

/-- The moving average `W_γ(θ) = q ∫_{θ-γ}^{θ} q(τ) dτ`; plan R2: `log N(θ - γ) - log N(θ) = W_γ(θ)`. -/
noncomputable def Wmov (q γ θ : ℝ) : ℝ := q * ∫ τ in (θ - γ)..θ, qang q τ

/-- The distance from `θ` to the coset `θ' + (π/2)ℤ` (the angular distance to the four points `±e(θ'), ±J e(θ')`). -/
noncomputable def angDist (θ θ' : ℝ) : ℝ :=
  (π / 2) * min (Int.fract ((θ - θ') / (π / 2))) (1 - Int.fract ((θ - θ') / (π / 2)))

/-- The paper's `Σ_a` (eq. `eq:Sigma`, Theorem 3.6, Step 1) at `s = e(θ)`, for a constant `C` (in use, `C = C_a = ‖P_a(J)‖_p`):
`Σ_a(s) = 2 (C^q ‖s‖_q^q - ‖P_a(J) s‖_q^q)`, `P_a(J) s = ((1+B)u + a v, (1+B)v - a u)` for `s = (u, v)`. -/
noncomputable def SigmaAng (q a B C θ : ℝ) : ℝ :=
  2 * (C ^ q * Nang q θ - (|(1 + B) * Real.cos θ + a * Real.sin θ| ^ q + |(1 + B) * Real.sin θ - a * Real.cos θ| ^ q))

/-- Everything the later steps use about the maximum angle `θ_* = arctan t_*` (Lemma 3.4 in angle form, plan R3).
A helper proves `∃ θs, IsThetaStar q θs` for `q > 2`; downstream lemmas take `θs` and this as hypotheses. -/
structure IsThetaStar (q θs : ℝ) : Prop where
  mem : 0 < θs ∧ θs < π / 4
  dstar_pos : 0 < Dstar q
  le_dstar : ∀ θ : ℝ, qang q θ ≤ Dstar q
  eq_at : qang q θs = Dstar q
  eq_iff : ∀ θ : ℝ, qang q θ = Dstar q ↔ ∃ k : ℤ, θ = θs + k * (π / 2)
  /-- `q` is differentiable everywhere (`q > 2`), with critical points exactly the maxima `θs + kπ/2` and the minima
  `-θs + kπ/2`. -/
  differentiable : Differentiable ℝ (qang q)
  crit_iff : ∀ θ : ℝ, deriv (qang q) θ = 0 ↔ ∃ k : ℤ, θ = θs + k * (π / 2) ∨ θ = -θs + k * (π / 2)
  min_value : ∀ k : ℤ, qang q (-θs + k * (π / 2)) = -Dstar q
  /-- Strict concavity near the maximum: `q'' ≤ -m` on `[θs - ρ₀, θs + ρ₀]`, with `q` twice differentiable there. -/
  concave_near : ∃ ρ₀ m : ℝ, 0 < ρ₀ ∧ 0 < m ∧ ∀ θ ∈ Set.Icc (θs - ρ₀) (θs + ρ₀),
    DifferentiableAt ℝ (deriv (qang q)) θ ∧ deriv (deriv (qang q)) θ ≤ -m

end Matsaev.Angle
