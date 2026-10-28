/-
Matsaev/Defs/Conjecture.lean — Matsaev's conjecture in the literature's form (trust surface).
Paper: eq. `eq:matsaev`.
-/
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Matsaev.Defs.Spaces

namespace Matsaev

open scoped ENNReal
open Polynomial

/-- **Matsaev's conjecture** (1971) at the exponent `p`, as in the literature (eq. `eq:matsaev`): for every measure
space `(Ω, μ)`, every contraction `T` of the complex space `L^p(μ)` (Mathlib's `MeasureTheory.Lp ℂ p μ`) and every complex
polynomial `P`, `‖P(T)‖_{L^p → L^p} ≤ ‖P(S)‖_{ℓ^p → ℓ^p}`, where `S` is the right shift on `ℓ^p(ℕ)`. -/
def MatsaevConjecture (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (T : MeasureTheory.Lp ℂ p μ →L[ℂ] MeasureTheory.Lp ℂ p μ),
    ‖T‖ ≤ 1 → ∀ P : ℂ[X], ‖Polynomial.aeval T P‖ ≤ shiftNorm p ℂ P

end Matsaev
