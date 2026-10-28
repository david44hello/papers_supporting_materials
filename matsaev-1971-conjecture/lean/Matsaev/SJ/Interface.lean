/-
Matsaev/SJ/Interface.lean — the interface between Steps D/E (lower bounds for Σ_a) and Steps F-I (the Bellman function) of
Theorem 3.6 (internal). `SigmaInterface` is proved in Matsaev/SJ/Sigma.lean; the
Bellman inequality is proved from it (Matsaev/SJ/Bellman*.lean). Not trust surface: since Statements v0.51 no statement mentions `Ca` or
`SigmaInterface` (`lemma_3_5_angle_form` states the same property in full, and `bellman_of_sigma` consumes it by unfolding).
-/
import Mathlib.Analysis.Normed.Lp.Matrix
import Matsaev.Angle.Defs
import Matsaev.Defs.Spaces

namespace Matsaev.SJ

open Matsaev Matsaev.Angle
open scoped ENNReal

/-- `C_a = ‖P_a(J)‖_{ℓ^p_2}` (real). -/
noncomputable def Ca (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B : ℝ) : ℝ :=
  matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))

/-- The conclusion of Steps D/E (plan §4.2): for every small `ρ` there are `a₁, η > 0` such that for `0 < a < a₁` some angle
`θa` with `|θa - θs| ≤ a` has `Σ_a(e(θa)) = 0`, and `Σ_a(e(θ)) ≥ a η min(ρ, dist(θ, θa + (π/2)ℤ))²` for all `θ`. -/
def SigmaInterface (p : ℝ≥0∞) [Fact (1 ≤ p)] (B θs : ℝ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ a₁ η : ℝ, 0 < a₁ ∧ 0 < η ∧ ∀ a : ℝ, 0 < a → a < a₁ →
    ∃ θa : ℝ, |θa - θs| ≤ a ∧ SigmaAng p.toReal a B (Ca p a B) θa = 0 ∧
      ∀ θ : ℝ, a * η * (min ρ (angDist θ θa)) ^ 2 ≤ SigmaAng p.toReal a B (Ca p a B) θ

end Matsaev.SJ
