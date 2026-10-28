/-
Smale/Proofs/Parity.lean — the parity of the Dieudonné polynomials of paper 009 (tex v1.90 l.234): since
`U_ℓ(-c) = (-1)^ℓ U_ℓ(c)` (Mathlib's `Chebyshev.U_eval_neg`), `P_{-c}(w) = P_c(-w)`.
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial

/-- `U_ℓ(-c) = (-1)^ℓ U_ℓ(c)` for the real Chebyshev polynomials of the second kind. -/
theorem U_eval_neg_real (l : ℕ) (c : ℝ) :
    (Chebyshev.U ℝ (l : ℤ)).eval (-c) = (-1) ^ l * (Chebyshev.U ℝ (l : ℤ)).eval c := by
  rw [Chebyshev.U_eval_neg, Int.cast_negOnePow_natCast]

/-- tex v1.90 l.234, the proposed Statements type: `U_ℓ(-c) = (-1)^ℓ U_ℓ(c)`, hence `P_{-c}(w) = P_c(-w)`. -/
theorem sec4_P_neg_proved (H : ℂ[X]) (n : ℕ) (c : ℝ) (w : ℂ) :
    (∀ l : ℕ, (Chebyshev.U ℝ (l : ℤ)).eval (-c) = (-1) ^ l * (Chebyshev.U ℝ (l : ℤ)).eval c) ∧
      (dieudonne H n (-c)).eval w = (dieudonne H n c).eval (-w) := by
  refine ⟨fun l => U_eval_neg_real l c, ?_⟩
  simp only [dieudonne, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [U_eval_neg_real, neg_pow w l]
  push_cast
  ring

end Smale
