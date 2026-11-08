/-
Smale/R/Final.lean — The cover of [0, 1], and fact (R).
-/
import Smale.R.Round
import Smale.R.Cover

namespace Smale.RCheck

open Finset Smale.RK

theorem coverList_chain : coverChain 0 coverList = true := by decide +kernel

/-! ### Fact (R) -/

/-- The kernel computation, on the 299 intervals that cover `[0, 1]`. -/
theorem schurB_data_det_ne_zero (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) : (schurB 17 (pData c)).det ≠ 0 := by
  have hne : coverList ≠ [] := by
    intro h
    have := coverList_chain
    rw [h] at this
    exact absurd this (by decide)
  obtain ⟨e, he, h1, h2⟩ := coverChain_sound c coverList 0 coverList_chain
    (by rw [Nat.cast_zero]; exact mul_nonneg (by positivity) hc.1) hc.2 hne
  obtain ⟨A, hA⟩ := coverList_proved e he
  exact interval_det_ne hA hb_size hb_round c ⟨by linarith [hc.1], hc.2⟩ h1 h2

/-- FACT (R), the printed statement, by this route. -/
theorem condR_proved : CondRdata := condR_of_det schurB_data_det_ne_zero

end Smale.RCheck
