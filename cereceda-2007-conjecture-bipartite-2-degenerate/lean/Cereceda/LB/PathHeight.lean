/-
Cereceda/LB/PathHeight.lean — plain colourings have path heights; sigma steps.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.LowerBound
import Cereceda.LB.LowerBounds

namespace Cereceda

open Finset

namespace PathHeightAux

/-- The height built step by step from the residues `col`: start at `0`, then `+1` when the next residue is one more,
else `-1`. -/
def buildHeight (col : ℕ → ZMod 3) : ℕ → ℤ
  | 0 => 0
  | i + 1 => buildHeight col i + (if col (i + 1) = col i + 1 then 1 else -1)

/-- If consecutive residues always differ, the built height is a `PathAux.StepHeight`. -/
theorem buildHeight_step {n : ℕ} (col : ℕ → ZMod 3) (hne : ∀ i, i + 1 < n → col (i + 1) ≠ col i) :
    PathAux.StepHeight n col (buildHeight col) := by
  intro i hi
  by_cases hup : col (i + 1) = col i + 1
  · left
    exact ⟨by simp [buildHeight, hup], hup⟩
  · right
    refine ⟨by simp [buildHeight, hup]; ring, PathAux.third_fin _ _ (hne i hi) hup⟩

end PathHeightAux

open PathHeightAux MovesAux

theorem sec4_path_height_proved (n k : ℕ) (f : Fin n → Fin k) :
    (∀ c : Fin n ⊕ Fin k → Fin 4, IsProperFn (pathApex n k f) c → IsPlain c → ∃ h, IsPathHeight c h) ∧
    IsPathHeight (sigmaPlus n k) (fun i => (i : ℤ)) ∧ IsPathHeight (sigmaMinus n k) (fun i => -(i : ℤ)) := by
  refine ⟨fun c hc hp => ⟨buildHeight (pcol c), isPathHeight_of c _ (buildHeight_step _ ?_)⟩,
    LBAux.sp_height, LBAux.sm_height⟩
  intro i hi
  rw [pcol_of_lt c hi, pcol_of_lt c (by omega : i < n)]
  exact res_ne _ _ (path_ne_three hc hp _) (path_ne_three hc hp _)
    (hc _ _ (adj_path (f := f) ⟨i, by omega⟩ (i + 1) hi (Or.inl rfl))).symm

end Cereceda
