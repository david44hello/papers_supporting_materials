/-
Osserman/Defs/Threshold.lean — the objects of Lemma 4.1 (lem:threshold, paper 013 l. 491-494): h(x) = (⟨H_ix,x⟩)_i and
H(a) = ∑ a_i H_i.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Basic

namespace Osserman

open Matrix

/-- `h(x) = (⟨H_ix, x⟩)_{i=0}^m` (l. 492). -/
def hvec {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Fin (m + 1) → ℝ :=
  fun i => x ⬝ᵥ (H i *ᵥ x)

/-- `H(a) = ∑_i a_i H_i` (l. 494). -/
def Hcomb {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (a : Fin (m + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, a i • H i

end Osserman
