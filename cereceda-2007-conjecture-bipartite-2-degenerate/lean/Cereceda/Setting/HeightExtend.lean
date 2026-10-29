/-
Cereceda/Setting/HeightExtend.lean — a height given only on one component extends to the whole graph (the
paper's heights in the proof of Lemma 2.3 are "height functions `h_α` of `α|_T` and `h_β` of `β|_T`", short v3.90 l. 336).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

If some height of `c` on `F` exists (`h0`), and `h` is a height of `c` on the component of `s` only, then the function
equal to `h` on that component and to `h0` elsewhere is a height on `F`: no edge of `F` leaves a component.
-/
import Cereceda.Defs.Basic

namespace Cereceda

namespace HeightExtend

variable {W : Type}

open Classical in
theorem extend (F : SimpleGraph W) (s : W) (c : W → Fin 4) (h0 : W → ℤ) (hh0 : IsHeight F c h0) (h : W → ℤ)
    (hT : (∀ v, F.Reachable s v → ((h v : ℤ) : ZMod 3) = res (c v)) ∧
      ∀ u v, F.Reachable s u → F.Adj u v → |h u - h v| = 1) :
    ∃ h' : W → ℤ, IsHeight F c h' ∧ ∀ v, F.Reachable s v → h' v = h v := by
  refine ⟨fun v => if F.Reachable s v then h v else h0 v, ⟨fun v => ?_, fun u v huv => ?_⟩,
    fun v hv => by simp only [hv, ↓reduceIte]⟩
  · by_cases hv : F.Reachable s v
    · simp only [hv, ↓reduceIte]; exact hT.1 v hv
    · simp only [hv, ↓reduceIte]; exact hh0.1 v
  · by_cases hu : F.Reachable s u
    · have hv : F.Reachable s v := hu.trans huv.reachable
      simp only [hu, hv, ↓reduceIte]; exact hT.2 u v hu huv
    · have hv : ¬ F.Reachable s v := fun hv => hu (hv.trans huv.symm.reachable)
      simp only [hu, hv, ↓reduceIte]; exact hh0.2 u v huv

end HeightExtend

end Cereceda
