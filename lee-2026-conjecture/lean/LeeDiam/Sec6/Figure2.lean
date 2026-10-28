/-
LeeDiam/Sec6/Figure2.lean — Figure 2 of paper 004 (fig:Pn, sec_reverse l. 54-83): the Hasse diagram of `P_n`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

The cover pairs of `P_n` are the listed relations of Definition 6.1, by `covBy_iff_of_level` (Sec1/Figure1.lean) with
the level function of `def_6_1_rank_proved` (Sec6/Structure.lean).
-/
import LeeDiam.Sec1.Figure1
import LeeDiam.Sec6.Structure

namespace LeeDiam

/-- Figure 2: the cover pairs of `P_n` are exactly the listed relations of Definition 6.1. -/
theorem fig_2_hasse_proved (n : ℕ) (x z : Pn n) : x ⋖ z ↔ PnElem.Rel x z :=
  covBy_iff_of_level (PnElem.Rel (n := n)) PnElem.level (fun _ _ => Iff.rfl) (def_6_1_rank_proved n) x z

end LeeDiam
