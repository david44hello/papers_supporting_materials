/-
Cereceda/Intro/ColourDense.lean — class (iii) of Section 1 (short v3.90): the 2-colour-dense graphs are 3-colour-dense
(l. 157-158).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.ColourDense
import Cereceda.Intro.SemiFalse

namespace Cereceda

namespace ColourDense

/-! ### The 2-colour-dense graphs are 3-colour-dense (v3.90 l. 157-158) -/

theorem _root_.Cereceda.colourDense_two_three_proved {V : Type} (G : SimpleGraph V) : IsColourDense 2 G → IsColourDense 3 G := by
  intro h
  induction h with
  | @base V _ G hc hq =>
    exact IsColourDense.base G (hc.mono (by norm_num)) ⟨hq.1, fun x => (hq.2 x).trans (by norm_num)⟩
  | @step V _ G S u v hc hsep hu hv hvD hS hD _ ih =>
    exact IsColourDense.step G S u v (hc.mono (by norm_num)) hsep hu hv hvD hS
      (hD.imp id fun h => h.trans (by norm_num)) ih

end ColourDense

end Cereceda
