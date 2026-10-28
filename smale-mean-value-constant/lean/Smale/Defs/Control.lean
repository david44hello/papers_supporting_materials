/-
Smale/Defs/Control.lean — the data of the control experiment of paper 009 (posted v1.80, tex l.439-442): `H(z)` replaced
by `H(sz)`, `s = 1250009/1250000`. A NEW file (definitions added after the freeze go in new files).
-/
import Smale.Defs.Data

namespace Smale

open Polynomial

/-- The scaling factor `s = 1250009/1250000` of the control (tex l.439). -/
noncomputable def sCtrl : ℂ := 1250009 / 1250000

/-- `H(sz)`, the polynomial of the control (tex l.439). -/
noncomputable def Hctrl : ℂ[X] := Hdata.comp (C sCtrl * X)

end Smale
