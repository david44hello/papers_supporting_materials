/-
Cereceda/Defs/Degeneracy.lean — the degeneracy of a graph (short v3.90 l. 64-65), for Cereceda's form of
Conjecture 1.1 (l. 76-78).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE (v3.90 l. 64-65, verbatim): "The degeneracy of a graph is the least d for which it is d-degenerate."
-/
import Cereceda.Defs.Basic

namespace Cereceda

variable {V : Type} [Fintype V]

/-- The degeneracy of `G` (v3.90 l. 64-65): the least `d` for which `G` is `d`-degenerate (`IsDegenerate`). Every
finite graph is `d`-degenerate for `d` = its number of vertices, so the set is nonempty and the infimum is attained. -/
noncomputable def degeneracy (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sInf {d | IsDegenerate G d}

end Cereceda
