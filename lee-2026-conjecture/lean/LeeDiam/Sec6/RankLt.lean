/-
LeeDiam/Sec6/RankLt.lean — sec_reverse l. 85 of paper 004 (new in v1.30): in `P_n`, `p < q` implies `ρ(p) < ρ(q)`,
where `ρ` (the rank) is the level function `PnElem.level`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec6.PnOrder

namespace LeeDiam

/-- `p < q` in `P_n` implies `level p < level q` (the level rises by one along each listed relation, and `<` is a
nonempty chain of them). -/
theorem def_6_1_rank_lt_proved (n : ℕ) : ∀ p q : Pn n, p < q → PnElem.level p < PnElem.level q :=
  fun _ _ h => PnOrder.lt_level h

end LeeDiam
