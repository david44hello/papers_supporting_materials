/-
LeeDiam/Defs/Questions.lean — the two open questions of Section 7 of paper 004 (short v1.50, l. 221-227), as
propositions (they are questions, not claims: nothing here is proved or assumed).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic

namespace LeeDiam

/-- Question 7.1 (q:unbounded, l. 221-223): "Is `diam C(P) - diam O(P)` bounded on connected finite posets `P`?" — read
as bounded above (the other direction is unbounded by Theorem 1.3): some constant `C` has
`diam C(P) ≤ diam O(P) + C` for every connected finite poset `P`. -/
def question_7_1 : Prop :=
  ∃ C : ℕ, ∀ (P : Type) [Fintype P] [PartialOrder P], IsConnPoset P → chainDiam P ≤ orderDiam P + C

/-- Question 7.2 (l. 226-227): "Is the supremum of `diam O(P) / diam C(P)` over connected finite posets `P` finite?" —
some constant `C` has `diam O(P) ≤ C · diam C(P)` for every connected finite poset `P` (a connected poset is nonempty,
so `∅` and a singleton are two distinct antichains and `diam C(P) ≥ 1`; the bound is the finiteness of the
supremum). -/
def question_7_2 : Prop :=
  ∃ C : ℕ, ∀ (P : Type) [Fintype P] [PartialOrder P], IsConnPoset P → orderDiam P ≤ (C : ℕ∞) * chainDiam P

end LeeDiam
