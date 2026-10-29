/-
Cereceda/Defs/Bipartite.lean — the words of Section 3: patterns and kinds of vertices (fixed, leaver, joiner; v3.90
l. 418-421), the colouring `μ` of Definition 3.7 (`IsGreedyMu`), and two kinds of vertices (low swappers, high movers) used by the
proofs in Bip/Basic.lean and Bip/SidesFacts.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against v3.90 Section 3 (l. 418-421 and 514-517). Low swappers and high movers are not
definitions of v3.90: they are words of the Lean proofs only.
The pattern of `v` is `(α v, β v)`; all predicates take `α β` explicitly.
-/
import Cereceda.Defs.Instance

namespace Cereceda

open Finset

variable {W : Type} [Fintype W] [DecidableEq W]

/-- `v` is fixed: `α v = β v`. -/
def IsFixed (α β : W → Fin 4) (v : W) : Prop := α v = β v

/-- `v` is a low swapper: its pattern is `(0,1)` or `(1,0)`. -/
def IsLowSwapper (α β : W → Fin 4) (v : W) : Prop :=
  (α v = 0 ∧ β v = 1) ∨ (α v = 1 ∧ β v = 0)

/-- `v` is a high mover: it is not fixed and has the colour `2` at one end. -/
def IsHighMover (α β : W → Fin 4) (v : W) : Prop :=
  α v ≠ β v ∧ (α v = 2 ∨ β v = 2)

/-- `v` is a leaver: its pattern is `(0, b)` with `b ≠ 0`. -/
def IsLeaver (α β : W → Fin 4) (v : W) : Prop := α v = 0 ∧ β v ≠ 0

/-- `v` is a joiner: its pattern is `(a, 0)` with `a ≠ 0`. -/
def IsJoiner (α β : W → Fin 4) (v : W) : Prop := α v ≠ 0 ∧ β v = 0

/-- Definition 3.7 (the colouring `μ`), v3.90 l. 514-517, as a predicate: `μ(s) = x` and, for `v ≠ s`, `μ(v)` is the least
colour of `L(v)` that is at least `max(α(v), β(v))` and differs from `μ(u)` for every out-neighbour `u` of `v`. -/
def IsGreedyMu (I : Instance W) (α β μ : W → Fin 4) : Prop :=
  μ I.sink = I.x ∧ ∀ v, v ≠ I.sink →
    μ v ∈ I.L v ∧ max (α v) (β v) ≤ μ v ∧ (∀ u ∈ I.out v, μ u ≠ μ v) ∧
      ∀ y ∈ I.L v, max (α v) (β v) ≤ y → (∀ u ∈ I.out v, μ u ≠ y) → μ v ≤ y

end Cereceda
