/-
Cereceda/Defs/Minor.lean — graph minors by minor models (branch sets), and the four branch sets of `J_ℓ` named in
Remark 4.8 (i) (short v3.90 l. 718-720).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE. Mathlib has no graph minors. We use the standard definition by minor models: `G` has `H` as a minor
exactly when `G` has pairwise disjoint, nonempty vertex sets `B x`, one for each vertex `x` of `H` (the branch sets),
each inducing a connected subgraph of `G`, with an edge of `G` between `B x` and `B y` for every edge `x y` of `H`.
(Contracting each `B x` to one vertex and deleting the other vertices and edges then gives `H`.) Remark 4.8 (i) uses
exactly this form: "the sets ... are disjoint, each induces a connected subgraph, and any two of them are joined by an
edge".
-/
import Cereceda.Defs.LowerBound

namespace Cereceda

/-- `B` is a minor model of `H` in `G`: the branch sets `B x` are nonempty, pairwise disjoint, each induces a connected
subgraph of `G`, and `G` has an edge between `B x` and `B y` for every edge `x y` of `H`. -/
structure IsMinorModel {V W : Type} (H : SimpleGraph W) (G : SimpleGraph V) (B : W → Set V) : Prop where
  nonempty : ∀ x, (B x).Nonempty
  disjoint : ∀ x y, x ≠ y → Disjoint (B x) (B y)
  connected : ∀ x, (G.induce (B x)).Connected
  adj : ∀ x y, H.Adj x y → ∃ a ∈ B x, ∃ b ∈ B y, G.Adj a b

/-- `G` has `H` as a minor: some minor model of `H` in `G` exists. -/
def HasMinor {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ B : W → Set V, IsMinorModel H G B

/-- The branch sets of the `K_4` minor of `J_n` in Remark 4.8 (i) (v3.90 l. 718-720): `{a_1, v_1, v_9, v_10, v_11}`,
`{a_2, v_2}`, `{a_3, v_3}` and `{a_0, v_4, …, v_8}`, as `Jbranch n 0`, …, `Jbranch n 3`. As in `Jgraph`, the path
vertex `v_i` is `Sum.inl` of the 0-based index `i - 1`, and `a_j` is `Sum.inr j`. -/
def Jbranch (n : ℕ) (x : Fin 4) : Set (Fin n ⊕ Fin 4) :=
  {y | match y with
    | .inl i => (x = 0 ∧ (i.val = 0 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10)) ∨ (x = 1 ∧ i.val = 1) ∨
        (x = 2 ∧ i.val = 2) ∨ (x = 3 ∧ 3 ≤ i.val ∧ i.val ≤ 7)
    | .inr j => (x = 0 ∧ j = 1) ∨ (x = 1 ∧ j = 2) ∨ (x = 2 ∧ j = 3) ∨ (x = 3 ∧ j = 0)}

end Cereceda
