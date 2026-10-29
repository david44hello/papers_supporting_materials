/-
Cereceda/Defs/ColourDense.lean — class (iii) of Section 1: the k-colour-dense graphs of [BJLPP14, Section 3]
(short v3.90 l. 150-158).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE (v3.90 l. 151-158, verbatim): "A separator of a graph is a set S of vertices whose removal increases the
number of components, and identifying two vertices u and v replaces them by one vertex adjacent to all their
neighbours. A 3-colourable graph is 3-colour-dense if either it is a disjoint union of cliques with at most three
vertices each, or it has a separator S and vertices u and v with these four properties: u and v lie in different
components of the graph minus S; S ⊆ N(v); the component D of u in the graph minus S satisfies |D| = 1 or
|D ∪ S| ≤ 3; and identifying u with v gives a 3-colour-dense graph. With 2 in place of 3, this defines the
2-colour-dense graphs".
-/
import Mathlib

namespace Cereceda

/-- Identifying `u` with `v` (v3.90 l. 152: "replaces them by one vertex adjacent to all their neighbours"): the
graph on the vertices other than `u`, in which the merged vertex is `v`; `v` is adjacent to every neighbour of `u` and
every neighbour of `v`, and two vertices other than `v` are adjacent exactly when they are in `G`. -/
def identify {V : Type} (G : SimpleGraph V) (u v : V) : SimpleGraph {w : V // w ≠ u} where
  Adj a b := a ≠ b ∧ (G.Adj a b ∨ (a.1 = v ∧ G.Adj u b) ∨ (b.1 = v ∧ G.Adj u a))
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `G` is a disjoint union of cliques with at most `k` vertices each (v3.90 l. 153): adjacency is transitive on
distinct vertices (so every component is a clique), and every closed neighbourhood (= the component) has at most `k`
vertices. -/
def IsCliqueUnionAtMost {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (∀ x y z, G.Adj x y → G.Adj y z → x ≠ z → G.Adj x z) ∧ ∀ x, {y | y = x ∨ G.Adj x y}.ncard ≤ k

/-- The component `D` of `u` in the graph minus `S` (v3.90 l. 155), as a set of vertices of `G` (empty if
`u ∈ S`). -/
def compMinus {V : Type} (G : SimpleGraph V) (S : Set V) (u : V) : Set V :=
  {w | ∃ (hu : u ∉ S) (hw : w ∉ S), (G.induce {x | x ∉ S}).Reachable ⟨u, hu⟩ ⟨w, hw⟩}

/-- `S` is a separator of `G` (v3.90 l. 151: "a set S of vertices whose removal increases the number of components";
[BJLPP14] txt l. 171-172, verbatim: "A separator of a graph G = (V, E) is a set S ⊂ V such that G − S has more connected
components than G"). -/
def IsSeparator {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  Nat.card G.ConnectedComponent < Nat.card (G.induce {x | x ∉ S}).ConnectedComponent

/-- The `k`-colour-dense graphs of [BJLPP14, Section 3] (l. 193-207; v3.90 l. 153-158; `k = 3`: class (iii)). A finite
`k`-colourable graph is `k`-colour-dense if it is a disjoint union of cliques with at most `k` vertices each (`base`),
or if it has a separator `S` and vertices `u, v ∉ S` in different components of `G - S` with `S ⊆ N(v)`, the component
`D` of `u` in `G - S` has `|D| = 1` or `|D ∪ S| ≤ k`, and identifying `u` with `v` gives a `k`-colour-dense graph
(`step`). -/
inductive IsColourDense (k : ℕ) : {V : Type} → SimpleGraph V → Prop
  | base {V : Type} [Finite V] (G : SimpleGraph V) : G.Colorable k → IsCliqueUnionAtMost G k → IsColourDense k G
  | step {V : Type} [Finite V] (G : SimpleGraph V) (S : Set V) (u v : V) : G.Colorable k → IsSeparator G S →
      u ∉ S → v ∉ S → v ∉ compMinus G S u → S ⊆ G.neighborSet v →
      ((compMinus G S u).ncard = 1 ∨ (compMinus G S u ∪ S).ncard ≤ k) →
      IsColourDense k (identify G u v) → IsColourDense k G

end Cereceda
