/-
Cereceda/Defs/Classes.lean — two graph classes of Section 1 (short v3.90): semi-false graphs (`IsSemiFalse`, l. 158-162;
they lie in class (iii)) and distance-hereditary graphs (`IsDistanceHereditary`, l. 174-176).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Intro

namespace Cereceda

section SemiFalse

variable {V : Type} [Fintype V]

/-- A *semi-false* graph (v3.90 l. 158-160): it "can be built from isolated vertices by repeatedly adding a vertex
adjacent to exactly one existing vertex, or a vertex `u` with `N(u) ⊆ N(v)` for an existing vertex `v`". A construction is the order `ρ` in which
the vertices are added (the starting isolated vertices first). When `u` is added, its neighbours are its neighbours `w`
with `ρ w < ρ u`, and an earlier vertex `v` then has as neighbours its neighbours added before `u`. So for each `u`:
it has no earlier neighbour (a starting isolated vertex; later, this is the case `N(u) = ∅ ⊆ N(v)`), or exactly one
(adjacent to exactly one existing vertex), or some earlier vertex `v` is adjacent to all its earlier neighbours (`N(u) ⊆ N(v)`). -/
def IsSemiFalse (G : SimpleGraph V) : Prop :=
  ∃ ρ : V ≃ Fin (Fintype.card V), ∀ u : V,
    (∀ w, G.Adj u w → ¬ ρ w < ρ u) ∨
    (∃ w, G.Adj u w ∧ ρ w < ρ u ∧ ∀ w', G.Adj u w' → ρ w' < ρ u → w' = w) ∨
    (∃ v, ρ v < ρ u ∧ ∀ w, G.Adj u w → ρ w < ρ u → G.Adj v w)

end SemiFalse

section DistanceHereditary

variable {V : Type}

/-- A graph is *distance-hereditary* (v3.90 l. 175-176: "a graph in which any two vertices of a connected induced
subgraph are at the same distance in the subgraph as in the whole graph"): every connected induced subgraph
is isometric. (Howorka, Quart. J. Math. Oxford 28 (1977) 417-420; the class of [BB18, Thm. 4].) -/
def IsDistanceHereditary (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, (G.induce s).Connected → ∀ u v : s, (G.induce s).dist u v = G.dist u.1 v.1

end DistanceHereditary

end Cereceda
