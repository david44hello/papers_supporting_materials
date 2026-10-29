/-
Cereceda/Defs/Intro.lean — words used only in the introduction: once-subdivided graphs, the Grundy number (as in
[BB18]), tree decompositions and treewidth.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against short v3.90 l. 132-171 (the classes (i)-(v), l. 132-144; chordal bipartite graphs, l. 161;
the Grundy number and first-fit colourings, l. 164-166; subdivisions, l. 166-171) and [BB18] p. 2.
-/
import Cereceda.Defs.Basic

namespace Cereceda

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The graph obtained from `G` by subdividing every edge once: vertices `V ⊕ E(G)`, an original vertex `v` is
joined to the subdivision vertex of every edge `e ∋ v`; there are no other edges. -/
def subdivision (G : SimpleGraph V) : SimpleGraph (V ⊕ G.edgeSet) where
  Adj a b := match a, b with
    | .inl v, .inr e => v ∈ (e : Sym2 V)
    | .inr e, .inl v => v ∈ (e : Sym2 V)
    | _, _ => False
  symm := ⟨fun a b h => by rcases a with a | a <;> rcases b with b | b <;> simp_all⟩
  loopless := ⟨fun a h => by rcases a with a | a <;> simp_all⟩

instance (G : SimpleGraph V) : DecidableRel (subdivision G).Adj := fun a b =>
  match a, b with
  | .inl v, .inr e => inferInstanceAs (Decidable (v ∈ (e : Sym2 V)))
  | .inr e, .inl v => inferInstanceAs (Decidable (v ∈ (e : Sym2 V)))
  | .inl _, .inl _ => inferInstanceAs (Decidable False)
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

/-- The greedy colouring `C(G, O)` relative to an order `O = ρ` ([BB18] p. 2): every vertex has the smallest colour
(colours `0, 1, 2, …` in `ℕ`) that does not appear on its EARLIER neighbours. -/
def IsGreedyRel (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n) (c : V → ℕ) : Prop :=
  ∀ v, c v ∉ (univ.filter (fun u => G.Adj v u ∧ ρ u < ρ v)).image c ∧
    ∀ y < c v, y ∈ (univ.filter (fun u => G.Adj v u ∧ ρ u < ρ v)).image c

/-- The Grundy number `χ_g(G)` ([BB18] p. 2): the maximum, over all orders `O`, of the number of colours used in the
greedy colouring `C(G, O)`. -/
noncomputable def grundyNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  sSup {k | ∃ ρ : V ≃ Fin (Fintype.card V), ∃ c : V → ℕ, IsGreedyRel G ρ c ∧ (univ.image c).card = k}

/-- A tree decomposition of `G`: a finite tree `T` on `ι` with bags `bag i ⊆ V`; every vertex and every edge of `G`
lies in some bag, and for every vertex `v` the nodes whose bags contain `v` induce a connected subtree. -/
structure TreeDecomposition (G : SimpleGraph V) (ι : Type) [Fintype ι] where
  T : SimpleGraph ι
  isTree : T.IsTree
  bag : ι → Finset V
  cover_vertex : ∀ v, ∃ i, v ∈ bag i
  cover_edge : ∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  subtree : ∀ v, (T.induce {i | v ∈ bag i}).Connected

/-- The width of a tree decomposition: the largest bag size minus one. -/
def TreeDecomposition.width {G : SimpleGraph V} {ι : Type} [Fintype ι] (D : TreeDecomposition G ι) : ℕ :=
  univ.sup (fun i => (D.bag i).card) - 1

/-- The treewidth of `G`: the least width of a tree decomposition (on any finite index type). -/
noncomputable def treewidth (G : SimpleGraph V) : ℕ :=
  sInf {w | ∃ (ι : Type) (_ : Fintype ι) (D : TreeDecomposition G ι), D.width = w}

/-- The maximum average degree `mad(G)`: the largest value of `2|E(G[s])| / |s|` over nonempty vertex sets `s`
(`0` for the empty graph). -/
noncomputable def mad (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sSup {r | ∃ s : Finset V, s.Nonempty ∧
    r = 2 * ((G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ s)).card : ℝ) / s.card}

/-- A chordal bipartite graph: bipartite, and every cycle of length at least `6` has a chord (an edge of `G` between two
vertices of the cycle that is not an edge of the cycle). -/
def IsChordalBipartite (G : SimpleGraph V) : Prop :=
  G.IsBipartite ∧ ∀ (v : V) (w : G.Walk v v), w.IsCycle → 6 ≤ w.length →
    ∃ x ∈ w.support, ∃ y ∈ w.support, G.Adj x y ∧ s(x, y) ∉ w.edges

end Cereceda
