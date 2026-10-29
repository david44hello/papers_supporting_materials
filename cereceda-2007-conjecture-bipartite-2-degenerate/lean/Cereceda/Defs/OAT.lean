/-
Cereceda/Defs/OAT.lean — the OAT graphs of Biedl, Lubiw and Merkel [BLM21] (short v3.90 l. 179-182): built from single
vertices by disjoint unions, joins, adding a vertex u with N(u) ⊆ N(v), and attaching a clique to a vertex.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Classes

namespace Cereceda

open SimpleGraph

/-! ### The OAT operations -/

/-- The join of `G` and `H`: their disjoint union plus every edge between them (v3.90 l. 181). -/
def joinGraph {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj
    | Sum.inl a, Sum.inl a' => G.Adj a a'
    | Sum.inr b, Sum.inr b' => H.Adj b b'
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm := ⟨by
    rintro (a | b) (a' | b') h
    · exact G.adj_symm h
    · trivial
    · trivial
    · exact H.adj_symm h⟩
  loopless := ⟨by
    rintro (a | b) h
    · exact G.irrefl h
    · exact H.irrefl h⟩

/-- Add one new vertex (`none`) adjacent exactly to the vertices of `S`. -/
def addVertex {V : Type} (G : SimpleGraph V) (S : Set V) : SimpleGraph (Option V) where
  Adj
    | some a, some b => G.Adj a b
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | none, none => False
  symm := ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact G.adj_symm h⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact G.irrefl h⟩

/-- Attach a clique on `Fin k` to the vertex `v`: the clique's vertices are pairwise adjacent and each is joined to `v`. -/
def attachClique {V : Type} (G : SimpleGraph V) (v : V) (k : ℕ) : SimpleGraph (V ⊕ Fin k) where
  Adj
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr _ => a = v
    | Sum.inr _, Sum.inl b => b = v
    | Sum.inr i, Sum.inr j => i ≠ j
  symm := ⟨by
    rintro (a | i) (b | j) h
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact fun hji => h hji.symm⟩
  loopless := ⟨by
    rintro (a | i) h
    · exact G.irrefl h
    · exact h rfl⟩

/-- OAT graphs (v3.90 l. 180-182, after [BLM21, Def. 1]): built from single vertices by disjoint unions, joins, adding a
vertex `u` with `N(u) ⊆ N(v)` for an existing vertex `v`, and attaching a clique to a vertex; closed under isomorphism. -/
inductive IsOAT : {V : Type} → SimpleGraph V → Prop
  | single : IsOAT (⊥ : SimpleGraph Unit)
  | union {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} : IsOAT G → IsOAT H → IsOAT (G ⊕g H)
  | join {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} : IsOAT G → IsOAT H → IsOAT (joinGraph G H)
  | addSub {V : Type} {G : SimpleGraph V} (v : V) (S : Set V) : IsOAT G → S ⊆ G.neighborSet v →
      IsOAT (addVertex G S)
  | attach {V : Type} {G : SimpleGraph V} (v : V) (k : ℕ) : IsOAT G → IsOAT (attachClique G v k)
  | iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} : IsOAT G → Nonempty (G ≃g H) → IsOAT H

section Adj

variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

@[simp] theorem joinGraph_adj_inl_inl (a a' : V) : (joinGraph G H).Adj (Sum.inl a) (Sum.inl a') ↔ G.Adj a a' :=
  Iff.rfl

@[simp] theorem joinGraph_adj_inr_inr (b b' : W) : (joinGraph G H).Adj (Sum.inr b) (Sum.inr b') ↔ H.Adj b b' :=
  Iff.rfl

@[simp] theorem joinGraph_adj_inl_inr (a : V) (b : W) : (joinGraph G H).Adj (Sum.inl a) (Sum.inr b) ↔ True :=
  Iff.rfl

@[simp] theorem joinGraph_adj_inr_inl (b : W) (a : V) : (joinGraph G H).Adj (Sum.inr b) (Sum.inl a) ↔ True :=
  Iff.rfl

end Adj

end Cereceda
