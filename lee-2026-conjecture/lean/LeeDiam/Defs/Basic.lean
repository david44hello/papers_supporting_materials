/-
LeeDiam/Defs/Basic.lean — the words of paper 004 (short v1.50): comparability, connected sets, ideals, antichains, the
order and chain polytopes, the graph of a polytope, the two diameters, the width, and the Lee (2026) conjecture.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against short v1.50 (P4_short_v1.50.tex), Section 1 (l. 50-61) and Section 2 (l. 139). Polytopes,
faces and indicator vectors come from the polytope library of a companion formalization (LeeDiam/Vendor/HibiLi,
copied; only import paths and lint changed): `HibiLi.IsFace` = nonempty exposed face, `HibiLi.chainPolytope`,
`HibiLi.setVector S` = indicator vector of `S`.
-/
import LeeDiam.Vendor.HibiLi.Defs.Poset

namespace LeeDiam

section Order

variable {P : Type} [PartialOrder P]

/-- Two elements are comparable (v1.50 l. 50): one is smaller than the other (comparable elements are distinct). -/
def Comp (p q : P) : Prop := p < q ∨ q < p

variable (P) in
/-- The comparability graph of `P` (v1.50 l. 50): two elements are joined when one is smaller than the other. -/
def compGraph : SimpleGraph P where
  Adj := Comp
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (lt_irrefl _) (lt_irrefl _)⟩

/-- A connected set (v1.50 l. 139): nonempty, and the comparability graph induces a connected graph on it (Mathlib's
`Connected` includes nonemptiness). -/
def IsConnSet (D : Set P) : Prop := ((compGraph P).induce D).Connected

/-- An ideal (v1.50 l. 50): a subset that contains, with each of its elements, every smaller element. -/
abbrev IsIdeal (I : Set P) : Prop := IsLowerSet I

/-- An antichain (v1.50 l. 50): a set of pairwise incomparable elements. -/
abbrev IsAntichainSet (A : Set P) : Prop := IsAntichain (· ≤ ·) A

variable (P) in
/-- `P` is connected (v1.50 l. 50): its comparability graph is connected (so `P` is nonempty). -/
def IsConnPoset : Prop := (compGraph P).Connected

end Order

section Polytopes

variable (P : Type) [Fintype P] [PartialOrder P]

/-- The order polytope `O(P)` of the paper (v1.50 l. 50 and its footnote): `{x ∈ [0,1]^P : x_q ≤ x_p whenever p ≤ q}`,
whose vertices are the indicator vectors of the ideals. (Stanley's order polytope, `HibiLi.orderPolytope P`, uses filters;
`x ↦ 1 - x` carries it onto this one: claim `sec1_footnote_stanley`.) -/
def orderPolytope : Set (P → ℝ) := {x | (∀ p, 0 ≤ x p ∧ x p ≤ 1) ∧ ∀ p q, p ≤ q → x q ≤ x p}

/-- The chain polytope `C(P)` (v1.50 l. 50; Stanley): `{x ≥ 0 : Σ_{p ∈ K} x_p ≤ 1 for every chain K}`. -/
abbrev chainPolytope : Set (P → ℝ) := HibiLi.chainPolytope P

variable {P} in
/-- The graph of a polytope `Q` (v1.50 l. 50): its vertices are the vertices of `Q` (the points `v` with `{v}` a face);
two vertices are adjacent when the segment between them is a face of `Q` (an edge of `Q`). -/
def polyGraph (Q : Set (P → ℝ)) : SimpleGraph {v : P → ℝ // HibiLi.IsFace Q {v}} where
  Adj u v := u ≠ v ∧ HibiLi.IsFace Q (segment ℝ u.1 v.1)
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The order diameter `diam O(P)` (v1.50 l. 50): the diameter of the graph of `O(P)` (`⊤` if it is disconnected). -/
noncomputable def orderDiam : ℕ∞ := (polyGraph (orderPolytope P)).ediam

/-- The chain diameter `diam C(P)` (v1.50 l. 50): the diameter of the graph of `C(P)` (`⊤` if it is disconnected). -/
noncomputable def chainDiam : ℕ∞ := (polyGraph (chainPolytope P)).ediam

/-- The width `w(P)` (v1.50 l. 61): the largest size of an antichain. -/
noncomputable def width : ℕ := sSup {n | ∃ A : Finset P, IsAntichain (· ≤ ·) (A : Set P) ∧ A.card = n}

end Polytopes

/-- The Lee (2026) conjecture [Lee26, Conjecture 29] (v1.50 l. 52-57), as a DEFINITION (the paper disproves it): for
every connected finite poset `P`, `|diam O(P) - diam C(P)| ≤ 1`. -/
def LeeConjecture : Prop :=
  ∀ (P : Type) [Fintype P] [PartialOrder P], IsConnPoset P →
    orderDiam P ≤ chainDiam P + 1 ∧ chainDiam P ≤ orderDiam P + 1

end LeeDiam
