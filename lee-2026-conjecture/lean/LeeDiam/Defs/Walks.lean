/-
LeeDiam/Defs/Walks.lean — walks, splits and components (paper 004, short v1.50, Section 2, l. 139-163).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against v1.50 l. 139 ("components"), l. 147 (walks) and l. 163 (splits).
-/
import LeeDiam.Defs.Basic

namespace LeeDiam

variable {P : Type} [PartialOrder P]

/-- A convex set (v1.50 l. 139): `x < y < z` and `x, z ∈ D` imply `y ∈ D`. -/
def IsConvexSet (D : Set P) : Prop := ∀ x y z, x < y → y < z → x ∈ D → z ∈ D → y ∈ D

/-- The open neighbourhood `N(S)` in the comparability graph (v1.50, proof of Lemma 2.4): the elements comparable to
some element of `S`. -/
def nbhd (S : Set P) : Set P := {x | ∃ z ∈ S, Comp x z}

/-- `π_R(S) = S ∪ (R \ N(S))` (v1.50, proof of Lemma 2.4). -/
def proj (R S : Set P) : Set P := S ∪ (R \ nbhd S)

/-- A component of `D` (v1.50 l. 139: "The components of a set are its maximal connected subsets"). -/
def IsComponent (C D : Set P) : Prop :=
  IsConnSet C ∧ C ⊆ D ∧ ∀ C' : Set P, IsConnSet C' → C ⊆ C' → C' ⊆ D → C' = C

/-- `C` is a union of components of `D`: a subset of `D` closed under comparability inside `D` (an element of `D`
comparable to an element of `C` is in `C`). `isCompUnion_iff` (a claim) proves that this is exactly a union of
components of `D`. -/
def IsCompUnion (C D : Set P) : Prop := C ⊆ D ∧ ∀ x ∈ C, ∀ y ∈ D, Comp x y → y ∈ C

/-- The number of components of `D`: the connected components of the comparability graph induced on `D`. -/
noncomputable def numComp (D : Set P) : ℕ := Nat.card ((compGraph P).induce D).ConnectedComponent

/-- A walk (v1.50 l. 147): a nonempty sequence `(X_0, …, X_n)` of antichains, its states, in which every difference
`X_{t-1} △ X_t` is nonempty and connected. Its length `ℓ(W) = n` is `W.length - 1`. -/
def IsWalk (W : List (Set P)) : Prop :=
  W ≠ [] ∧ (∀ X ∈ W, IsAntichainSet X) ∧ W.IsChain (fun X Y => IsConnSet (symmDiff X Y))

/-- `W` is a walk from `X` to `Y`. -/
def IsWalkFromTo (W : List (Set P)) (X Y : Set P) : Prop := IsWalk W ∧ W.head? = some X ∧ W.getLast? = some Y

/-- A split of `U` (v1.50 l. 163): a pair `(A, B)` of disjoint sets whose union `U` is an antichain. -/
def IsSplit (A B U : Set P) : Prop := Disjoint A B ∧ A ∪ B = U ∧ IsAntichainSet U

end LeeDiam
