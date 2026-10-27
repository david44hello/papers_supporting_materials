/-
HibiLi/Defs/Polytope.lean — faces, dimensions and face numbers of subsets of a real vector space.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper (v0.70, lines 130–132): "Write F_Q(t) = Σ_{j≥0} f_j(Q) t^j for the face polynomial of a polytope Q (all nonempty
faces, Q included)."  A face is an exposed face (Ziegler, Def. 2.1): Q ∩ {x : c·x = max_Q c}; the zero
functional gives Q itself.  The empty face is excluded.
-/
import Mathlib

namespace HibiLi

open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A polytope: the convex hull of finitely many points (Ziegler, Def. 0.1; the empty polytope is allowed). -/
def IsPolytope (Q : Set V) : Prop := ∃ S : Finset V, Q = convexHull ℝ (S : Set V)

/-- `F` is a nonempty face of `Q`: nonempty and exposed (cut out by maximizing a continuous linear functional). -/
def IsFace (Q F : Set V) : Prop := F.Nonempty ∧ IsExposed ℝ Q F

/-- Affine dimension of a set: the dimension of the direction of its affine hull (meaningful for nonempty sets). -/
noncomputable def adim (F : Set V) : ℕ := Module.finrank ℝ (vectorSpan ℝ F)

/-- The set of `j`-dimensional nonempty faces of `Q`. -/
def faces (Q : Set V) (j : ℕ) : Set (Set V) := {F | IsFace Q F ∧ adim F = j}

/-- `f_j(Q)`, the number of `j`-dimensional nonempty faces of `Q`.  (`ncard` is 0 on infinite sets, so finiteness of
`faces Q j` is proved separately for every polytope we count.) -/
noncomputable def fNum (Q : Set V) (j : ℕ) : ℕ := (faces Q j).ncard

/-- Number of `j`-dimensional members of a family of cells (a polytopal complex or subdivision). -/
noncomputable def cellNum (K : Set (Set V)) (j : ℕ) : ℕ := {A ∈ K | adim A = j}.ncard

/-- `E` is the carrier of the cell `C` in `B`: the smallest face of `B` containing `C` (paper lines 288–289). -/
def IsCarrier (B E C : Set V) : Prop :=
  IsFace B E ∧ C ⊆ E ∧ ∀ E', IsFace B E' → C ⊆ E' → E ⊆ E'

section Poly
variable (N : ℕ)

/-- The face polynomial `F_Q(t) = Σ_j f_j(Q) t^j`, summed over `j ≤ N` (callers take `N` = ambient dimension, which
bounds every face dimension). -/
noncomputable def facePolyUpTo (Q : Set V) : ℤ[X] :=
  ∑ j ∈ Finset.range (N + 1), C (fNum Q j : ℤ) * X ^ j

/-- `F_K(t) = Σ_j (number of j-cells of K) t^j` for a family of cells, summed over `j ≤ N`. -/
noncomputable def cellPolyUpTo (K : Set (Set V)) : ℤ[X] :=
  ∑ j ∈ Finset.range (N + 1), C (cellNum K j : ℤ) * X ^ j

end Poly

section Coord
variable {ι : Type*} [Fintype ι]

/-- Face polynomial of a subset of `ι → ℝ` (dimension bound `card ι`). -/
noncomputable def facePoly (Q : Set (ι → ℝ)) : ℤ[X] := facePolyUpTo (Fintype.card ι) Q

/-- Cell polynomial of a family of cells in `ι → ℝ`. -/
noncomputable def cellPoly (K : Set (Set (ι → ℝ))) : ℤ[X] := cellPolyUpTo (Fintype.card ι) K

end Coord

end HibiLi
