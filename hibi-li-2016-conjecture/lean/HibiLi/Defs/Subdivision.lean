/-
HibiLiLean — the general finite-subdivision interface.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Polytope

namespace HibiLi

/-- A subdivision of `base` (paper v1.00, lines 271–274): a finite family of nonempty polytopes covering `base`
exactly, closed under nonempty faces, any two meeting in a common face (or not at all).  The relative interiors of its
cells partition `base`: `subdivision_relint_partition` (HibiLi/Polytope/RelintPartition.lean). -/
def IsFinitePolytopalSubdivision {ι : Type*} [Fintype ι]
    (base : Set (ι → ℝ)) (cells : Finset (Set (ι → ℝ))) : Prop :=
  (∀ cell ∈ cells, IsPolytope cell ∧ cell.Nonempty) ∧
  (⋃₀ (cells : Set (Set (ι → ℝ)))) = base ∧
  (∀ cell ∈ cells, ∀ face, IsFace cell face → face ∈ cells) ∧
  (∀ left ∈ cells, ∀ right ∈ cells,
    (left ∩ right).Nonempty →
      IsFace left (left ∩ right) ∧ IsFace right (left ∩ right))

abbrev MaxSubdivisionCell {ι : Type*} [Fintype ι]
    (cells : Finset (Set (ι → ℝ))) :=
  {cell : Set (ι → ℝ) // cell ∈ cells ∧
    ∀ other ∈ cells, cell ⊆ other → other = cell}

def subdivisionDualGraph {ι : Type*} [Fintype ι]
    (cells : Finset (Set (ι → ℝ))) : SimpleGraph (MaxSubdivisionCell cells) where
  Adj left right := left ≠ right ∧ (left.1 ∩ right.1).Nonempty ∧
    IsFace left.1 (left.1 ∩ right.1) ∧ IsFace right.1 (left.1 ∩ right.1) ∧
    adim (left.1 ∩ right.1) + 1 = adim left.1 ∧
    adim (left.1 ∩ right.1) + 1 = adim right.1
  symm := ⟨by
    intro left right adjacent
    simpa only [Set.inter_comm, ne_comm, and_comm, and_left_comm, and_assoc] using adjacent⟩
  loopless := ⟨fun _ adjacent => adjacent.1 rfl⟩

end HibiLi
