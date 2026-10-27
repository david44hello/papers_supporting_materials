/-
HibiLiLean — maximal refinement cells, top cells, and the connected subdivision dual graph.
-/
import HibiLi.Polytope.RefinementSubdivision
import HibiLi.Polytope.SubdivisionPurity
import HibiLi.Polytope.SubdivisionTransport
import HibiLi.Polytope.GraphCells

namespace HibiLi.Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

noncomputable def refinementCells (face : Set (switch.P' → ℝ)) : Finset (Set (switch.P' → ℝ)) :=
  (switch.restrict_finite switch.cellsR_finite face).toFinset

theorem mem_refinementCells {face cell : Set (switch.P' → ℝ)} :
    cell ∈ switch.refinementCells face ↔ cell ∈ switch.restrict switch.cellsR face := by
  simp [refinementCells]

theorem refinement_max_is_top {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) : cell.1 ∈ switch.topCells switch.cellsR face :=
  ⟨switch.mem_refinementCells.mp cell.2.1,
    subdivision_max_adim (switch.B_isPolytope.face hface) hface.1 (switch.restrict_cellsR_subdivision hface) cell⟩

theorem refinement_top_is_max {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : switch.topCells switch.cellsR face) :
    cell.1 ∈ switch.refinementCells face ∧
      ∀ other ∈ switch.refinementCells face, cell.1 ⊆ other → other = cell.1 := by
  refine ⟨switch.mem_refinementCells.mpr cell.2.1, ?_⟩
  intro other member inside
  have restricted := switch.mem_refinementCells.mp member
  have cellR := switch.restrict_cellsR_subset hface cell.2.1
  have otherR := switch.restrict_cellsR_subset hface restricted
  have nonempty : (cell.1 ∩ other).Nonempty := cell.2.1.1.mono fun _ member => ⟨member, inside member⟩
  have face_of_other : IsFace other cell.1 := by
    have result := (switch.cellsR_inter_faces cellR otherR nonempty).2
    simpa only [Set.inter_eq_left.mpr inside] using result
  have lower : adim cell.1 ≤ adim other := Submodule.finrank_mono (vectorSpan_mono ℝ inside)
  have upper : adim other ≤ adim face :=
    Submodule.finrank_mono (vectorSpan_mono ℝ (switch.restrict_cell_subset restricted))
  have dimension := cell.2.2
  exact (face_of_other.eq_of_adim_eq (by omega)).symm

noncomputable def refinementMaxEquivTop {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    MaxSubdivisionCell (switch.refinementCells face) ≃ switch.topCells switch.cellsR face where
  toFun cell := ⟨cell.1, switch.refinement_max_is_top hface cell⟩
  invFun cell := ⟨cell.1, switch.refinement_top_is_max hface cell⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem refinementDual_connected {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    (subdivisionDualGraph (switch.refinementCells face)).Connected :=
  subdivisionDualGraph_connected face (switch.refinementCells face)
    (switch.B_isPolytope.face hface) hface.1 (switch.restrict_cellsR_subdivision hface)

noncomputable def refinementMaxEdge {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) : (switch.graphG face).edgeSet :=
  (switch.graphEdgeEquivTopR hface).symm (switch.refinementMaxEquivTop hface cell)

theorem refinementMaxEdge_cell {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) :
    (switch.graphEdgeCell face (switch.refinementMaxEdge hface cell)).1 = cell.1 :=
  congrArg Subtype.val ((switch.graphEdgeEquivTopR hface).apply_symm_apply (switch.refinementMaxEquivTop hface cell))

noncomputable def refinementMaxPair {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) :
    switch.topCells switch.cellsS face × switch.topCells switch.cellsT face :=
  switch.graphEdgePair face (switch.refinementMaxEdge hface cell)

theorem refinementMaxPair_inter {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) :
    (switch.refinementMaxPair hface cell).1.1 ∩ (switch.refinementMaxPair hface cell).2.1 = cell.1 :=
  switch.refinementMaxEdge_cell hface cell

theorem refinementMaxPair_adj {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) :
    (switch.graphG face).Adj (Sum.inl (switch.refinementMaxPair hface cell).1)
      (Sum.inr (switch.refinementMaxPair hface cell).2) :=
  (switch.graphEdgePair_spec face (switch.refinementMaxEdge hface cell)).2

end HibiLi.Switch
