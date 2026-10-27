/-
HibiLiLean — paper Lemma 3.5(ii), connectivity of the switch bipartite graph.
-/
import HibiLi.Polytope.RefinementAdjacency
import HibiLi.Polytope.RefinementCover

namespace HibiLi

private theorem eq_of_common_full_dim {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {left right common : Set V} {dim : ℕ}
    (nonempty : common.Nonempty) (inside_left : common ⊆ left) (inside_right : common ⊆ right)
    (common_dim : adim common = dim) (left_dim : adim left = dim)
    (unique : (left ∩ right).Nonempty → adim (left ∩ right) = dim → left = right) : left = right := by
  have inside : common ⊆ left ∩ right := fun _ member => ⟨inside_left member, inside_right member⟩
  have lower : adim common ≤ adim (left ∩ right) := Submodule.finrank_mono (vectorSpan_mono ℝ inside)
  have upper : adim (left ∩ right) ≤ adim left := Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  exact unique (nonempty.mono inside) (by omega)

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

noncomputable def refinementMaxLeft {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (cell : MaxSubdivisionCell (switch.refinementCells face)) :
    switch.topCells switch.cellsS face ⊕ switch.topCells switch.cellsT face :=
  Sum.inl (switch.refinementMaxPair hface cell).1

theorem refinement_adjacent_reachable {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (transverse : switch.Transverse)
    {left right : MaxSubdivisionCell (switch.refinementCells face)}
    (adjacent : (subdivisionDualGraph (switch.refinementCells face)).Adj left right) :
    (switch.graphG face).Reachable (switch.refinementMaxLeft hface left) (switch.refinementMaxLeft hface right) := by
  change (switch.graphG face).Reachable (Sum.inl (switch.refinementMaxPair hface left).1)
    (Sum.inl (switch.refinementMaxPair hface right).1)
  rcases switch.refinement_adjacent_pairs hface transverse left right adjacent with same | same
  · rw [same]
  · have first := (switch.refinementMaxPair_adj hface left).reachable
    have second := (switch.refinementMaxPair_adj hface right).symm.reachable
    rw [same] at first
    exact first.trans second

theorem refinement_reachable_lift {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (transverse : switch.Transverse)
    {left right : MaxSubdivisionCell (switch.refinementCells face)}
    (reachable : (subdivisionDualGraph (switch.refinementCells face)).Reachable left right) :
    (switch.graphG face).Reachable (switch.refinementMaxLeft hface left) (switch.refinementMaxLeft hface right) := by
  obtain ⟨walk⟩ := reachable
  induction walk with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons adjacent rest induction =>
    exact (switch.refinement_adjacent_reachable hface transverse adjacent).trans induction

theorem graphVertex_reaches_max {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (vertex : switch.topCells switch.cellsS face ⊕ switch.topCells switch.cellsT face) :
    ∃ maximal : MaxSubdivisionCell (switch.refinementCells face),
      (switch.graphG face).Reachable vertex (switch.refinementMaxLeft hface maximal) := by
  classical
  cases vertex with
  | inl cell =>
    have member := switch.restrict_cellsS_subset hface cell.2.1
    obtain ⟨refinement, in_refinement⟩ := switch.RR_nonempty_of_mem_cellsS member
    have inside : refinement ⊆ face := in_refinement.2.1.trans (switch.restrict_cell_subset cell.2.1)
    have dimension : adim refinement = adim face := in_refinement.2.2.trans cell.2.2
    have top : refinement ∈ switch.topCells switch.cellsR face :=
      ⟨⟨in_refinement.1.1, refinement, in_refinement.1, (Set.inter_eq_left.mpr inside).symm⟩, dimension⟩
    let maximal := (switch.refinementMaxEquivTop hface).symm ⟨refinement, top⟩
    have representation : (switch.refinementMaxPair hface maximal).1.1 ∩
        (switch.refinementMaxPair hface maximal).2.1 = refinement :=
      switch.refinementMaxPair_inter hface maximal
    have chosen_inside : refinement ⊆ (switch.refinementMaxPair hface maximal).1.1 := by
      rw [← representation]
      exact Set.inter_subset_left
    have same : cell.1 = (switch.refinementMaxPair hface maximal).1.1 :=
      eq_of_common_full_dim in_refinement.1.1 in_refinement.2.1 chosen_inside dimension cell.2.2
        (switch.topCellsS_eq_of_full_inter hface cell.2 (switch.refinementMaxPair hface maximal).1.2)
    refine ⟨maximal, ?_⟩
    change (switch.graphG face).Reachable (Sum.inl cell) (Sum.inl (switch.refinementMaxPair hface maximal).1)
    rw [show cell = (switch.refinementMaxPair hface maximal).1 from Subtype.ext same]
  | inr cell =>
    have member := switch.restrict_cellsT_subset hface cell.2.1
    obtain ⟨refinement, in_refinement⟩ := switch.RR_nonempty_of_mem_cellsT member
    have inside : refinement ⊆ face := in_refinement.2.1.trans (switch.restrict_cell_subset cell.2.1)
    have dimension : adim refinement = adim face := in_refinement.2.2.trans cell.2.2
    have top : refinement ∈ switch.topCells switch.cellsR face :=
      ⟨⟨in_refinement.1.1, refinement, in_refinement.1, (Set.inter_eq_left.mpr inside).symm⟩, dimension⟩
    let maximal := (switch.refinementMaxEquivTop hface).symm ⟨refinement, top⟩
    have representation : (switch.refinementMaxPair hface maximal).1.1 ∩
        (switch.refinementMaxPair hface maximal).2.1 = refinement :=
      switch.refinementMaxPair_inter hface maximal
    have chosen_inside : refinement ⊆ (switch.refinementMaxPair hface maximal).2.1 := by
      rw [← representation]
      exact Set.inter_subset_right
    have same : cell.1 = (switch.refinementMaxPair hface maximal).2.1 :=
      eq_of_common_full_dim in_refinement.1.1 in_refinement.2.1 chosen_inside dimension cell.2.2
        (switch.topCellsT_eq_of_full_inter hface cell.2 (switch.refinementMaxPair hface maximal).2.2)
    refine ⟨maximal, ?_⟩
    change (switch.graphG face).Reachable (Sum.inr cell) (Sum.inl (switch.refinementMaxPair hface maximal).1)
    rw [show cell = (switch.refinementMaxPair hface maximal).2 from Subtype.ext same]
    exact (switch.refinementMaxPair_adj hface maximal).symm.reachable

end Switch

theorem lemma_3_5_ii_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) : (s.graphG E).Connected := by
  have connected := s.refinementDual_connected hE
  obtain ⟨base⟩ := connected.nonempty
  let : Nonempty (s.topCells s.cellsS E ⊕ s.topCells s.cellsT E) := ⟨s.refinementMaxLeft hE base⟩
  refine ⟨?_⟩
  intro first second
  obtain ⟨firstMax, first_reaches⟩ := s.graphVertex_reaches_max hE first
  obtain ⟨secondMax, second_reaches⟩ := s.graphVertex_reaches_max hE second
  exact first_reaches.trans
    ((s.refinement_reachable_lift hE hT (connected firstMax secondMax)).trans second_reaches.symm)

end HibiLi
