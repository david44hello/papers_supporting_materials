/-
HibiLiLean — top refinement cells and the bipartite graph edges.
-/
import HibiLi.Polytope.AffinityCells

namespace HibiLi.Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem topCells_finite {family : Set (Set (switch.P' → ℝ))} (finite : family.Finite)
    (face : Set (switch.P' → ℝ)) : (switch.topCells family face).Finite :=
  (switch.restrict_finite finite face).subset fun _ member => member.1

theorem topR_exists_pair {face cell : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (member : cell ∈ switch.topCells switch.cellsR face) :
    ∃ left ∈ switch.topCells switch.cellsS face, ∃ right ∈ switch.topCells switch.cellsT face,
      cell = left ∩ right := by
  have restricted := member.1
  have dimension := member.2
  have nonempty := restricted.1
  have cell_subset : cell ⊆ face := by
    obtain ⟨_, original, _, rfl⟩ := restricted
    exact Set.inter_subset_right
  obtain ⟨_, left, hleft, right, hright, same⟩ := switch.restrict_cellsR_subset hface restricted
  have left_nonempty : (left ∩ face).Nonempty := nonempty.mono fun point member =>
    ⟨(same ▸ member).1, cell_subset member⟩
  have right_nonempty : (right ∩ face).Nonempty := nonempty.mono fun point member =>
    ⟨(same ▸ member).2, cell_subset member⟩
  have left_lower : adim cell ≤ adim (left ∩ face) :=
    Submodule.finrank_mono (vectorSpan_mono ℝ fun _ member => ⟨(same ▸ member).1, cell_subset member⟩)
  have right_lower : adim cell ≤ adim (right ∩ face) :=
    Submodule.finrank_mono (vectorSpan_mono ℝ fun _ member => ⟨(same ▸ member).2, cell_subset member⟩)
  have left_upper : adim (left ∩ face) ≤ adim face :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_right)
  have right_upper : adim (right ∩ face) ≤ adim face :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_right)
  refine ⟨left ∩ face, ⟨⟨left_nonempty, left, hleft, rfl⟩, by omega⟩,
    right ∩ face, ⟨⟨right_nonempty, right, hright, rfl⟩, by omega⟩, ?_⟩
  ext point
  constructor
  · intro member
    exact ⟨⟨(same ▸ member).1, cell_subset member⟩, (same ▸ member).2, cell_subset member⟩
  · intro member
    rw [same]
    exact ⟨member.1.1, member.2.1⟩

theorem top_pairs_eq_of_inter_eq {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (left right : switch.topCells switch.cellsS face × switch.topCells switch.cellsT face)
    (top : left.1.1 ∩ left.2.1 ∈ switch.topCells switch.cellsR face)
    (same : left.1.1 ∩ left.2.1 = right.1.1 ∩ right.2.1) : left = right := by
  have nonempty := top.1.1
  have dim := top.2
  have left_subset : left.1.1 ∩ left.2.1 ⊆ left.1.1 ∩ right.1.1 :=
    fun point member => ⟨member.1, (same ▸ member).1⟩
  have right_subset : left.1.1 ∩ left.2.1 ⊆ left.2.1 ∩ right.2.1 :=
    fun point member => ⟨member.2, (same ▸ member).2⟩
  have left_lower := Submodule.finrank_mono (vectorSpan_mono ℝ left_subset)
  have right_lower := Submodule.finrank_mono (vectorSpan_mono ℝ right_subset)
  have left_upper : adim (left.1.1 ∩ right.1.1) ≤ adim left.1.1 :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have right_upper : adim (left.2.1 ∩ right.2.1) ≤ adim left.2.1 :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have left_dim := left.1.2.2
  have right_dim := left.2.2.2
  have same_left := switch.topCellsS_eq_of_full_inter hface left.1.2 right.1.2
    (nonempty.mono left_subset) (by change adim _ ≤ adim _ at left_lower; omega)
  have same_right := switch.topCellsT_eq_of_full_inter hface left.2.2 right.2.2
    (nonempty.mono right_subset) (by change adim _ ≤ adim _ at right_lower; omega)
  exact Prod.ext (Subtype.ext same_left) (Subtype.ext same_right)

theorem graphEdge_exists_pair (face : Set (switch.P' → ℝ)) (edge : (switch.graphG face).edgeSet) :
    ∃ pair : switch.topCells switch.cellsS face × switch.topCells switch.cellsT face,
      edge.1 = s(Sum.inl pair.1, Sum.inr pair.2) ∧
        pair.1.1 ∩ pair.2.1 ∈ switch.topCells switch.cellsR face := by
  rcases edge with ⟨edge, edge_mem⟩
  induction edge using Sym2.inductionOn with | hf first second
  cases first with
  | inl left =>
    cases second with
    | inl other => exact False.elim edge_mem
    | inr right => exact ⟨(left, right), rfl, edge_mem⟩
  | inr right =>
    cases second with
    | inl left => exact ⟨(left, right), Sym2.eq_swap, edge_mem⟩
    | inr other => exact False.elim edge_mem

noncomputable def graphEdgePair (face : Set (switch.P' → ℝ)) (edge : (switch.graphG face).edgeSet) :
    switch.topCells switch.cellsS face × switch.topCells switch.cellsT face :=
  Classical.choose (switch.graphEdge_exists_pair face edge)

theorem graphEdgePair_spec (face : Set (switch.P' → ℝ)) (edge : (switch.graphG face).edgeSet) :
    edge.1 = s(Sum.inl (switch.graphEdgePair face edge).1, Sum.inr (switch.graphEdgePair face edge).2) ∧
      (switch.graphEdgePair face edge).1.1 ∩ (switch.graphEdgePair face edge).2.1 ∈
        switch.topCells switch.cellsR face :=
  Classical.choose_spec (switch.graphEdge_exists_pair face edge)

noncomputable def graphEdgeCell (face : Set (switch.P' → ℝ))
    (edge : (switch.graphG face).edgeSet) : switch.topCells switch.cellsR face :=
  ⟨(switch.graphEdgePair face edge).1.1 ∩ (switch.graphEdgePair face edge).2.1,
    (switch.graphEdgePair_spec face edge).2⟩

theorem graphEdgeCell_bijective {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    Function.Bijective (switch.graphEdgeCell face) := by
  constructor
  · intro first second same
    have same_pair := switch.top_pairs_eq_of_inter_eq hface
      (switch.graphEdgePair face first) (switch.graphEdgePair face second)
      (switch.graphEdgePair_spec face first).2 (congrArg Subtype.val same)
    apply Subtype.ext
    rw [(switch.graphEdgePair_spec face first).1, (switch.graphEdgePair_spec face second).1, same_pair]
  · intro cell
    obtain ⟨left, hleft, right, hright, same⟩ := switch.topR_exists_pair hface cell.2
    let leftVertex : switch.topCells switch.cellsS face := ⟨left, hleft⟩
    let rightVertex : switch.topCells switch.cellsT face := ⟨right, hright⟩
    let edge : (switch.graphG face).edgeSet :=
      ⟨s(Sum.inl leftVertex, Sum.inr rightVertex), by
        change left ∩ right ∈ switch.topCells switch.cellsR face
        rw [← same]
        exact cell.2⟩
    refine ⟨edge, ?_⟩
    have pair_eq := (switch.graphEdgePair_spec face edge).1
    change s(Sum.inl leftVertex, Sum.inr rightVertex) =
      s(Sum.inl (switch.graphEdgePair face edge).1, Sum.inr (switch.graphEdgePair face edge).2) at pair_eq
    have components : leftVertex = (switch.graphEdgePair face edge).1 ∧
        rightVertex = (switch.graphEdgePair face edge).2 := by simpa [Sym2.eq_iff] using pair_eq
    apply Subtype.ext
    change (switch.graphEdgePair face edge).1.1 ∩ (switch.graphEdgePair face edge).2.1 = cell.1
    rw [← components.1, ← components.2]
    exact same.symm

noncomputable def graphEdgeEquivTopR {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    (switch.graphG face).edgeSet ≃ switch.topCells switch.cellsR face :=
  Equiv.ofBijective (switch.graphEdgeCell face) (switch.graphEdgeCell_bijective hface)

theorem top_carrier_count_bound {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face)
    (connected : (switch.graphG face).Connected) :
    switch.carrierNum switch.cellsS face (adim face) + switch.carrierNum switch.cellsT face (adim face) ≤
      switch.carrierNum switch.cellsR face (adim face) + 1 := by
  classical
  let := (switch.topCells_finite switch.cellsS_finite face).fintype
  let := (switch.topCells_finite switch.cellsT_finite face).fintype
  have count := connected.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_sum, Nat.card_congr (switch.graphEdgeEquivTopR hface)] at count
  simpa only [Nat.card_coe_set_eq, switch.topCellsS_eq_carried hface,
    switch.topCellsT_eq_carried hface, switch.topCellsR_eq_carried hface, carrierNum] using count

end HibiLi.Switch
