/-
HibiLiLean — the restricted common refinement is a finite polytopal subdivision.
-/
import HibiLi.Polytope.AffinityComplex
import HibiLi.Defs.Subdivision

namespace HibiLi

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private theorem intersections_face {left right otherLeft otherRight : Set V}
    (leftFace : IsFace left (left ∩ otherLeft)) (rightFace : IsFace right (right ∩ otherRight))
    (nonempty : ((left ∩ right) ∩ (otherLeft ∩ otherRight)).Nonempty) :
    IsFace (left ∩ right) ((left ∩ right) ∩ (otherLeft ∩ otherRight)) := by
  have left_nonempty : ((left ∩ right) ∩ (left ∩ otherLeft)).Nonempty :=
    nonempty.mono fun _ member => ⟨member.1, member.1.1, member.2.1⟩
  have right_nonempty : ((left ∩ right) ∩ (right ∩ otherRight)).Nonempty :=
    nonempty.mono fun _ member => ⟨member.1, member.1.2, member.2.2⟩
  have first := leftFace.inter_subset Set.inter_subset_left left_nonempty
  have second := rightFace.inter_subset Set.inter_subset_right right_nonempty
  have both_nonempty : (((left ∩ right) ∩ (left ∩ otherLeft)) ∩
      ((left ∩ right) ∩ (right ∩ otherRight))).Nonempty :=
    nonempty.mono fun _ member => ⟨⟨member.1, member.1.1, member.2.1⟩, member.1, member.1.2, member.2.2⟩
  have result := first.inter second both_nonempty
  have same : ((left ∩ right) ∩ (left ∩ otherLeft)) ∩ ((left ∩ right) ∩ (right ∩ otherRight)) =
      (left ∩ right) ∩ (otherLeft ∩ otherRight) := by
    ext point
    simp only [Set.mem_inter_iff]
    tauto
  simpa only [same] using result

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem cellsR_face_closed {cell face : Set (switch.P' → ℝ)}
    (member : cell ∈ switch.cellsR) (hface : IsFace cell face) : face ∈ switch.cellsR := by
  obtain ⟨_, left, hleft, right, hright, rfl⟩ := member
  obtain ⟨leftFace, rightFace, left_face, right_face, same⟩ := hface.inter_decomposition
    (switch.cellsS_isPolytope hleft) (switch.cellsT_isPolytope hright)
    (switch.cellsS_halfspaces hleft) (switch.cellsT_halfspaces hright)
  exact ⟨hface.1, leftFace, switch.cellsS_face_closed hleft left_face,
    rightFace, switch.cellsT_face_closed hright right_face, same⟩

theorem cellsR_inter_faces {left right : Set (switch.P' → ℝ)}
    (hleft : left ∈ switch.cellsR) (hright : right ∈ switch.cellsR) (nonempty : (left ∩ right).Nonempty) :
    IsFace left (left ∩ right) ∧ IsFace right (left ∩ right) := by
  obtain ⟨_, leftS, hleftS, leftT, hleftT, rfl⟩ := hleft
  obtain ⟨_, rightS, hrightS, rightT, hrightT, rfl⟩ := hright
  have nonemptyS : (leftS ∩ rightS).Nonempty := nonempty.mono fun _ member => ⟨member.1.1, member.2.1⟩
  have nonemptyT : (leftT ∩ rightT).Nonempty := nonempty.mono fun _ member => ⟨member.1.2, member.2.2⟩
  have facesS := switch.cellsS_inter_faces hleftS hrightS nonemptyS
  have facesT := switch.cellsT_inter_faces hleftT hrightT nonemptyT
  constructor
  · exact intersections_face facesS.1 facesT.1 nonempty
  · have reverseS : IsFace rightS (rightS ∩ leftS) := by simpa only [Set.inter_comm] using facesS.2
    have reverseT : IsFace rightT (rightT ∩ leftT) := by simpa only [Set.inter_comm] using facesT.2
    have result := intersections_face reverseS reverseT (by simpa only [Set.inter_comm] using nonempty)
    simpa only [Set.inter_comm] using result

theorem cellsR_cover : switch.B ⊆ ⋃ cell : switch.cellsR, (cell : Set (switch.P' → ℝ)) := by
  intro point member
  obtain ⟨left, left_member⟩ := Set.mem_iUnion.mp (switch.cellsS_cover member)
  obtain ⟨right, right_member⟩ := Set.mem_iUnion.mp (switch.cellsT_cover member)
  have common_member : left.1 ∩ right.1 ∈ switch.cellsR :=
    ⟨⟨point, left_member, right_member⟩, left.1, left.2, right.1, right.2, rfl⟩
  exact Set.mem_iUnion.mpr ⟨⟨left.1 ∩ right.1, common_member⟩, left_member, right_member⟩

theorem restrict_cell_subset {family : Set (Set (switch.P' → ℝ))} {face cell : Set (switch.P' → ℝ)}
    (member : cell ∈ switch.restrict family face) : cell ⊆ face := by
  obtain ⟨_, original, _, rfl⟩ := member
  exact Set.inter_subset_right

theorem restrict_cellsR_cover {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    face ⊆ ⋃ cell : switch.restrict switch.cellsR face, (cell : Set (switch.P' → ℝ)) := by
  intro point member
  obtain ⟨original, in_original⟩ := Set.mem_iUnion.mp (switch.cellsR_cover (hface.subset member))
  have restricted : original.1 ∩ face ∈ switch.restrict switch.cellsR face :=
    ⟨⟨point, in_original, member⟩, original.1, original.2, rfl⟩
  exact Set.mem_iUnion.mpr ⟨⟨original.1 ∩ face, restricted⟩, in_original, member⟩

theorem restrict_cellsR_subdivision {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    IsFinitePolytopalSubdivision face (switch.restrict_finite switch.cellsR_finite face).toFinset := by
  classical
  let finite := switch.restrict_finite switch.cellsR_finite face
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cell member
    have restricted := finite.mem_toFinset.mp member
    exact ⟨switch.cellsR_isPolytope (switch.restrict_cellsR_subset hface restricted), restricted.1⟩
  · ext point
    constructor
    · rintro ⟨cell, member, in_cell⟩
      exact switch.restrict_cell_subset (finite.mem_toFinset.mp member) in_cell
    · intro member
      obtain ⟨cell, in_cell⟩ := Set.mem_iUnion.mp (switch.restrict_cellsR_cover hface member)
      exact ⟨cell.1, finite.mem_toFinset.mpr cell.2, in_cell⟩
  · intro cell member subface hsubface
    have restricted := finite.mem_toFinset.mp member
    have cellR := switch.restrict_cellsR_subset hface restricted
    have subfaceR := switch.cellsR_face_closed cellR hsubface
    have inside := hsubface.subset.trans (switch.restrict_cell_subset restricted)
    apply finite.mem_toFinset.mpr
    exact ⟨hsubface.1, subface, subfaceR, (Set.inter_eq_left.mpr inside).symm⟩
  · intro left hleft right hright nonempty
    exact switch.cellsR_inter_faces
      (switch.restrict_cellsR_subset hface (finite.mem_toFinset.mp hleft))
      (switch.restrict_cellsR_subset hface (finite.mem_toFinset.mp hright)) nonempty

end Switch
end HibiLi
