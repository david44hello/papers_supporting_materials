/-
HibiLiLean — faces of affinity domains form face-to-face complexes.
-/
import HibiLi.Polytope.IntersectionFaces
import HibiLi.Polytope.Transitivity

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isFace_affine_level (body : Set E) (functional : E →ᵃ[ℝ] ℝ) (level : ℝ)
    (bounded : ∀ point ∈ body, functional point ≤ level)
    (attained : ∃ point ∈ body, functional point = level) :
    IsFace body {point ∈ body | functional point = level} := by
  obtain ⟨base, base_member, equal⟩ := attained
  let linear := functional.linear.toContinuousLinearMap
  have difference (point other : E) : linear point - linear other = functional point - functional other := by
    simpa [linear] using functional.linear_apply_vsub point other
  refine ⟨⟨base, base_member, equal⟩, fun _ => ⟨linear, ?_⟩⟩
  ext point
  constructor
  · rintro ⟨member, same⟩
    refine ⟨member, fun other other_member => ?_⟩
    have bound := bounded other other_member
    have delta := difference other point
    linarith
  · rintro ⟨member, maximal⟩
    refine ⟨member, le_antisymm (bounded point member) ?_⟩
    have bound := maximal base base_member
    have delta := difference base point
    linarith

theorem face_inter_of_common_face {leftBody rightBody left right : Set E}
    (polytope : IsPolytope leftBody) (common : IsFace leftBody (leftBody ∩ rightBody))
    (hleft : IsFace leftBody left) (hright : IsFace rightBody right)
    (nonempty : (left ∩ right).Nonempty) : IsFace left (left ∩ right) := by
  have common_right_nonempty : ((leftBody ∩ rightBody) ∩ right).Nonempty := by
    obtain ⟨point, left_member, right_member⟩ := nonempty
    exact ⟨point, ⟨hleft.subset left_member, hright.subset right_member⟩, right_member⟩
  have restricted := hright.inter_subset Set.inter_subset_right common_right_nonempty
  have outer := IsFace.trans polytope common restricted
  have triple_nonempty : (left ∩ ((leftBody ∩ rightBody) ∩ right)).Nonempty :=
    nonempty.mono fun _ member => ⟨member.1, ⟨hleft.subset member.1, hright.subset member.2⟩, member.2⟩
  have result := outer.inter_subset hleft.subset triple_nonempty
  have same : left ∩ ((leftBody ∩ rightBody) ∩ right) = left ∩ right := by
    ext point
    constructor
    · exact fun member => ⟨member.1, member.2.2⟩
    · exact fun member => ⟨member.1, ⟨hleft.subset member.1, hright.subset member.2⟩, member.2⟩
  simpa only [same] using result

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem domL_inter_face (left right : Finset switch.P') (right_valid : right ∈ switch.lowBranches)
    (nonempty : (switch.domL left ∩ switch.domL right).Nonempty) :
    IsFace (switch.domL left) (switch.domL left ∩ switch.domL right) := by
  let functional := switch.chainSumAffine right - switch.chainSumAffine left
  have evaluation (point : switch.P' → ℝ) :
      functional point = switch.chainSum right point - switch.chainSum left point := by
    simp [functional]
  have selected : {point ∈ switch.domL left | functional point = 0} = switch.domL left ∩ switch.domL right := by
    ext point
    simp only [Set.mem_ofPred_eq, evaluation]
    constructor
    · rintro ⟨left_member, same⟩
      exact ⟨left_member, left_member.1, left_member.2.trans (sub_eq_zero.mp same).symm⟩
    · rintro ⟨left_member, right_member⟩
      exact ⟨left_member, sub_eq_zero.mpr (right_member.2.symm.trans left_member.2)⟩
  obtain ⟨base, left_base, right_base⟩ := nonempty
  have result := isFace_affine_level (switch.domL left) functional 0
    (by
      intro point member
      rw [evaluation]
      apply sub_nonpos.mpr
      exact (Finset.le_sup' (fun branch => switch.chainSum branch point) right_valid).trans_eq member.2)
    ⟨base, left_base, by
      rw [evaluation]
      exact sub_eq_zero.mpr (right_base.2.symm.trans left_base.2)⟩
  simpa only [selected] using result

theorem domU_inter_face (left right : Option switch.P') (right_valid : right ∈ switch.upBranches)
    (nonempty : (switch.domU left ∩ switch.domU right).Nonempty) :
    IsFace (switch.domU left) (switch.domU left ∩ switch.domU right) := by
  let functional := switch.upValAffine left - switch.upValAffine right
  have evaluation (point : switch.P' → ℝ) :
      functional point = switch.upVal left point - switch.upVal right point := by
    simp [functional]
  have selected : {point ∈ switch.domU left | functional point = 0} = switch.domU left ∩ switch.domU right := by
    ext point
    simp only [Set.mem_ofPred_eq, evaluation]
    constructor
    · rintro ⟨left_member, same⟩
      exact ⟨left_member, left_member.1, left_member.2.trans (sub_eq_zero.mp same)⟩
    · rintro ⟨left_member, right_member⟩
      exact ⟨left_member, sub_eq_zero.mpr (left_member.2.symm.trans right_member.2)⟩
  obtain ⟨base, left_base, right_base⟩ := nonempty
  have result := isFace_affine_level (switch.domU left) functional 0
    (by
      intro point member
      rw [evaluation]
      apply sub_nonpos.mpr
      exact member.2.symm.trans_le (Finset.inf'_le (fun branch => switch.upVal branch point) right_valid))
    ⟨base, left_base, by
      rw [evaluation]
      exact sub_eq_zero.mpr (left_base.2.symm.trans right_base.2)⟩
  simpa only [selected] using result

theorem cellsS_face_closed {cell face : Set (switch.P' → ℝ)}
    (member : cell ∈ switch.cellsS) (hface : IsFace cell face) : face ∈ switch.cellsS := by
  obtain ⟨branch, valid, full, hcell⟩ := member
  exact ⟨branch, valid, full, IsFace.trans (switch.domL_isPolytope branch valid) hcell hface⟩

theorem cellsT_face_closed {cell face : Set (switch.P' → ℝ)}
    (member : cell ∈ switch.cellsT) (hface : IsFace cell face) : face ∈ switch.cellsT := by
  obtain ⟨branch, valid, full, hcell⟩ := member
  exact ⟨branch, valid, full, IsFace.trans (switch.domU_isPolytope branch valid) hcell hface⟩

theorem cellsS_inter_faces {left right : Set (switch.P' → ℝ)}
    (hleft : left ∈ switch.cellsS) (hright : right ∈ switch.cellsS) (nonempty : (left ∩ right).Nonempty) :
    IsFace left (left ∩ right) ∧ IsFace right (left ∩ right) := by
  obtain ⟨leftBranch, left_valid, _, left_face⟩ := hleft
  obtain ⟨rightBranch, right_valid, _, right_face⟩ := hright
  have domains_nonempty : (switch.domL leftBranch ∩ switch.domL rightBranch).Nonempty :=
    nonempty.mono fun _ member => ⟨left_face.subset member.1, right_face.subset member.2⟩
  constructor
  · exact face_inter_of_common_face (switch.domL_isPolytope leftBranch left_valid)
      (switch.domL_inter_face leftBranch rightBranch right_valid domains_nonempty) left_face right_face nonempty
  · have result := face_inter_of_common_face (switch.domL_isPolytope rightBranch right_valid)
      (switch.domL_inter_face rightBranch leftBranch left_valid (by simpa [Set.inter_comm] using domains_nonempty))
      right_face left_face (by simpa [Set.inter_comm] using nonempty)
    simpa only [Set.inter_comm] using result

theorem cellsT_inter_faces {left right : Set (switch.P' → ℝ)}
    (hleft : left ∈ switch.cellsT) (hright : right ∈ switch.cellsT) (nonempty : (left ∩ right).Nonempty) :
    IsFace left (left ∩ right) ∧ IsFace right (left ∩ right) := by
  obtain ⟨leftBranch, left_valid, _, left_face⟩ := hleft
  obtain ⟨rightBranch, right_valid, _, right_face⟩ := hright
  have domains_nonempty : (switch.domU leftBranch ∩ switch.domU rightBranch).Nonempty :=
    nonempty.mono fun _ member => ⟨left_face.subset member.1, right_face.subset member.2⟩
  constructor
  · exact face_inter_of_common_face (switch.domU_isPolytope leftBranch left_valid)
      (switch.domU_inter_face leftBranch rightBranch right_valid domains_nonempty) left_face right_face nonempty
  · have result := face_inter_of_common_face (switch.domU_isPolytope rightBranch right_valid)
      (switch.domU_inter_face rightBranch leftBranch left_valid (by simpa [Set.inter_comm] using domains_nonempty))
      right_face left_face (by simpa [Set.inter_comm] using nonempty)
    simpa only [Set.inter_comm] using result

end Switch
end HibiLi
