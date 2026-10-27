/-
HibiLiLean — convex cells and intrinsic interiors under equal-dimension inclusions.
-/
import HibiLi.Polytope.AffinityCells

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsPolytope.convex {body : Set E} (polytope : IsPolytope body) : Convex ℝ body := by
  obtain ⟨vertices, rfl⟩ := polytope
  exact convex_convexHull ℝ _

theorem intrinsicInterior_mono_of_adim_eq {small large : Set E} (nonempty : small.Nonempty)
    (subset : small ⊆ large) (dimension : adim small = adim large) :
    intrinsicInterior ℝ small ⊆ intrinsicInterior ℝ large := by
  have same := affineSpan_eq_of_subset_of_adim_eq nonempty subset dimension
  unfold intrinsicInterior
  rw [same]
  exact Set.image_mono (interior_mono (Set.preimage_mono subset))

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem cellsS_isPolytope {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsS) : IsPolytope cell := by
  obtain ⟨branch, valid, _, hface⟩ := member
  exact (switch.domL_isPolytope branch valid).face hface

theorem cellsT_isPolytope {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsT) : IsPolytope cell := by
  obtain ⟨branch, valid, _, hface⟩ := member
  exact (switch.domU_isPolytope branch valid).face hface

theorem cellsR_convex {cell : Set (switch.P' → ℝ)} (member : cell ∈ switch.cellsR) : Convex ℝ cell := by
  obtain ⟨_, left, hleft, right, hright, rfl⟩ := member
  exact (switch.cellsS_isPolytope hleft).convex.inter (switch.cellsT_isPolytope hright).convex

theorem cellsS_eq_of_full_inter {left right : Set (switch.P' → ℝ)}
    (hleft : left ∈ switch.cellsS) (hright : right ∈ switch.cellsS)
    (nonempty : (left ∩ right).Nonempty)
    (leftDim : adim (left ∩ right) = adim left) (rightDim : adim (left ∩ right) = adim right) : left = right := by
  obtain ⟨leftBranch, _, _, leftFace⟩ := hleft
  obtain ⟨rightBranch, _, _, rightFace⟩ := hright
  apply affinity_cells_eq_of_full_inter switch.B switch.L
    (switch.chainSumAffine leftBranch) (switch.chainSumAffine rightBranch)
  · simpa only [chainSumAffine_apply, domL] using leftFace
  · simpa only [chainSumAffine_apply, domL] using rightFace
  · exact nonempty
  · exact leftDim
  · exact rightDim

theorem cellsT_eq_of_full_inter {left right : Set (switch.P' → ℝ)}
    (hleft : left ∈ switch.cellsT) (hright : right ∈ switch.cellsT)
    (nonempty : (left ∩ right).Nonempty)
    (leftDim : adim (left ∩ right) = adim left) (rightDim : adim (left ∩ right) = adim right) : left = right := by
  obtain ⟨leftBranch, _, _, leftFace⟩ := hleft
  obtain ⟨rightBranch, _, _, rightFace⟩ := hright
  apply affinity_cells_eq_of_full_inter switch.B switch.U
    (switch.upValAffine leftBranch) (switch.upValAffine rightBranch)
  · simpa only [upValAffine_apply, domU] using leftFace
  · simpa only [upValAffine_apply, domU] using rightFace
  · exact nonempty
  · exact leftDim
  · exact rightDim

end Switch
end HibiLi
