/-
HibiLiLean — full-dimensional intersections determine affinity cells uniquely.
-/
import HibiLi.Polytope.TopCells

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem affineSpan_eq_of_subset_of_adim_eq {small large : Set E} (nonempty : small.Nonempty)
    (subset : small ⊆ large) (dimension : adim small = adim large) :
    affineSpan ℝ small = affineSpan ℝ large :=
  AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
    (by simpa only [direction_affineSpan] using
      Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ subset) dimension)
    (nonempty.mono (subset_affineSpan ℝ small)) (affineSpan_mono ℝ subset)

theorem affinity_cells_eq_of_full_inter (base : Set E) (envelope : E → ℝ)
    (leftBranch rightBranch : E →ᵃ[ℝ] ℝ) {left right : Set E}
    (hleft : IsFace {point ∈ base | envelope point = leftBranch point} left)
    (hright : IsFace {point ∈ base | envelope point = rightBranch point} right)
    (nonempty : (left ∩ right).Nonempty)
    (leftDim : adim (left ∩ right) = adim left)
    (rightDim : adim (left ∩ right) = adim right) : left = right := by
  have span_left := affineSpan_eq_of_subset_of_adim_eq nonempty Set.inter_subset_left leftDim
  have span_right := affineSpan_eq_of_subset_of_adim_eq nonempty Set.inter_subset_right rightDim
  have agree : (left ∩ right).EqOn leftBranch rightBranch := by
    intro point member
    exact (hleft.subset member.1).2.symm.trans (hright.subset member.2).2
  have agree_span := AffineMap.eqOn_affineSpan agree
  apply Set.Subset.antisymm
  · intro point member
    have span_member : point ∈ affineSpan ℝ (left ∩ right) := by
      rw [span_left]
      exact subset_affineSpan ℝ left member
    apply (Set.ext_iff.mp hright.eq_inter_affineSpan point).mpr
    refine ⟨⟨(hleft.subset member).1, (hleft.subset member).2.trans (agree_span span_member)⟩, ?_⟩
    rwa [← span_right]
  · intro point member
    have span_member : point ∈ affineSpan ℝ (left ∩ right) := by
      rw [span_right]
      exact subset_affineSpan ℝ right member
    apply (Set.ext_iff.mp hleft.eq_inter_affineSpan point).mpr
    refine ⟨⟨(hright.subset member).1, (hright.subset member).2.trans (agree_span span_member).symm⟩, ?_⟩
    rwa [← span_left]

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

noncomputable def chainSumAffine (branch : Finset switch.P') : (switch.P' → ℝ) →ᵃ[ℝ] ℝ :=
  (∑ coord ∈ branch, (ContinuousLinearMap.proj coord : StrongDual ℝ (switch.P' → ℝ))).toLinearMap.toAffineMap

@[simp] theorem chainSumAffine_apply (branch : Finset switch.P') (point : switch.P' → ℝ) :
    switch.chainSumAffine branch point = switch.chainSum branch point := by
  simp [chainSumAffine, chainSum]

noncomputable def upValAffine : Option switch.P' → (switch.P' → ℝ) →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ _ 1
  | some coord => (ContinuousLinearMap.proj coord : StrongDual ℝ (switch.P' → ℝ)).toLinearMap.toAffineMap

@[simp] theorem upValAffine_apply (branch : Option switch.P') (point : switch.P' → ℝ) :
    switch.upValAffine branch point = switch.upVal branch point := by
  cases branch <;> rfl

theorem topCellsS_eq_of_full_inter {face left right : Set (switch.P' → ℝ)}
    (hface : IsFace switch.B face) (hleft : left ∈ switch.topCells switch.cellsS face)
    (hright : right ∈ switch.topCells switch.cellsS face) (nonempty : (left ∩ right).Nonempty)
    (dimension : adim (left ∩ right) = adim face) : left = right := by
  have left_member := switch.restrict_cellsS_subset hface hleft.1
  have right_member := switch.restrict_cellsS_subset hface hright.1
  obtain ⟨leftBranch, _, _, left_face⟩ := left_member
  obtain ⟨rightBranch, _, _, right_face⟩ := right_member
  apply affinity_cells_eq_of_full_inter switch.B switch.L
    (switch.chainSumAffine leftBranch) (switch.chainSumAffine rightBranch)
  · simpa only [chainSumAffine_apply, domL] using left_face
  · simpa only [chainSumAffine_apply, domL] using right_face
  · exact nonempty
  · exact dimension.trans hleft.2.symm
  · exact dimension.trans hright.2.symm

theorem topCellsT_eq_of_full_inter {face left right : Set (switch.P' → ℝ)}
    (hface : IsFace switch.B face) (hleft : left ∈ switch.topCells switch.cellsT face)
    (hright : right ∈ switch.topCells switch.cellsT face) (nonempty : (left ∩ right).Nonempty)
    (dimension : adim (left ∩ right) = adim face) : left = right := by
  have left_member := switch.restrict_cellsT_subset hface hleft.1
  have right_member := switch.restrict_cellsT_subset hface hright.1
  obtain ⟨leftBranch, _, _, left_face⟩ := left_member
  obtain ⟨rightBranch, _, _, right_face⟩ := right_member
  apply affinity_cells_eq_of_full_inter switch.B switch.U
    (switch.upValAffine leftBranch) (switch.upValAffine rightBranch)
  · simpa only [upValAffine_apply, domU] using left_face
  · simpa only [upValAffine_apply, domU] using right_face
  · exact nonempty
  · exact dimension.trans hleft.2.symm
  · exact dimension.trans hright.2.symm

end Switch
end HibiLi
