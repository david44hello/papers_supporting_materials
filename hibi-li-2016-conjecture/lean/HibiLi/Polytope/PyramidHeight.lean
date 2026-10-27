/-
HibiLiLean — a linear height separating a base affine span from an apex.
-/
import HibiLi.Polytope.PyramidDimension

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_pyramid_height {body : Set E} (nonempty : body.Nonempty) (apex : E)
    (outside : apex ∉ affineSpan ℝ body) :
    ∃ height : StrongDual ℝ E, ∃ level : ℝ,
      (∀ point ∈ body, height point = level) ∧ height apex = level + 1 := by
  obtain ⟨base, base_member⟩ := nonempty
  have base_span := subset_affineSpan ℝ body base_member
  have not_direction : apex - base ∉ (affineSpan ℝ body).direction := by
    simpa only [← vsub_eq_sub, AffineSubspace.vsub_right_mem_direction_iff_mem base_span] using outside
  obtain ⟨functional, nonzero, annihilator⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem not_direction inferInstance
  have vanishes (point : E) (member : point ∈ body) : functional (point - base) = 0 := by
    have direction : point - base ∈ (affineSpan ℝ body).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ body member) base_span
    have image_member : functional (point - base) ∈ (affineSpan ℝ body).direction.map functional :=
      ⟨point - base, direction, rfl⟩
    rw [annihilator] at image_member
    simpa using image_member
  let height : StrongDual ℝ E := (functional (apex - base))⁻¹ • functional.toContinuousLinearMap
  refine ⟨height, height base, ?_, ?_⟩
  · intro point member
    have equal : functional point = functional base := by
      have zero := vanishes point member
      simpa only [map_sub, sub_eq_zero] using zero
    simp [height, equal]
  · have difference_ne : functional apex - functional base ≠ 0 := by simpa using nonzero
    have difference : height (apex - base) = 1 := by simp [height, difference_ne]
    rw [map_sub] at difference
    linarith

end HibiLi
