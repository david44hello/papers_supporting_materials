/-
HibiLiLean — adjoining an apex raises affine dimension by one.
-/
import HibiLi.Polytope.FiniteFaces

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem adim_convexHull_insert {body : Set E} (nonempty : body.Nonempty) (apex : E)
    (outside : apex ∉ affineSpan ℝ body) :
    adim (convexHull ℝ (insert apex body)) = adim body + 1 := by
  rw [adim_convexHull]
  have upper := finrank_vectorSpan_insert_le_set ℝ body apex
  have included : affineSpan ℝ body ≤ affineSpan ℝ (insert apex body) :=
    affineSpan_mono ℝ (Set.subset_insert apex body)
  have directions : vectorSpan ℝ body < vectorSpan ℝ (insert apex body) := by
    refine lt_of_le_of_ne (vectorSpan_mono ℝ (Set.subset_insert apex body)) ?_
    intro same
    have spans := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (by simpa only [direction_affineSpan] using same)
      (nonempty.mono (subset_affineSpan ℝ body)) included
    apply outside
    rw [spans]
    exact subset_affineSpan ℝ _ (Set.mem_insert apex body)
  have lower := Submodule.finrank_lt_finrank_of_lt directions
  unfold adim
  omega

omit [FiniteDimensional ℝ E] in
theorem convexHull_insert_convexHull (apex : E) (body : Set E) :
    convexHull ℝ (insert apex (convexHull ℝ body)) = convexHull ℝ (insert apex body) := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro point member
    rcases member with rfl | member
    · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
    · exact convexHull_mono (Set.subset_insert apex body) member
  · exact convexHull_mono (Set.insert_subset_insert (subset_convexHull ℝ body))

theorem IsPolytope.convexHull_insert {body : Set E} (polytope : IsPolytope body) (apex : E) :
    IsPolytope (convexHull ℝ (insert apex body)) := by
  classical
  rcases polytope with ⟨vertices, rfl⟩
  refine ⟨insert apex vertices, ?_⟩
  simp only [Finset.coe_insert, convexHull_insert_convexHull]

end HibiLi
