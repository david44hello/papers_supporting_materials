/-
HibiLi/Example21/FiniteHull.lean — finite generating sets and exposed faces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Defs.Polytope

namespace HibiLi

section AffineDimension

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem adim_convexHull (S : Set E) : adim (convexHull ℝ S) = adim S := by
  unfold adim
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]

end AffineDimension

section FiniteHull

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
  {V F : Set E}

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
theorem IsFace.extremePoints_finite (hV : V.Finite)
    (hF : IsFace (convexHull ℝ V) F) : (Set.extremePoints ℝ F).Finite :=
  hV.subset (hF.2.isExtreme.extremePoints_subset_extremePoints.trans
    extremePoints_convexHull_subset)

theorem IsFace.eq_convexHull_extremePoints (hV : V.Finite)
    (hF : IsFace (convexHull ℝ V) F) : F = convexHull ℝ (Set.extremePoints ℝ F) := by
  have hcompact := hF.2.isCompact (hV.isCompact_convexHull ℝ)
  have hconvex := hF.2.convex (convex_convexHull ℝ V)
  have hclosed := (hF.extremePoints_finite hV).isClosed_convexHull ℝ
  simpa only [hclosed.closure_eq] using
    (closure_convexHull_extremePoints hcompact hconvex).symm

theorem IsFace.eq_convexHull_inter (hV : V.Finite)
    (hF : IsFace (convexHull ℝ V) F) : F = convexHull ℝ (V ∩ F) := by
  apply Set.Subset.antisymm
  · conv_lhs => rw [hF.eq_convexHull_extremePoints hV]
    apply convexHull_mono
    intro x hx
    exact ⟨extremePoints_convexHull_subset
      (hF.2.isExtreme.extremePoints_subset_extremePoints hx), extremePoints_subset hx⟩
  · exact convexHull_min Set.inter_subset_right (hF.2.convex (convex_convexHull ℝ V))

end FiniteHull

end HibiLi
