/-
HibiLi/Example21/BottomPyramid.lean — adjoining a bottom element gives two pyramids.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.BottomGeometry

namespace HibiLi

open Polynomial
variable (P : Type*) [Fintype P] [PartialOrder P]

theorem orderPolytope_withBot_pyramid :
    orderPolytope (WithBot P) = convexHull ℝ (insert orderBottomApex (bottomLift '' orderPolytope P)) := by
  calc
    orderPolytope (WithBot P) = convexHull ℝ (orderPolytope (WithBot P) ∩ zeroOneVectors (WithBot P)) :=
      orderPolytope_eq_convexHull_zeroOne _
    _ = convexHull ℝ (insert orderBottomApex (bottomLift '' (orderPolytope P ∩ zeroOneVectors P))) :=
      congrArg (convexHull ℝ) orderZeroOne_withBot
    _ = convexHull ℝ (insert orderBottomApex
        (convexHull ℝ (bottomLift '' (orderPolytope P ∩ zeroOneVectors P)))) :=
      (convexHull_insert_convexHull _ _).symm
    _ = convexHull ℝ (insert orderBottomApex
        (bottomLift '' convexHull ℝ (orderPolytope P ∩ zeroOneVectors P))) := by
      exact congrArg (fun S : Set (WithBot P → ℝ) => convexHull ℝ (insert orderBottomApex S))
        (bottomLift.toLinearMap.toAffineMap.image_convexHull _).symm
    _ = _ := by rw [← orderPolytope_eq_convexHull_zeroOne P]

theorem chainPolytope_withBot_pyramid :
    chainPolytope (WithBot P) = convexHull ℝ (insert chainBottomApex (bottomLift '' chainPolytope P)) := by
  calc
    chainPolytope (WithBot P) = convexHull ℝ (chainPolytope (WithBot P) ∩ zeroOneVectors (WithBot P)) :=
      chainPolytope_eq_convexHull_zeroOne _
    _ = convexHull ℝ (insert chainBottomApex (bottomLift '' (chainPolytope P ∩ zeroOneVectors P))) :=
      congrArg (convexHull ℝ) chainZeroOne_withBot
    _ = convexHull ℝ (insert chainBottomApex
        (convexHull ℝ (bottomLift '' (chainPolytope P ∩ zeroOneVectors P)))) :=
      (convexHull_insert_convexHull _ _).symm
    _ = convexHull ℝ (insert chainBottomApex
        (bottomLift '' convexHull ℝ (chainPolytope P ∩ zeroOneVectors P))) := by
      exact congrArg (fun S : Set (WithBot P → ℝ) => convexHull ℝ (insert chainBottomApex S))
        (bottomLift.toLinearMap.toAffineMap.image_convexHull _).symm
    _ = _ := by rw [← chainPolytope_eq_convexHull_zeroOne P]

theorem facePoly_order_withBot :
    facePoly (orderPolytope (WithBot P)) = 1 + (1 + X) * facePoly (orderPolytope P) := by
  rw [orderPolytope_withBot_pyramid]
  rw [eq_1_pyramid_proved _ ((orderPolytope_isPolytope P).image_linear bottomLift)
    orderBottomApex (bottomLift_apex_outside _ _ (by simp)), facePoly_bottomLift]

theorem facePoly_chain_withBot :
    facePoly (chainPolytope (WithBot P)) = 1 + (1 + X) * facePoly (chainPolytope P) := by
  rw [chainPolytope_withBot_pyramid]
  rw [eq_1_pyramid_proved _ ((chainPolytope_isPolytope P).image_linear bottomLift)
    chainBottomApex (bottomLift_apex_outside _ _ (by simp)), facePoly_bottomLift]

theorem facePoly_gap_withBot :
    facePoly (chainPolytope (WithBot P)) - facePoly (orderPolytope (WithBot P)) =
      (1 + X) * (facePoly (chainPolytope P) - facePoly (orderPolytope P)) := by
  rw [facePoly_order_withBot, facePoly_chain_withBot]
  ring

end HibiLi
