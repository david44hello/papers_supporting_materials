/-
HibiLi/Example21/ZeroOneResult.lean — full-dimensional zero-one polytopes for every finite poset.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Example21.ChainZeroOne
import LeeDiam.Vendor.HibiLi.Polytope.Dimension

namespace HibiLi

theorem sec1_zero_one_polytopes_proved (P : Type*) [Fintype P] [PartialOrder P] :
    (∃ S : Finset (P → ℝ), (∀ v ∈ S, ∀ p, v p = 0 ∨ v p = 1) ∧
      orderPolytope P = convexHull ℝ (S : Set (P → ℝ))) ∧
    (∃ S : Finset (P → ℝ), (∀ v ∈ S, ∀ p, v p = 0 ∨ v p = 1) ∧
      chainPolytope P = convexHull ℝ (S : Set (P → ℝ))) ∧
    adim (orderPolytope P) = Fintype.card P ∧ adim (chainPolytope P) = Fintype.card P := by
  classical
  have horder := (zeroOneVectors_finite P).inter_of_right (orderPolytope P)
  have hchain := (zeroOneVectors_finite P).inter_of_right (chainPolytope P)
  refine ⟨⟨horder.toFinset, ?_, ?_⟩, ⟨hchain.toFinset, ?_, ?_⟩, ?_, ?_⟩
  · intro v hv
    exact (horder.mem_toFinset.mp hv).2
  · simpa only [Set.Finite.coe_toFinset] using orderPolytope_eq_convexHull_zeroOne P
  · intro v hv
    exact (hchain.mem_toFinset.mp hv).2
  · simpa only [Set.Finite.coe_toFinset] using chainPolytope_eq_convexHull_zeroOne P
  · simpa only [chainOrderPolytope_empty] using chainOrderPolytope_adim P ∅
  · simpa only [chainOrderPolytope_univ] using chainOrderPolytope_adim P Set.univ

end HibiLi
