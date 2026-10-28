/-
HibiLi/Example21/ZeroOne.lean — zero-one generators of finite-poset polytopes.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Example21.IntervalDecomposition
import LeeDiam.Vendor.HibiLi.Example21.XVertices

namespace HibiLi

def zeroOneVectors (P : Type*) : Set (P → ℝ) := {v | ∀ pp, v pp = 0 ∨ v pp = 1}

theorem zeroOneVectors_finite (P : Type*) [Fintype P] : (zeroOneVectors P).Finite := by
  classical
  apply (Set.finite_range (fun bits : P → Bool => fun pp => if bits pp then (1 : ℝ) else 0)).subset
  intro v hv
  refine ⟨fun pp => decide (v pp = 1), ?_⟩
  ext pp
  rcases hv pp with hz | ho
  · simp [hz]
  · simp [ho]

theorem intervalVector_mem_zeroOne {P : Type*} (start finish : P → ℝ) (time : ℝ) :
    intervalVector start finish time ∈ zeroOneVectors P :=
  intervalVector_zero_one start finish time

theorem orderPolytope_eq_convexHull_zeroOne (P : Type*) [Fintype P] [PartialOrder P] :
    orderPolytope P = convexHull ℝ (orderPolytope P ∩ zeroOneVectors P) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hh := intervalVector_convexHull (fun _ : P => 0) x (fun _ => le_refl 0)
      (fun pp => (hx.1 pp).1) (fun pp => (hx.1 pp).2)
      ((zeroOneVectors_finite P).inter_of_right (orderPolytope P))
    simp only [sub_zero] at hh
    apply hh
    intro time htime
    refine ⟨?_, intervalVector_mem_zeroOne _ _ _⟩
    constructor
    · intro pp
      rcases intervalVector_zero_one (fun _ : P => 0) x time pp with hz | ho
      · rw [hz]; norm_num
      · rw [ho]; norm_num
    · intro pp qq hpq
      have hmono := hx.2 pp qq hpq
      by_cases hp : time ≤ x pp
      · have hq := hp.trans hmono
        simp [intervalVector, Set.mem_Ioc, htime.1, hp, hq]
      · simp [intervalVector, Set.mem_Ioc, hp]
        by_cases hq : time ∈ Set.Ioc 0 (x qq) <;> simp [hq]
  · exact convexHull_min Set.inter_subset_left (orderPolytope_convex P)

end HibiLi
