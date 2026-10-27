/-
HibiLi/Example21/ChainZeroOne.lean — antichain indicators generate the chain polytope.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.ChainIntervals

namespace HibiLi

variable {P : Type*} [Fintype P] [PartialOrder P]

theorem zeroOne_antichain_mem_chainPolytope {v : P → ℝ} (hv : v ∈ zeroOneVectors P)
    (hanti : IsAntichain (· ≤ ·) {pp | v pp = 1}) : v ∈ chainPolytope P := by
  classical
  constructor
  · intro pp
    rcases hv pp with hz | ho
    · rw [hz]
    · rw [ho]; norm_num
  · intro K hK
    have hcard : (K.filter fun pp => v pp = 1).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro pp hp qq hq
      rcases Finset.mem_filter.mp hp with ⟨hpK, hpv⟩
      rcases Finset.mem_filter.mp hq with ⟨hqK, hqv⟩
      rcases hK.total hpK hqK with hpq | hqp
      · exact hanti.eq hpv hqv hpq
      · exact (hanti.eq hqv hpv hqp).symm
    calc
      ∑ pp ∈ K, v pp = ∑ pp ∈ K, if v pp = 1 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro pp _
        rcases hv pp with hz | ho
        · simp [hz]
        · simp [ho]
      _ = ((K.filter fun pp => v pp = 1).card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard

theorem chainInterval_antichain (x : P → ℝ) (time : ℝ) :
    IsAntichain (· ≤ ·) {pp | intervalVector (chainStart x) (chainFinish x) time pp = 1} := by
  classical
  intro pp hp qq hq hpq hle
  have hlt : pp < qq := lt_of_le_of_ne hle hpq
  have hp' : time ∈ Set.Ioc (chainStart x pp) (chainFinish x pp) := by
    simpa [intervalVector] using hp
  have hq' : time ∈ Set.Ioc (chainStart x qq) (chainFinish x qq) := by
    simpa [intervalVector] using hq
  have hsep := chainFinish_le_chainStart (x := x) hlt
  exact (not_lt_of_ge (hp'.2.trans hsep)) hq'.1

theorem chainPolytope_eq_convexHull_zeroOne (P : Type*) [Fintype P] [PartialOrder P] :
    chainPolytope P = convexHull ℝ (chainPolytope P ∩ zeroOneVectors P) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    have hh := intervalVector_convexHull (chainStart x) (chainFinish x)
      (chainStart_nonneg x) (fun pp => le_add_of_nonneg_right (hx.1 pp))
      (chainFinish_le_one hx) ((zeroOneVectors_finite P).inter_of_right (chainPolytope P))
      (fun time _ => ⟨zeroOne_antichain_mem_chainPolytope (intervalVector_mem_zeroOne _ _ _)
        (chainInterval_antichain x time), intervalVector_mem_zeroOne _ _ _⟩)
    simpa only [chainFinish, add_sub_cancel_left] using hh
  · exact convexHull_min Set.inter_subset_left (chainPolytope_convex P)

end HibiLi
