/-
HibiLi/Example21/Triangles.lean — the two-chain example via two genuine pyramids.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.XVertices
import HibiLi.Polytope.Pyramid

namespace HibiLi
namespace Example21

open Polynomial

def orderTriangle : Fin 3 → Fin 2 → ℝ := ![![0, 0], ![0, 1], ![1, 1]]
def chainTriangle : Fin 3 → Fin 2 → ℝ := ![![0, 0], ![0, 1], ![1, 0]]

theorem chain2_mem_iff (x : Fin 2 → ℝ) :
    x ∈ chainPolytope Chain2 ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    have hh := hx.2 Finset.univ (fun _ _ _ _ _ => le_total _ _)
    simpa [Fin.sum_univ_two] using And.intro (hx.1 0) (And.intro (hx.1 1) hh)
  · rintro ⟨hzero, hone, hsum⟩
    have hn (idx : Fin 2) : 0 ≤ x idx := by fin_cases idx <;> assumption
    refine ⟨hn, fun K _ => ?_⟩
    calc
      ∑ idx ∈ K, x idx ≤ ∑ idx : Fin 2, x idx :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) (fun idx _ _ => hn idx)
      _ ≤ 1 := by simpa [Fin.sum_univ_two] using hsum

theorem orderTriangle_mem (idx : Fin 3) : orderTriangle idx ∈ orderPolytope Chain2 := by
  constructor
  · intro pp
    fin_cases idx <;> fin_cases pp <;> norm_num [orderTriangle]
  · intro pp qq hpq
    fin_cases idx <;> fin_cases pp <;> fin_cases qq <;> simp_all [orderTriangle]

theorem chainTriangle_mem (idx : Fin 3) : chainTriangle idx ∈ chainPolytope Chain2 := by
  rw [chain2_mem_iff]
  fin_cases idx <;> norm_num [chainTriangle]

theorem orderPolytope_chain2_hull : orderPolytope Chain2 = convexHull ℝ (Set.range orderTriangle) := by
  apply Set.Subset.antisymm
  · intro x hx
    let weights : Fin 3 → ℝ := ![1 - x 1, x 1 - x 0, x 0]
    have hmono := hx.2 0 1 (by decide)
    refine mem_convexHull_of_exists_fintype weights orderTriangle ?_ ?_
      (fun idx => Set.mem_range_self idx) ?_
    · intro idx
      fin_cases idx <;> norm_num [weights] <;> nlinarith [(hx.1 0).1, (hx.1 1).2]
    · simp [weights, Fin.sum_univ_succ]
    · ext pp
      fin_cases pp <;> simp [weights, orderTriangle, Fin.sum_univ_succ]
  · exact convexHull_min (Set.range_subset_iff.mpr orderTriangle_mem) (orderPolytope_convex Chain2)

theorem chainPolytope_chain2_hull : chainPolytope Chain2 = convexHull ℝ (Set.range chainTriangle) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨hzero, hone, hsum⟩ := (chain2_mem_iff x).mp hx
    let weights : Fin 3 → ℝ := ![1 - x 0 - x 1, x 1, x 0]
    refine mem_convexHull_of_exists_fintype weights chainTriangle ?_ ?_
      (fun idx => Set.mem_range_self idx) ?_
    · intro idx
      fin_cases idx <;> norm_num [weights] <;> linarith
    · simp [weights, Fin.sum_univ_succ] <;> ring
    · ext pp
      fin_cases pp <;> simp [weights, chainTriangle, Fin.sum_univ_succ]
  · exact convexHull_min (Set.range_subset_iff.mpr chainTriangle_mem) (chainPolytope_convex Chain2)

theorem facePoly_triangle {ι : Type*} [Fintype ι] (base edge apex : ι → ℝ)
    (hedge : edge ≠ base) (hapex : apex ∉ affineSpan ℝ ({edge, base} : Set (ι → ℝ))) :
    facePoly (convexHull ℝ ({apex, edge, base} : Set (ι → ℝ))) =
      3 + 3 * X + X ^ 2 := by
  have hbase : IsPolytope ({base} : Set (ι → ℝ)) := ⟨{base}, by simp⟩
  have hfirst := eq_1_pyramid_proved {base} hbase edge (by simpa using hedge)
  have hsecond := eq_1_pyramid_proved (convexHull ℝ {edge, base})
    (hbase.convexHull_insert edge) apex (by rw [affineSpan_convexHull]; exact hapex)
  rw [convexHull_insert_convexHull, hfirst, facePoly_singleton] at hsecond
  exact hsecond.trans (by ring)

theorem triangle_apex_outside (last : ℝ) :
    (![1, last] : Fin 2 → ℝ) ∉ affineSpan ℝ
      ({![0, 1], ![0, 0]} : Set (Fin 2 → ℝ)) := by
  intro hin
  obtain ⟨param, hparam⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hin
  have hh := congrFun hparam 0
  norm_num [AffineMap.lineMap_apply] at hh

end Example21

open Polynomial Example21

theorem sec2_chain2_triangles_proved :
    facePoly (orderPolytope Chain2) = 3 + 3 * X + X ^ 2 ∧
    facePoly (chainPolytope Chain2) = 3 + 3 * X + X ^ 2 := by
  have hedge : (![0, 1] : Fin 2 → ℝ) ≠ ![0, 0] := by
    intro hh
    have hi := congrFun hh 1
    norm_num at hi
  constructor
  · rw [orderPolytope_chain2_hull]
    have hrange : Set.range orderTriangle =
        ({![1, 1], ![0, 1], ![0, 0]} : Set (Fin 2 → ℝ)) := by
      ext point
      simp [orderTriangle, Fin.exists_fin_succ, or_comm, or_left_comm]
    rw [hrange]
    exact facePoly_triangle _ _ _ hedge (triangle_apex_outside 1)
  · rw [chainPolytope_chain2_hull]
    have hrange : Set.range chainTriangle =
        ({![1, 0], ![0, 1], ![0, 0]} : Set (Fin 2 → ℝ)) := by
      ext point
      simp [chainTriangle, Fin.exists_fin_succ, or_comm, or_left_comm]
    rw [hrange]
    exact facePoly_triangle _ _ _ hedge (triangle_apex_outside 0)

end HibiLi
