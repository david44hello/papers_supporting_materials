/-
HibiLi — universal consequences of the center-switch finite counts.
-/
import HibiLi.Example21.CenterCountData

namespace HibiLi.Example21.CenterRegions

open Finset

theorem baseFaces_subset : baseFaces ⊆ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces :=
  fun _ h => mem_union_left _ (mem_union_left _ (mem_union_left _ h))

theorem sFaces_subset : sFaces ⊆ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces :=
  fun _ h => mem_union_left _ (mem_union_left _ (mem_union_right _ h))

theorem tFaces_subset : tFaces ⊆ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces :=
  fun _ h => mem_union_left _ (mem_union_right _ h)

theorem rFaces_subset : rFaces ⊆ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces :=
  fun _ h => mem_union_right _ h

theorem count_zero_above (family : Finset (Finset (Fin 8)))
    (subset : family ⊆ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces) (face : Finset (Fin 8)) (dim : ℕ)
    (high : 4 < dim) : count family face dim = 0 := by
  have empty : carriedSupports baseFaces family dimension face dim = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro support member
    obtain ⟨hs, hd, _⟩ := Finset.mem_filter.mp member
    have bound := (family_dimensions_checked support (subset hs)).2.2
    omega
  simp [count, empty]

theorem base_counts (dim : ℕ) :
    count sFaces (maskFinset 127) dim = (if dim = 4 then 2 else if dim = 3 then 1 else 0) ∧
    count tFaces (maskFinset 127) dim = (if dim = 4 then 2 else if dim = 3 then 1 else 0) ∧
    count rFaces (maskFinset 127) dim =
      (if dim = 4 then 4 else if dim = 3 then 4 else if dim = 2 then 1 else 0) := by
  by_cases small : dim < 5
  · exact base_counts_checked ⟨dim, small⟩
  · have high : 4 < dim := by omega
    have hs := count_zero_above sFaces sFaces_subset (maskFinset 127) dim high
    have ht := count_zero_above tFaces tFaces_subset (maskFinset 127) dim high
    have hr := count_zero_above rFaces rFaces_subset (maskFinset 127) dim high
    simp [hs, ht, hr, show dim ≠ 4 by omega, show dim ≠ 3 by omega, show dim ≠ 2 by omega]

theorem proper_counts (face : Finset (Fin 8)) (member : face ∈ baseFaces)
    (proper : face ≠ maskFinset 127) (dim : ℕ) :
    (count rFaces face dim : ℤ) - count sFaces face dim - count tFaces face dim +
      (if dim = dimension face then 1 else 0) = 0 := by
  by_cases small : dim < 5
  · exact proper_counts_checked face member proper ⟨dim, small⟩
  · have high : 4 < dim := by omega
    have hs := count_zero_above sFaces sFaces_subset face dim high
    have ht := count_zero_above tFaces tFaces_subset face dim high
    have hr := count_zero_above rFaces rFaces_subset face dim high
    have faceMember := baseFaces_subset member
    have bound := (family_dimensions_checked face faceMember).2.2
    simp [hs, ht, hr, show dim ≠ dimension face by omega]

end HibiLi.Example21.CenterRegions
