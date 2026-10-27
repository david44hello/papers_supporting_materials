/-
HibiLi — geometric consequences of the checked center-switch support counts.
-/
import HibiLi.Example21.CenterCounts
import HibiLi.Example21.CarrierTransport

namespace HibiLi.Example21.CenterRegions

theorem base_eq_supportHull : base = supportHull points (maskFinset 127) := by
  change body none none = _
  rw [body_eq_hull, base_vertices]

theorem s_count (face : Finset (Fin 8)) (dim : ℕ) :
    carriedCount base familyS (supportHull points face) dim = count sFaces face dim := by
  rw [sFaces_geometry]
  exact carrier_count_eq points points_zeroOne points_injective base baseFaces sFaces baseFaces_geometry
    dimension (fun support member => family_dimension_eq (sFaces_subset member)) face dim

theorem t_count (face : Finset (Fin 8)) (dim : ℕ) :
    carriedCount base familyT (supportHull points face) dim = count tFaces face dim := by
  rw [tFaces_geometry]
  exact carrier_count_eq points points_zeroOne points_injective base baseFaces tFaces baseFaces_geometry
    dimension (fun support member => family_dimension_eq (tFaces_subset member)) face dim

theorem r_count (face : Finset (Fin 8)) (dim : ℕ) :
    carriedCount base familyR (supportHull points face) dim = count rFaces face dim := by
  rw [rFaces_geometry]
  exact carrier_count_eq points points_zeroOne points_injective base baseFaces rFaces baseFaces_geometry
    dimension (fun support member => family_dimension_eq (rFaces_subset member)) face dim

theorem geometric_base_counts (dim : ℕ) :
    carriedCount base familyS base dim = (if dim = 4 then 2 else if dim = 3 then 1 else 0) ∧
    carriedCount base familyT base dim = (if dim = 4 then 2 else if dim = 3 then 1 else 0) ∧
    carriedCount base familyR base dim =
      (if dim = 4 then 4 else if dim = 3 then 4 else if dim = 2 then 1 else 0) := by
  have hs := s_count (maskFinset 127) dim
  have ht := t_count (maskFinset 127) dim
  have hr := r_count (maskFinset 127) dim
  rw [← base_eq_supportHull] at hs ht hr
  rw [hs, ht, hr]
  exact base_counts dim

theorem geometric_proper_coeff (face : Set (Fin 4 → ℝ)) (hface : IsFace base face)
    (proper : face ≠ base) (dim : ℕ) :
    (carriedCount base familyR face dim : ℤ) - carriedCount base familyS face dim -
      carriedCount base familyT face dim + (if dim = adim face then 1 else 0) = 0 := by
  have member : face ∈ {F | IsFace base F} := hface
  rw [baseFaces_geometry] at member
  obtain ⟨support, hs, rfl⟩ := member
  have ne : support ≠ maskFinset 127 := by
    intro same
    apply proper
    rw [same, ← base_eq_supportHull]
  have allMember := baseFaces_subset hs
  rw [s_count, t_count, r_count, family_dimension_eq allMember]
  exact proper_counts support hs ne dim

end HibiLi.Example21.CenterRegions
