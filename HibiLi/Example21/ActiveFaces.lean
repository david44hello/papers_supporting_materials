/-
HibiLi — finite halfspace descriptions enumerate all nonempty faces.
-/
import HibiLi.Polytope.IntersectionFaces
import HibiLi.Example21.RationalGeometry

open Set Filter
open scoped Topology

namespace HibiLi.Example21

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {κ : Type*} [Fintype κ]

def tightRegion (body : Set E) (linear : κ → StrongDual ℝ E) (bound : κ → ℝ)
    (active : Finset κ) : Set E := {point ∈ body | ∀ index ∈ active, linear index point = bound index}

theorem tightRegion_isFace (body : Set E) (linear : κ → StrongDual ℝ E) (bound : κ → ℝ)
    (bounded : ∀ point ∈ body, ∀ index, linear index point ≤ bound index) (active : Finset κ)
    (nonempty : (tightRegion body linear bound active).Nonempty) :
    IsFace body (tightRegion body linear bound active) := by
  obtain ⟨base, base_member, base_equal⟩ := nonempty
  refine ⟨⟨base, base_member, base_equal⟩, fun _ => ⟨∑ index ∈ active, linear index, ?_⟩⟩
  ext point
  simp only [ContinuousLinearMap.sum_apply]
  constructor
  · rintro ⟨member, equal⟩
    exact ⟨member, fun other other_member => Finset.sum_le_sum fun index hi =>
      (bounded other other_member index).trans_eq (equal index hi).symm⟩
  · rintro ⟨member, maximal⟩
    have le_each : ∀ index ∈ active, linear index point ≤ linear index base :=
      fun index hi => (bounded point member index).trans_eq (base_equal index hi).symm
    have equal_sum := le_antisymm (Finset.sum_le_sum le_each) (maximal base base_member)
    refine ⟨member, fun index hi => ?_⟩
    exact ((Finset.sum_eq_sum_iff_of_le le_each).mp equal_sum index hi).trans (base_equal index hi)

theorem IsFace.exists_active_constraints (linear : κ → StrongDual ℝ E) (bound : κ → ℝ)
    {body face : Set E} (representation : body = {point | ∀ index, linear index point ≤ bound index})
    (convex : Convex ℝ body) (hface : HibiLi.IsFace body face) :
    ∃ active : Finset κ, face = tightRegion body linear bound active := by
  classical
  obtain ⟨base, interior⟩ := hface.1.intrinsicInterior (hface.2.convex convex)
  have base_face : base ∈ face := intrinsicInterior_subset interior
  have base_body := hface.subset base_face
  have bounded (point : E) (member : point ∈ body) (index : κ) : linear index point ≤ bound index := by
    rw [representation] at member
    exact member index
  let active := Finset.univ.filter fun index => linear index base = bound index
  refine ⟨active, Set.Subset.antisymm ?_ ?_⟩
  · intro point member
    refine ⟨hface.subset member, fun index hi => ?_⟩
    have equality : linear index base = bound index := (Finset.mem_filter.mp hi).2
    exact (linear_eq_of_intrinsicInterior_max interior (linear index)
      (fun other hm => (bounded other (hface.subset hm) index).trans_eq equality.symm)
      point member).trans equality
  · rintro point ⟨member, equal⟩
    have nearby : ∀ᶠ scale : ℝ in 𝓝 0, base + scale • (point - base) ∈ body := by
      simp only [representation, Set.mem_ofPred_eq]
      rw [Filter.eventually_all]
      intro index
      by_cases equality : linear index base = bound index
      · have point_eq := equal index (Finset.mem_filter.mpr ⟨Finset.mem_univ _, equality⟩)
        exact Filter.Eventually.of_forall fun scale => by
          simp [map_add, map_sub, map_smul, equality, point_eq]
      · have strict := lt_of_le_of_ne (bounded base base_body index) equality
        have continuous : Continuous (fun scale : ℝ => linear index (base + scale • (point - base))) := by
          fun_prop
        exact (continuous.continuousAt.eventually_lt_const (by simpa using strict)).mono fun _ h => h.le
    obtain ⟨radius, positive, in_ball⟩ := Metric.eventually_nhds_iff.mp nearby
    have negative : -(radius / 2) < 0 := by linarith
    have extrapolated := in_ball (y := -(radius / 2)) (by
      rw [Real.dist_eq, sub_zero, abs_of_neg negative]
      linarith)
    obtain ⟨functional, exposed⟩ := hface.2 hface.1
    have base_max := base_face
    rw [exposed] at base_max
    have lower := base_max.2 _ extrapolated
    have upper := base_max.2 point member
    simp only [map_add, map_smul, map_sub, smul_eq_mul] at lower
    have flat : functional point = functional base := by nlinarith
    rw [exposed]
    exact ⟨member, fun other other_member => (base_max.2 other other_member).trans_eq flat.symm⟩

end HibiLi.Example21
