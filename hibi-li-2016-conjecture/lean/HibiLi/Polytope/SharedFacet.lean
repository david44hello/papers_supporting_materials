/-
HibiLi/Polytope/SharedFacet.lean — a common facet of two full-dimensional subcells lies inside the big polytope.
If `A, B ⊆ E` have the dimension of `E` and `A ∩ B` is a face of `A` of one dimension less, then
`relint (A ∩ B) ⊆ relint E` (used for Lemma 3.5(ii)).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Polytope

open Set Filter
open scoped Topology

namespace HibiLi

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Near a relative-interior point, every point of the affine span of the body lies in the body. -/
theorem eventually_mem_of_mem_intrinsicInterior {body : Set V} {point : V}
    (interior : point ∈ intrinsicInterior ℝ body) :
    ∀ᶠ other in 𝓝 point, other ∈ affineSpan ℝ body → other ∈ body := by
  obtain ⟨inner, open_member, rfl⟩ := mem_intrinsicInterior.mp interior
  obtain ⟨nearby, nearby_mem, inside⟩ :=
    (mem_nhds_subtype _ inner _).mp (mem_interior_iff_mem_nhds.mp open_member)
  filter_upwards [nearby_mem] with other near span
  exact inside (show (⟨other, span⟩ : affineSpan ℝ body) ∈ Subtype.val ⁻¹' nearby from near)

/-- Converse: a point of the affine span whose nearby span points all lie in the body is relatively interior. -/
theorem mem_intrinsicInterior_of_eventually {body : Set V} {point : V}
    (span : point ∈ affineSpan ℝ body)
    (nearby : ∀ᶠ other in 𝓝 point, other ∈ affineSpan ℝ body → other ∈ body) :
    point ∈ intrinsicInterior ℝ body := by
  refine mem_intrinsicInterior.mpr ⟨⟨point, span⟩, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  exact ((continuous_subtype_val.tendsto _).eventually nearby).mono fun other member => member other.2

/-- Cone lemma.  A convex body containing a point `apex` of `slab` strictly below the level `functional point`, and
near `point` every point of the slice `slab ∩ {functional = functional point}`, contains every point of `slab` near
`point` on the apex side: such a point lies on the segment from its foot on the slice to the apex. -/
theorem eventually_mem_of_slice {body : Set V} (convex : Convex ℝ body) (slab : AffineSubspace ℝ V)
    (functional : StrongDual ℝ V) {point apex : V} (apex_body : apex ∈ body) (apex_slab : apex ∈ slab)
    (below : functional apex < functional point)
    (slice : ∀ᶠ other in 𝓝 point, other ∈ slab → functional other = functional point → other ∈ body) :
    ∀ᶠ other in 𝓝 point, other ∈ slab → functional other ≤ functional point → other ∈ body := by
  have gap_pos : 0 < functional point - functional apex := sub_pos.mpr below
  -- `other = (1 - ratio) • foot + ratio • apex`, with `foot` on the slice
  let ratio : V → ℝ := fun other => (functional point - functional other) / (functional point - functional apex)
  let foot : V → V := fun other => other + (ratio other / (1 - ratio other)) • (other - apex)
  have ratio_cont : Continuous ratio := by fun_prop
  have ratio_zero : ratio point = 0 := by simp [ratio]
  have foot_cont : ContinuousAt foot point :=
    continuousAt_id.add ((ratio_cont.continuousAt.div (continuousAt_const.sub ratio_cont.continuousAt)
      (by simp [ratio_zero])).smul (continuousAt_id.sub continuousAt_const))
  have foot_tend : Tendsto foot (𝓝 point) (𝓝 point) := by
    simpa [foot, ratio_zero] using foot_cont.tendsto
  have small : ∀ᶠ other in 𝓝 point, ratio other < 1 :=
    (ratio_cont.tendsto point).eventually_lt_const (by simp [ratio_zero])
  filter_upwards [foot_tend.eventually slice, small] with other foot_slice small_ratio member level
  have ratio_nonneg : 0 ≤ ratio other := div_nonneg (sub_nonneg.mpr level) gap_pos.le
  have rest_pos : 0 < 1 - ratio other := sub_pos.mpr small_ratio
  have foot_mem : foot other ∈ slab := by
    have direction : (ratio other / (1 - ratio other)) • (other -ᵥ apex) ∈ slab.direction :=
      slab.direction.smul_mem _ (slab.vsub_mem_direction member apex_slab)
    simpa [foot, vadd_eq_add, vsub_eq_sub, add_comm] using slab.vadd_mem_of_mem_direction direction member
  have foot_level : functional (foot other) = functional point := by
    have rest_eq : 1 - ratio other =
        (functional other - functional apex) / (functional point - functional apex) := by
      simp only [ratio]
      field_simp
      ring
    have apex_lt : 0 < functional other - functional apex := by
      rw [rest_eq] at rest_pos
      exact (div_pos_iff_of_pos_right gap_pos).mp rest_pos
    simp only [foot, map_add, map_smul, map_sub, smul_eq_mul]
    rw [rest_eq]
    simp only [ratio]
    field_simp
    ring
  have combo := convex (foot_slice foot_mem foot_level) apex_body rest_pos.le ratio_nonneg (by ring)
  have cancel : (1 - ratio other) * (ratio other / (1 - ratio other)) = ratio other := by
    field_simp
  have recombine : (1 - ratio other) • foot other + ratio other • apex = other := by
    simp only [foot, smul_add, smul_smul, cancel]
    module
  rwa [recombine] at combo

end General

theorem interior_shared_facet {ι : Type*} [Fintype ι] {E A B : Set (ι → ℝ)}
    (hE : IsPolytope E) (hA : IsPolytope A) (hB : IsPolytope B) (hAE : A ⊆ E) (hBE : B ⊆ E)
    (hAdim : adim A = adim E) (hBdim : adim B = adim E) (hAB : A ≠ B)
    (hfA : IsFace A (A ∩ B)) (hfB : IsFace B (A ∩ B)) (hdim : adim (A ∩ B) + 1 = adim E) :
    intrinsicInterior ℝ (A ∩ B) ⊆ intrinsicInterior ℝ E := by
  -- only convexity of `A` and `B` and the face property in `A` are used (`hE`, `hAB`, `hfB` are not needed)
  intro point interior
  have point_mem : point ∈ A ∩ B := intrinsicInterior_subset interior
  have convexA : Convex ℝ A := by
    obtain ⟨vertices, rfl⟩ := hA
    exact convex_convexHull ℝ _
  have convexB : Convex ℝ B := by
    obtain ⟨vertices, rfl⟩ := hB
    exact convex_convexHull ℝ _
  have spanE : ∀ other ∈ E, other ∈ affineSpan ℝ E := fun _ member => subset_affineSpan ℝ E member
  -- the exposing functional of the face `A ∩ B` of `A`, with level `functional point`
  obtain ⟨functional, exposed⟩ := hfA.2 ⟨point, point_mem⟩
  have top : ∀ other ∈ A, functional other ≤ functional point := by
    have member := point_mem
    rw [exposed] at member
    exact member.2
  have level : ∀ other ∈ A ∩ B, functional other = functional point := by
    intro other member
    have maximal := member
    rw [exposed] at maximal
    exact le_antisymm (top other member.1) (maximal.2 point point_mem.1)
  have small_of_subset : ∀ body : Set (ι → ℝ), body ⊆ affineSpan ℝ (A ∩ B) → adim body ≤ adim (A ∩ B) := by
    intro body subset
    have directions := AffineSubspace.direction_le (affineSpan_le.mpr subset)
    rw [direction_affineSpan, direction_affineSpan] at directions
    exact Submodule.finrank_mono directions
  -- `A` has a point strictly below the level, else `A ⊆ A ∩ B` would be too small
  obtain ⟨low, low_mem, low_lt⟩ : ∃ low ∈ A, functional low < functional point := by
    by_contra none
    push Not at none
    have inside : A ⊆ affineSpan ℝ (A ∩ B) := by
      intro other member
      have in_face : other ∈ A ∩ B := by
        rw [exposed]
        exact ⟨member, fun third third_mem =>
          (top third third_mem).trans (none other member)⟩
      exact subset_affineSpan ℝ _ in_face
    have := small_of_subset A inside
    omega
  -- inside `aff E`, the level set of `functional` through `point` is exactly `aff (A ∩ B)`
  have span_le : vectorSpan ℝ (A ∩ B) ≤
      vectorSpan ℝ E ⊓ LinearMap.ker (functional : (ι → ℝ) →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨first, first_mem, second, second_mem, rfl⟩
    refine ⟨vsub_mem_vectorSpan ℝ (hAE first_mem.1) (hAE second_mem.1), ?_⟩
    simp [LinearMap.mem_ker, level first first_mem, level second second_mem]
  have proper : vectorSpan ℝ E ⊓ LinearMap.ker (functional : (ι → ℝ) →ₗ[ℝ] ℝ) < vectorSpan ℝ E := by
    refine lt_of_le_of_ne inf_le_left fun same => ?_
    have step : low -ᵥ point ∈ vectorSpan ℝ E := vsub_mem_vectorSpan ℝ (hAE low_mem) (hAE point_mem.1)
    rw [← same] at step
    have flat := step.2
    simp [LinearMap.mem_ker] at flat
    linarith
  have span_eq := Submodule.eq_of_le_of_finrank_eq span_le
    (le_antisymm (Submodule.finrank_mono span_le)
      (by have := Submodule.finrank_lt_finrank_of_lt proper; unfold adim at hdim; omega))
  have slice : ∀ other ∈ affineSpan ℝ E, functional other = functional point →
      other ∈ affineSpan ℝ (A ∩ B) := by
    intro other span same
    have step : other -ᵥ point ∈ vectorSpan ℝ (A ∩ B) := by
      rw [span_eq]
      refine ⟨?_, ?_⟩
      · rw [← direction_affineSpan]
        exact AffineSubspace.vsub_mem_direction span (spanE point (hAE point_mem.1))
      · simp [LinearMap.mem_ker, same]
    have moved := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan])
      (subset_affineSpan ℝ (A ∩ B) point_mem)
    simpa using moved
  have slice_near : ∀ᶠ other in 𝓝 point, other ∈ affineSpan ℝ E →
      functional other = functional point → other ∈ A ∩ B :=
    (eventually_mem_of_mem_intrinsicInterior interior).mono fun other near span same =>
      near (slice other span same)
  have lowA := eventually_mem_of_slice convexA (affineSpan ℝ E) functional low_mem (spanE low (hAE low_mem))
    low_lt (slice_near.mono fun _ near span same => (near span same).1)
  by_cases above : ∃ high ∈ B, functional point < functional high
  · -- opposite sides: near `point`, `aff E` is covered by `A ∪ B ⊆ E`
    obtain ⟨high, high_mem, high_gt⟩ := above
    have highB := eventually_mem_of_slice convexB (affineSpan ℝ E) (-functional) high_mem
      (spanE high (hBE high_mem)) (by simpa using high_gt)
      (slice_near.mono fun _ near span same => (near span (by simpa using same)).2)
    apply mem_intrinsicInterior_of_eventually (spanE point (hAE point_mem.1))
    filter_upwards [lowA, highB] with other inA inB span
    rcases le_total (functional other) (functional point) with below | below
    · exact hAE (inA span below)
    · exact hBE (inB span (by simpa using below))
  · -- same side is impossible: then `B` contains points of `A` strictly below the level near `point`
    push Not at above
    exfalso
    obtain ⟨lowB, lowB_mem, lowB_lt⟩ : ∃ lowB ∈ B, functional lowB < functional point := by
      by_contra none
      push Not at none
      have inside : B ⊆ affineSpan ℝ (A ∩ B) := fun other member =>
        slice other (spanE other (hBE member)) (le_antisymm (above other member) (none other member))
      have := small_of_subset B inside
      omega
    have nearB := eventually_mem_of_slice convexB (affineSpan ℝ E) functional lowB_mem
      (spanE lowB (hBE lowB_mem)) lowB_lt
      (slice_near.mono fun _ near span same => (near span same).2)
    have path : Tendsto (fun scalar : ℝ => AffineMap.lineMap point low scalar) (𝓝 0) (𝓝 point) := by
      have continuous : Continuous (fun scalar : ℝ => AffineMap.lineMap point low scalar) := by fun_prop
      simpa using continuous.tendsto 0
    obtain ⟨scalar, inB, scalar_pos, scalar_lt⟩ :=
      (((path.eventually nearB).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and
        (Ioo_mem_nhdsGT (zero_lt_one' ℝ))).exists
    have value : functional (AffineMap.lineMap point low scalar) =
        functional point + scalar * (functional low - functional point) := by
      simp [AffineMap.lineMap_apply_module]
      ring
    have strict : functional (AffineMap.lineMap point low scalar) < functional point := by
      rw [value]
      nlinarith
    have memA := convexA.lineMap_mem point_mem.1 low_mem ⟨scalar_pos.le, scalar_lt.le⟩
    have memB := inB (AffineMap.lineMap_mem scalar (spanE point (hAE point_mem.1)) (spanE low (hAE low_mem)))
      strict.le
    have := level _ ⟨memA, memB⟩
    linarith

end HibiLi
