/-
HibiLi/Polytope/SubdivisionPurity.lean — every maximal cell of a finite polytopal subdivision has the base's dimension.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Used for paper Lemma 3.5(ii).  Proof: take a relative-interior point `point` of the maximal cell.
The cells missing `point` are finitely many closed sets, so a small homothetic copy of the base centred at `point`
misses them all.  Some cell meets that copy in full dimension (`exists_full_dim_intersection`); it contains `point`,
so its intersection with the maximal cell is a face through a relative-interior point, hence the whole cell, and
maximality makes the two cells equal.
-/
import HibiLi.Defs.Subdivision
import HibiLi.Polytope.RefinementCover

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A face of `body` through a relative-interior point of `body` is `body` itself. -/
theorem IsFace.eq_of_mem_intrinsicInterior {body face : Set E} (hface : IsFace body face) {point : E}
    (in_face : point ∈ face) (relint : point ∈ intrinsicInterior ℝ body) : face = body := by
  have in_body : point ∈ body := intrinsicInterior_subset relint
  have carrier := isCarrier_of_subset_of_intrinsicInterior (IsFace.refl ⟨point, in_body⟩)
    (Set.singleton_subset_iff.mpr in_body) ⟨point, rfl, relint⟩
  exact hface.subset.antisymm (carrier.2.2 face hface (Set.singleton_subset_iff.mpr in_face))

section Shrink

variable {body : Set E} {center : E} {scale : ℝ}

omit [FiniteDimensional ℝ E] in
theorem IsPolytope.homothety_image (polytope : IsPolytope body) :
    IsPolytope (AffineMap.homothety center scale '' body) := by
  classical
  obtain ⟨vertices, rfl⟩ := polytope
  exact ⟨vertices.image (AffineMap.homothety center scale), by rw [Finset.coe_image, AffineMap.image_convexHull]⟩

omit [FiniteDimensional ℝ E] in
theorem homothety_image_subset (convex : Convex ℝ body) (member : center ∈ body)
    (nonneg : 0 ≤ scale) (le_one : scale ≤ 1) : AffineMap.homothety center scale '' body ⊆ body := by
  rintro _ ⟨point, inBody, rfl⟩
  rw [AffineMap.homothety_eq_lineMap]
  exact convex.lineMap_mem member inBody ⟨nonneg, le_one⟩

omit [FiniteDimensional ℝ E] in
theorem adim_homothety_image (nonzero : scale ≠ 0) :
    adim (AffineMap.homothety center scale '' body) = adim body := by
  have injective : Function.Injective (AffineMap.homothety center scale) := fun left right same => by
    simpa [AffineMap.homothety_apply, nonzero] using same
  unfold adim
  rw [← AffineMap.map_vectorSpan]
  exact (Submodule.equivMapOfInjective _ ((AffineMap.homothety center scale).linear_injective_iff.mpr injective)
    (vectorSpan ℝ body)).finrank_eq.symm

/-- A nonempty polytope has, around each of its points, an equal-dimensional sub-polytope inside any ball. -/
theorem exists_small_polytope (polytope : IsPolytope body) (member : center ∈ body) {radius : ℝ}
    (positive : 0 < radius) :
    ∃ small, IsPolytope small ∧ center ∈ small ∧ small ⊆ body ∧ adim small = adim body ∧
      small ⊆ Metric.ball center radius := by
  obtain ⟨bound, inBall⟩ := polytope.isCompact.isBounded.subset_closedBall center
  have bound_nonneg : 0 ≤ bound := by simpa using inBall member
  set ratio := radius / (bound + radius) with ratio_def
  have ratio_pos : 0 < ratio := div_pos positive (by linarith)
  have ratio_le : ratio ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have ratio_mul : ratio * bound < radius := by
    rw [ratio_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  refine ⟨AffineMap.homothety center ratio '' body, polytope.homothety_image,
    ⟨center, member, AffineMap.homothety_apply_same center ratio⟩,
    homothety_image_subset polytope.convex member ratio_pos.le ratio_le, adim_homothety_image ratio_pos.ne', ?_⟩
  rintro _ ⟨point, inBody, rfl⟩
  have close : dist point center ≤ bound := inBall inBody
  rw [Metric.mem_ball, dist_homothety_center, Real.norm_eq_abs, abs_of_pos ratio_pos, dist_comm]
  exact (mul_le_mul_of_nonneg_left close ratio_pos.le).trans_lt ratio_mul

end Shrink

theorem subdivision_max_adim {ι : Type*} [Fintype ι] {base : Set (ι → ℝ)} {cells : Finset (Set (ι → ℝ))}
    (hbase : IsPolytope base) (hne : base.Nonempty) (hsub : IsFinitePolytopalSubdivision base cells)
    (maximal : MaxSubdivisionCell cells) : adim maximal.1 = adim base := by
  obtain ⟨cell_props, union_eq, _, meets⟩ := hsub
  obtain ⟨cell, member, is_max⟩ := maximal
  change adim cell = adim base
  have cell_sub : cell ⊆ base := union_eq ▸ Set.subset_sUnion_of_mem member
  -- a relative-interior point of the maximal cell
  obtain ⟨point, relint⟩ := (cell_props cell member).2.intrinsicInterior (cell_props cell member).1.convex
  have point_cell : point ∈ cell := intrinsicInterior_subset relint
  -- the cells missing `point` stay a positive distance away from it
  let missing : Set (Set (ι → ℝ)) := {other | other ∈ cells ∧ point ∉ other}
  have far_closed : IsClosed (⋃ other ∈ missing, other) :=
    (cells.finite_toSet.subset fun _ inside => inside.1).isClosed_biUnion
      fun other inside => (cell_props other inside.1).1.isClosed
  have point_near : point ∈ (⋃ other ∈ missing, other)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun other inside => inside.2
  obtain ⟨radius, positive, ball_sub⟩ := Metric.isOpen_iff.mp far_closed.isOpen_compl point point_near
  -- some cell meets a small full-dimensional copy of the base around `point` in full dimension
  obtain ⟨small, small_poly, point_small, small_base, small_dim, small_ball⟩ :=
    exists_small_polytope hbase (cell_sub point_cell) positive
  have covers : small ⊆ ⋃ other : cells, (other : Set (ι → ℝ)) := by
    intro target inSmall
    have inUnion := small_base inSmall
    rw [← union_eq] at inUnion
    obtain ⟨other, otherMember, inOther⟩ := inUnion
    exact Set.mem_iUnion.mpr ⟨⟨other, otherMember⟩, inOther⟩
  obtain ⟨⟨other, otherMember⟩, touches, full⟩ := exists_full_dim_intersection small_poly ⟨point, point_small⟩
    (fun other : cells => (other : Set (ι → ℝ))) (fun other => (cell_props other.1 other.2).1.isClosed) covers
  -- that cell contains `point`, so its intersection with the maximal cell is the whole maximal cell
  have point_other : point ∈ other := by
    by_contra outside
    obtain ⟨target, inSmall, inOther⟩ := touches
    exact ball_sub (small_ball inSmall) (Set.mem_biUnion ⟨otherMember, outside⟩ inOther)
  have same : cell ∩ other = cell :=
    (meets cell member other otherMember ⟨point, point_cell, point_other⟩).1.eq_of_mem_intrinsicInterior
      ⟨point_cell, point_other⟩ relint
  have equal : other = cell := is_max other otherMember (Set.inter_eq_left.mp same)
  have upper : adim cell ≤ adim base := Submodule.finrank_mono (vectorSpan_mono ℝ cell_sub)
  have lower : adim (small ∩ other) ≤ adim other := Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_right)
  have full_dim : adim (small ∩ other) = adim base := full.trans small_dim
  rw [equal] at lower full_dim
  omega

end HibiLi
