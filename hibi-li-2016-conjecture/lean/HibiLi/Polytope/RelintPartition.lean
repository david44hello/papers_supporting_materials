/-
HibiLi/Polytope/RelintPartition.lean — the relative interiors of the cells of a subdivision partition the base.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof.  (1) A point `u` of a convex set `Q` outside its relative interior has a continuous linear functional that is
maximal over `Q` at `u` and not constant on `Q`: separate `0` from the interior of `Q − u` inside the linear span of
`Q − Q`, then extend the functional (Hahn–Banach).  (2) So every point of a polytope lies in the relative interior of
one of its faces: if it is not relatively interior, pass to the exposed face cut out by (1), which has smaller
dimension, and use that a face of a face of a polytope is a face.  (3) In a subdivision, a point lies in some cell,
hence in the relative interior of a face of it, which is a cell; two cells with the point in their relative interiors
meet in a common face through relative-interior points of both, so they are equal.
-/
import HibiLi.Defs.Subdivision
import HibiLi.Polytope.SubdivisionPurity
import HibiLi.Polytope.Transitivity
import HibiLi.Polytope.CarrierInterior
import HibiLi.Polytope.SharedFacet

open Set Filter
open scoped Topology

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `Q − u`, inside the direction `vectorSpan ℝ Q`. -/
private def shifted (Q : Set E) (u : E) : Set (vectorSpan ℝ Q) := {v | u + (v : E) ∈ Q}

omit [FiniteDimensional ℝ E] in
private theorem shifted_convex {Q : Set E} (convex : Convex ℝ Q) (u : E) : Convex ℝ (shifted Q u) :=
  (convex.translate_preimage_right u).linear_preimage (vectorSpan ℝ Q).subtype

omit [FiniteDimensional ℝ E] in
/-- A relative-interior point `c` of `Q` gives the interior point `c − u` of `Q − u`. -/
private theorem sub_mem_interior_shifted {Q : Set E} {u c : E} (member : u ∈ Q)
    (interior_c : c ∈ intrinsicInterior ℝ Q) :
    (⟨c - u, vsub_mem_vectorSpan ℝ (intrinsicInterior_subset interior_c) member⟩ : vectorSpan ℝ Q) ∈
      interior (shifted Q u) := by
  obtain ⟨radius, positive, inside⟩ := Metric.eventually_nhds_iff.mp (eventually_mem_of_mem_intrinsicInterior interior_c)
  refine mem_interior_iff_mem_nhds.mpr (Metric.eventually_nhds_iff.mpr ⟨radius, positive, fun v close => ?_⟩)
  have span : u + (v : E) ∈ affineSpan ℝ Q := by
    rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (by rw [direction_affineSpan]; exact v.2)
      (subset_affineSpan ℝ Q member)
  refine inside ?_ span
  rw [dist_eq_norm] at close ⊢
  convert close using 1
  rw [← Submodule.norm_coe, Submodule.coe_sub]
  change ‖u + (v : E) - c‖ = ‖(v : E) - (c - u)‖
  congr 1
  abel

omit [FiniteDimensional ℝ E] in
/-- If `0` is interior to `Q − u`, then `u` is relatively interior to `Q`. -/
private theorem mem_intrinsicInterior_of_zero_mem {Q : Set E} {u : E} (member : u ∈ Q)
    (zero_interior : (0 : vectorSpan ℝ Q) ∈ interior (shifted Q u)) : u ∈ intrinsicInterior ℝ Q := by
  obtain ⟨radius, positive, inside⟩ :=
    Metric.eventually_nhds_iff.mp (mem_interior_iff_mem_nhds.mp zero_interior)
  refine mem_intrinsicInterior_of_eventually (subset_affineSpan ℝ Q member)
    (Metric.eventually_nhds_iff.mpr ⟨radius, positive, fun point close span => ?_⟩)
  have direction : point - u ∈ vectorSpan ℝ Q := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction span (subset_affineSpan ℝ Q member)
  have shifted_member := inside (y := ⟨point - u, direction⟩) (by
    rw [dist_zero_right, ← Submodule.norm_coe, ← dist_eq_norm]
    exact close)
  simpa [shifted] using shifted_member

/-- **Supporting functional.**  At a point `u` of a convex set `Q` outside its relative interior, some continuous
linear functional is maximal over `Q` at `u` and not constant on `Q`. -/
theorem exists_support_of_not_mem_intrinsicInterior {Q : Set E} (convex : Convex ℝ Q) {u : E} (member : u ∈ Q)
    (boundary : u ∉ intrinsicInterior ℝ Q) :
    ∃ functional : StrongDual ℝ E, (∀ point ∈ Q, functional point ≤ functional u) ∧
      ∃ point ∈ Q, functional point < functional u := by
  obtain ⟨center, interior_center⟩ := (Set.Nonempty.intrinsicInterior convex ⟨u, member⟩ :
    (intrinsicInterior ℝ Q).Nonempty)
  have center_shift := sub_mem_interior_shifted member interior_center
  have zero_out : (0 : vectorSpan ℝ Q) ∉ interior (shifted Q u) :=
    fun zero_interior => boundary (mem_intrinsicInterior_of_zero_mem member zero_interior)
  obtain ⟨separating, below⟩ :=
    geometric_hahn_banach_open_point (shifted_convex convex u).interior isOpen_interior zero_out
  rw [map_zero] at below
  obtain ⟨functional, extends_separating, -⟩ := exists_extension_norm_eq (vectorSpan ℝ Q) separating
  have closed : IsClosed {v : vectorSpan ℝ Q | separating v ≤ 0} := isClosed_le separating.continuous continuous_const
  have nonpositive : shifted Q u ⊆ {v | separating v ≤ 0} := by
    refine subset_closure.trans ?_
    rw [← (shifted_convex convex u).closure_interior_eq_closure_of_nonempty_interior ⟨_, center_shift⟩]
    exact closed.closure_subset_iff.mpr fun v hv => (below v hv).le
  have value (point : E) (inQ : point ∈ Q) :
      functional point - functional u = separating ⟨point - u, vsub_mem_vectorSpan ℝ inQ member⟩ := by
    rw [← map_sub, ← extends_separating]
  refine ⟨functional, fun point inQ => ?_, center, intrinsicInterior_subset interior_center, ?_⟩
  · have shifted_member : (⟨point - u, vsub_mem_vectorSpan ℝ inQ member⟩ : vectorSpan ℝ Q) ∈ shifted Q u := by
      simpa [shifted] using inQ
    have nonpos : separating ⟨point - u, vsub_mem_vectorSpan ℝ inQ member⟩ ≤ 0 := nonpositive shifted_member
    linarith [value point inQ]
  · linarith [value center (intrinsicInterior_subset interior_center), below _ center_shift]

/-- Every point of a polytope lies in the relative interior of one of its (nonempty, exposed) faces. -/
theorem IsPolytope.exists_face_mem_intrinsicInterior {Q : Set E} (polytope : IsPolytope Q) {u : E}
    (member : u ∈ Q) : ∃ face, IsFace Q face ∧ u ∈ intrinsicInterior ℝ face := by
  induction hdim : adim Q using Nat.strong_induction_on generalizing Q with
  | _ dimension induction_hyp =>
  by_cases relint : u ∈ intrinsicInterior ℝ Q
  · exact ⟨Q, IsFace.refl ⟨u, member⟩, relint⟩
  obtain ⟨functional, maximal, other, other_member, other_lt⟩ :=
    exists_support_of_not_mem_intrinsicInterior polytope.convex member relint
  let top : Set E := {point ∈ Q | ∀ third ∈ Q, functional third ≤ functional point}
  have top_face : IsFace Q top := ⟨⟨u, member, maximal⟩, fun _ => ⟨functional, rfl⟩⟩
  have u_top : u ∈ top := ⟨member, maximal⟩
  have flat : ∀ point ∈ top, functional point = functional u :=
    fun point inTop => le_antisymm (maximal point inTop.1) (inTop.2 u member)
  have smaller : adim top < dimension := by
    have le : adim top ≤ adim Q := Submodule.finrank_mono (vectorSpan_mono ℝ top_face.subset)
    refine lt_of_le_of_ne (hdim ▸ le) fun same => ?_
    have spans := affineSpan_eq_of_subset_of_adim_eq ⟨u, u_top⟩ top_face.subset (same.trans hdim.symm)
    have other_span : other ∈ affineSpan ℝ top := by
      rw [spans]
      exact subset_affineSpan ℝ Q other_member
    have := linear_eq_on_affineSpan functional (functional u) flat other other_span
    linarith
  obtain ⟨face, face_top, interior⟩ :=
    induction_hyp (adim top) smaller (polytope.face top_face) u_top rfl
  exact ⟨face, top_face.trans polytope face_top, interior⟩

/-- **Paper v1.00 lines 273–274**: the relative interiors of the cells of a subdivision partition the polytope —
every point of the base lies in the relative interior of exactly one cell. -/
theorem subdivision_relint_partition {ι : Type*} [Fintype ι] (base : Set (ι → ℝ))
    (cells : Finset (Set (ι → ℝ))) (hsub : IsFinitePolytopalSubdivision base cells) (u : ι → ℝ)
    (hu : u ∈ base) : ∃! C, C ∈ cells ∧ u ∈ intrinsicInterior ℝ C := by
  obtain ⟨cell_props, union_eq, face_closed, meets⟩ := hsub
  rw [← union_eq] at hu
  obtain ⟨cell, cell_member, u_cell⟩ := hu
  obtain ⟨face, face_cell, u_face⟩ := (cell_props cell cell_member).1.exists_face_mem_intrinsicInterior u_cell
  have face_member := face_closed cell cell_member face face_cell
  refine ⟨face, ⟨face_member, u_face⟩, ?_⟩
  rintro other ⟨other_member, u_other⟩
  have both : u ∈ other ∩ face := ⟨intrinsicInterior_subset u_other, intrinsicInterior_subset u_face⟩
  obtain ⟨other_side, face_side⟩ := meets other other_member face face_member ⟨u, both⟩
  rw [← other_side.eq_of_mem_intrinsicInterior both u_other, face_side.eq_of_mem_intrinsicInterior both u_face]

end HibiLi
