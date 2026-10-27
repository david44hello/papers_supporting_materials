/-
HibiLiLean — full-dimensional pieces in finite closed convex covers.
-/
import HibiLi.Polytope.CellGeometry

namespace HibiLi

private theorem exists_interior_piece {X κ : Type*} [TopologicalSpace X] [BaireSpace X] [Finite κ]
    {body : Set X} (nonempty : (interior body).Nonempty) (pieces : κ → Set X)
    (closed : ∀ index, IsClosed (pieces index)) (covers : body ⊆ ⋃ index, pieces index) :
    ∃ index, (interior (pieces index)).Nonempty := by
  by_contra none
  push Not at none
  have nowhere (index : κ) : IsNowhereDense (pieces index) := by
    rw [IsNowhereDense, (closed index).closure_eq]
    exact none index
  have empty := interior_iUnion_of_isClosed closed nowhere
  have included := interior_mono covers
  rw [empty] at included
  exact nonempty.ne_empty (Set.eq_empty_of_subset_empty included)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsPolytope.isCompact {body : Set E} (polytope : IsPolytope body) : IsCompact body := by
  obtain ⟨vertices, rfl⟩ := polytope
  exact vertices.finite_toSet.isCompact_convexHull ℝ

theorem IsPolytope.isClosed {body : Set E} (polytope : IsPolytope body) : IsClosed body :=
  polytope.isCompact.isClosed

theorem full_interior_pieces_cover {κ : Type*} [Fintype κ] {body : Set E}
    (convex : Convex ℝ body) (nonempty : (interior body).Nonempty)
    (pieces : κ → Set E) (closed : ∀ index, IsClosed (pieces index))
    (covers : body ⊆ ⋃ index, pieces index) :
    body ⊆ ⋃ index : {index // (interior (pieces index)).Nonempty}, pieces index := by
  classical
  let good := ⋃ index : {index // (interior (pieces index)).Nonempty}, pieces index
  have good_closed : IsClosed good := isClosed_iUnion_of_finite fun index => closed index.1
  have inside : interior body ⊆ good := by
    intro point member
    by_contra outside
    let region := interior body ∩ goodᶜ
    have opened : IsOpen region := isOpen_interior.inter good_closed.isOpen_compl
    have region_nonempty : (interior region).Nonempty := by
      rw [opened.interior_eq]
      exact ⟨point, member, outside⟩
    have bad_cover : region ⊆ ⋃ index : {index // ¬(interior (pieces index)).Nonempty}, pieces index := by
      intro other inside
      obtain ⟨index, in_piece⟩ := Set.mem_iUnion.mp (covers (interior_subset inside.1))
      have bad : ¬(interior (pieces index)).Nonempty := fun full =>
        inside.2 (Set.mem_iUnion.mpr ⟨⟨index, full⟩, in_piece⟩)
      exact Set.mem_iUnion.mpr ⟨⟨index, bad⟩, in_piece⟩
    obtain ⟨index, full⟩ := exists_interior_piece region_nonempty
      (fun index : {index // ¬(interior (pieces index)).Nonempty} => pieces index)
      (fun index => closed index.1) bad_cover
    exact index.2 full
  have closure_inside := closure_minimal inside good_closed
  rw [convex.closure_interior_eq_closure_of_nonempty_interior nonempty] at closure_inside
  exact subset_closure.trans closure_inside

theorem exists_full_dim_intersection {κ : Type*} [Fintype κ] {body : Set E}
    (polytope : IsPolytope body) (nonempty : body.Nonempty) (pieces : κ → Set E)
    (closed : ∀ index, IsClosed (pieces index)) (covers : body ⊆ ⋃ index, pieces index) :
    ∃ index, (body ∩ pieces index).Nonempty ∧ adim (body ∩ pieces index) = adim body := by
  classical
  obtain ⟨base, base_member⟩ := nonempty
  let : Nonempty (affineSpan ℝ body) := ⟨⟨base, subset_affineSpan ℝ body base_member⟩⟩
  let : CompleteSpace (affineSpan ℝ body) :=
    (affineSpan ℝ body).closed_of_finiteDimensional.completeSpace_coe
  let subbody : Set (affineSpan ℝ body) := (↑) ⁻¹' body
  let subpieces : κ → Set (affineSpan ℝ body) := fun index => (↑) ⁻¹' (body ∩ pieces index)
  have subbody_interior : (interior subbody).Nonempty := by
    obtain ⟨point, member⟩ := (show body.Nonempty from ⟨base, base_member⟩).intrinsicInterior polytope.convex
    obtain ⟨intrinsicPoint, opened, _⟩ := mem_intrinsicInterior.mp member
    exact ⟨intrinsicPoint, opened⟩
  have subclosed (index : κ) : IsClosed (subpieces index) :=
    (polytope.isClosed.inter (closed index)).preimage continuous_subtype_val
  have subcovers : subbody ⊆ ⋃ index, subpieces index := by
    intro point member
    obtain ⟨index, in_piece⟩ := Set.mem_iUnion.mp (covers member)
    exact Set.mem_iUnion.mpr ⟨index, member, in_piece⟩
  obtain ⟨index, full⟩ := exists_interior_piece subbody_interior subpieces subclosed subcovers
  have span_top : affineSpan ℝ (subpieces index) = ⊤ := by
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top full]
    exact affineSpan_mono ℝ interior_subset
  have image_eq : (affineSpan ℝ body).subtype '' subpieces index = body ∩ pieces index := by
    ext point
    constructor
    · rintro ⟨original, member, rfl⟩
      exact member
    · intro member
      exact ⟨⟨point, subset_affineSpan ℝ body member.1⟩, member, rfl⟩
  have top_image : (⊤ : AffineSubspace ℝ (affineSpan ℝ body)).map (affineSpan ℝ body).subtype =
      affineSpan ℝ body := by
    ext point
    constructor
    · rintro ⟨original, _, rfl⟩
      exact original.2
    · intro member
      exact ⟨⟨point, member⟩, by trivial, rfl⟩
  have span_eq := congrArg (AffineSubspace.map (affineSpan ℝ body).subtype) span_top
  rw [AffineSubspace.map_span, image_eq, top_image] at span_eq
  have direction_eq := congrArg AffineSubspace.direction span_eq
  simp only [direction_affineSpan] at direction_eq
  refine ⟨index, ?_, ?_⟩
  · obtain ⟨point, member⟩ := full
    have in_piece : point ∈ subpieces index := interior_subset member
    exact ⟨point, in_piece⟩
  · unfold adim
    rw [direction_eq]

end HibiLi
