/-
HibiLiLean — a face of a polytope face is a face of the polytope.
-/
import HibiLi.Polytope.FiniteFaces

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFace.trans {body middle face : Set E} (polytope : IsPolytope body)
    (outer : IsFace body middle) (inner : IsFace middle face) : IsFace body face := by
  classical
  rcases polytope with ⟨vertices, rfl⟩
  obtain ⟨base, inFace⟩ := inner.1
  have inMiddle : base ∈ middle := inner.subset inFace
  have inBody : base ∈ convexHull ℝ (vertices : Set E) := outer.subset inMiddle
  obtain ⟨outerFn, outer_eq⟩ := outer.2 outer.1
  obtain ⟨innerFn, inner_eq⟩ := inner.2 inner.1
  have outer_base : ∀ point ∈ convexHull ℝ (vertices : Set E), outerFn point ≤ outerFn base := by
    have member := inMiddle
    rw [outer_eq] at member
    exact member.2
  have inner_base : ∀ point ∈ middle, innerFn point ≤ innerFn base := by
    have member := inFace
    rw [inner_eq] at member
    exact member.2
  obtain ⟨bound, upper⟩ :=
    (vertices.finite_toSet.image (fun point =>
      (innerFn point - innerFn base) / (outerFn base - outerFn point))).bddAbove
  let exposing : StrongDual ℝ E := (bound + 1) • outerFn + innerFn
  have vertex_bound (point : E) (member : point ∈ vertices) :
      exposing point ≤ exposing base ∧ (exposing point = exposing base ↔ point ∈ face) := by
    have body_member := subset_convexHull ℝ (vertices : Set E) member
    by_cases middle_member : point ∈ middle
    · have outer_same : outerFn point = outerFn base := by
        have maximal := middle_member
        rw [outer_eq] at maximal
        exact le_antisymm (outer_base point body_member) (maximal.2 base inBody)
      have bound_inner := inner_base point middle_member
      have face_iff : innerFn point = innerFn base ↔ point ∈ face := by
        constructor
        · intro same
          rw [inner_eq]
          exact ⟨middle_member, fun other member => (inner_base other member).trans_eq same.symm⟩
        · intro face_member
          rw [inner_eq] at face_member
          exact le_antisymm bound_inner (face_member.2 base inMiddle)
      simp only [exposing, add_apply, smul_apply,
        smul_eq_mul, outer_same]
      exact ⟨by linarith, by simpa only [add_right_inj] using face_iff⟩
    · have strict_outer : outerFn point < outerFn base := by
        refine lt_of_le_of_ne (outer_base point body_member) ?_
        intro equal
        apply middle_member
        rw [outer_eq]
        exact ⟨body_member, fun other member => (outer_base other member).trans_eq equal.symm⟩
      have ratio_bound := upper (Set.mem_image_of_mem
        (fun point => (innerFn point - innerFn base) / (outerFn base - outerFn point)) member)
      have strict_inner : innerFn point - innerFn base <
          (bound + 1) * (outerFn base - outerFn point) :=
        (div_lt_iff₀ (sub_pos.mpr strict_outer)).mp (lt_of_le_of_lt ratio_bound (by linarith))
      have strict : exposing point < exposing base := by
        simp only [exposing, add_apply, smul_apply,
          smul_eq_mul]
        nlinarith
      exact ⟨strict.le, iff_of_false (ne_of_lt strict) (fun member => middle_member (inner.subset member))⟩
  have full_bound : ∀ point ∈ convexHull ℝ (vertices : Set E), exposing point ≤ exposing base := by
    apply convexHull_min
    · exact fun point member => (vertex_bound point member).1
    · exact (convex_Iic (exposing base)).linear_preimage exposing.toLinearMap
  let selected : Set E := {point ∈ convexHull ℝ (vertices : Set E) |
    ∀ other ∈ convexHull ℝ (vertices : Set E), exposing other ≤ exposing point}
  have selected_face : IsFace (convexHull ℝ (vertices : Set E)) selected :=
    ⟨⟨base, inBody, full_bound⟩, fun _ => ⟨exposing, rfl⟩⟩
  have generator_eq : (vertices : Set E) ∩ selected = (vertices : Set E) ∩ face := by
    ext point
    constructor
    · rintro ⟨member, body_member, maximal⟩
      exact ⟨member, (vertex_bound point member).2.mp
        (le_antisymm (full_bound point body_member) (maximal base inBody))⟩
    · rintro ⟨member, face_member⟩
      have same := (vertex_bound point member).2.mpr face_member
      exact ⟨member, subset_convexHull ℝ _ member,
        fun other inBody => (full_bound other inBody).trans_eq same.symm⟩
  have inner_as_hull : IsFace (convexHull ℝ ((vertices : Set E) ∩ middle)) face := by
    rw [← outer.eq_convexHull_inter vertices.finite_toSet]
    exact inner
  have inside_inter : ((vertices : Set E) ∩ middle) ∩ face = (vertices : Set E) ∩ face := by
    ext point
    constructor
    · exact fun member => ⟨member.1.1, member.2⟩
    · exact fun member => ⟨⟨member.1, inner.subset member.2⟩, member.2⟩
  have face_eq := inner_as_hull.eq_convexHull_inter (vertices.finite_toSet.inter_of_left middle)
  rw [inside_inter] at face_eq
  have selected_eq := selected_face.eq_convexHull_inter vertices.finite_toSet
  rw [generator_eq, ← face_eq] at selected_eq
  simpa only [selected_eq] using selected_face

end HibiLi
