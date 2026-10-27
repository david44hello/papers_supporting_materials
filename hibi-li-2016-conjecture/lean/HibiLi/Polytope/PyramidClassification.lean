/-
HibiLiLean — classification and uniqueness of nonempty pyramid faces.
-/
import HibiLi.Polytope.PyramidFaces

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem pyramid_face_classification {body face : Set E} (polytope : IsPolytope body)
    (nonempty : body.Nonempty) (apex : E) (outside : apex ∉ affineSpan ℝ body)
    (hface : IsFace (convexHull ℝ (insert apex body)) face) :
    face = {apex} ∨ IsFace body face ∨
      ∃ baseFace, IsFace body baseFace ∧ face = convexHull ℝ (insert apex baseFace) := by
  have body_inside : body ⊆ convexHull ℝ (insert apex body) :=
    fun _ member => subset_convexHull ℝ _ (Set.mem_insert_of_mem _ member)
  have base_face := (pyramid_base_and_apex_faces polytope nonempty apex outside).1
  obtain ⟨vertices, body_eq⟩ := polytope
  have representation : face = convexHull ℝ (insert apex (vertices : Set E) ∩ face) := by
    have finite_face : IsFace (convexHull ℝ (insert apex (vertices : Set E))) face := by
      simpa only [body_eq, convexHull_insert_convexHull] using hface
    exact finite_face.eq_convexHull_inter (vertices.finite_toSet.insert apex)
  have vertex_inside : (vertices : Set E) ⊆ body := by
    rw [body_eq]
    exact subset_convexHull ℝ _
  by_cases apex_member : apex ∈ face
  · by_cases intersection_nonempty : (face ∩ body).Nonempty
    · right; right
      refine ⟨face ∩ body, ?_, ?_⟩
      · exact (hface.inter base_face intersection_nonempty).mono body_inside Set.inter_subset_right
      · apply Set.Subset.antisymm
        · conv_lhs => rw [representation]
          apply convexHull_mono
          rintro point ⟨rfl | vertex_member, face_member⟩
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ ⟨face_member, vertex_inside vertex_member⟩
        · apply convexHull_min _ (hface.2.convex (convex_convexHull ℝ _))
          exact Set.insert_subset_iff.mpr ⟨apex_member, Set.inter_subset_left⟩
    · left
      have selected : insert apex (vertices : Set E) ∩ face = {apex} := by
        ext point
        constructor
        · rintro ⟨rfl | vertex_member, face_member⟩
          · rfl
          · exact (intersection_nonempty ⟨point, face_member, vertex_inside vertex_member⟩).elim
        · rintro rfl
          exact ⟨Set.mem_insert _ _, apex_member⟩
      simpa only [selected, convexHull_singleton] using representation
  · right; left
    apply hface.mono body_inside
    rw [representation, body_eq]
    apply convexHull_mono
    rintro point ⟨rfl | member, face_member⟩
    · exact (apex_member face_member).elim
    · exact member

theorem pyramid_join_inter_base {body face : Set E} (polytope : IsPolytope body)
    (hface : IsFace body face) (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    convexHull ℝ (insert apex face) ∩ body = face := by
  have base_face := (pyramid_base_and_apex_faces polytope (hface.1.mono hface.subset) apex outside).1
  have joined_face := hface.pyramid_join polytope apex outside
  have intersection_nonempty : (convexHull ℝ (insert apex face) ∩ body).Nonempty := by
    obtain ⟨point, member⟩ := hface.1
    exact ⟨point, subset_convexHull ℝ _ (Set.mem_insert_of_mem _ member), hface.subset member⟩
  have intersection_face := (joined_face.inter base_face intersection_nonempty).mono
    joined_face.subset Set.inter_subset_left
  obtain ⟨vertices, face_eq⟩ := polytope.face hface
  have joined_eq : convexHull ℝ (insert apex face) = convexHull ℝ (insert apex (vertices : Set E)) := by
    rw [face_eq, convexHull_insert_convexHull]
  have finite_face : IsFace (convexHull ℝ (insert apex (vertices : Set E)))
      (convexHull ℝ (insert apex face) ∩ body) := by
    rw [← joined_eq]
    exact intersection_face
  have selected : insert apex (vertices : Set E) ∩
      (convexHull ℝ (insert apex face) ∩ body) = vertices := by
    ext point
    constructor
    · rintro ⟨rfl | member, _, body_member⟩
      · exact (outside (subset_affineSpan ℝ body body_member)).elim
      · exact member
    · intro member
      have face_member : point ∈ face := by rw [face_eq]; exact subset_convexHull ℝ _ member
      exact ⟨Set.mem_insert_of_mem _ member,
        subset_convexHull ℝ _ (Set.mem_insert_of_mem _ face_member), hface.subset face_member⟩
  have result := finite_face.eq_convexHull_inter (vertices.finite_toSet.insert apex)
  simpa only [selected, ← face_eq] using result

theorem pyramid_join_injective {body : Set E} (polytope : IsPolytope body)
    (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    Set.InjOn (fun face => convexHull ℝ (insert apex face)) {face | IsFace body face} := by
  intro left hleft right hright same
  have intersections := congrArg (fun joined => joined ∩ body) same
  simpa only [pyramid_join_inter_base polytope hleft apex outside,
    pyramid_join_inter_base polytope hright apex outside] using intersections

end HibiLi
