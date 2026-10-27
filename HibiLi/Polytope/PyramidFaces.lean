/-
HibiLiLean — base, apex, and joined faces of a pyramid.
-/
import HibiLi.Polytope.PyramidHeight
import HibiLi.Polytope.Transitivity
import HibiLi.Example21.Argmax

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem isFace_convexHull_level {vertices : Set E} (finite : vertices.Finite)
    (functional : StrongDual ℝ E) (level : ℝ)
    (bounded : ∀ point ∈ vertices, functional point ≤ level)
    (attained : ∃ point ∈ vertices, functional point = level) :
    IsFace (convexHull ℝ vertices) (convexHull ℝ {point ∈ vertices | functional point = level}) := by
  obtain ⟨base, base_member, same⟩ := attained
  have selected : generatorArgmax vertices functional = {point ∈ vertices | functional point = level} := by
    ext point
    constructor
    · rintro ⟨member, maximal⟩
      exact ⟨member, le_antisymm (bounded point member) (same ▸ maximal base base_member)⟩
    · rintro ⟨member, equal⟩
      exact ⟨member, fun other member => (bounded other member).trans_eq equal.symm⟩
  simpa only [selected] using isFace_convexHull_generatorArgmax finite ⟨base, base_member⟩ functional

theorem pyramid_base_and_apex_faces {body : Set E} (polytope : IsPolytope body)
    (nonempty : body.Nonempty) (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    IsFace (convexHull ℝ (insert apex body)) body ∧
      IsFace (convexHull ℝ (insert apex body)) {apex} := by
  obtain ⟨height, level, flat, raised⟩ := exists_pyramid_height nonempty apex outside
  rcases polytope with ⟨vertices, rfl⟩
  have vertices_nonempty := convexHull_nonempty_iff.mp nonempty
  obtain ⟨base, base_member⟩ := vertices_nonempty
  have flat_vertices (point : E) (member : point ∈ vertices) : height point = level :=
    flat point (subset_convexHull ℝ _ member)
  have base_selected : {point ∈ insert apex (vertices : Set E) | (-height) point = -level} = vertices := by
    ext point
    constructor
    · rintro ⟨rfl | member, same⟩
      · simp only [neg_apply, raised] at same
        linarith
      · exact member
    · intro member
      exact ⟨Set.mem_insert_of_mem _ member, by simp [flat_vertices point member]⟩
  have apex_selected : {point ∈ insert apex (vertices : Set E) | height point = level + 1} = {apex} := by
    ext point
    constructor
    · rintro ⟨rfl | member, same⟩
      · rfl
      · rw [flat_vertices point member] at same
        linarith
    · rintro rfl
      exact ⟨Set.mem_insert _ _, raised⟩
  rw [convexHull_insert_convexHull]
  constructor
  · have result := isFace_convexHull_level (vertices.finite_toSet.insert apex) (-height) (-level)
      (by
        intro point member
        rcases member with rfl | member
        · simp only [neg_apply, raised]; linarith
        · simp [flat_vertices point member])
      ⟨base, Set.mem_insert_of_mem _ base_member, by simp [flat_vertices base base_member]⟩
    simpa only [base_selected] using result
  · have result := isFace_convexHull_level (vertices.finite_toSet.insert apex) height (level + 1)
      (by
        intro point member
        rcases member with rfl | member
        · exact raised.le
        · rw [flat_vertices point member]; linarith)
      ⟨apex, Set.mem_insert _ _, raised⟩
    simpa only [apex_selected, convexHull_singleton] using result

theorem IsFace.pyramid_join {body face : Set E} (polytope : IsPolytope body)
    (hface : IsFace body face) (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    IsFace (convexHull ℝ (insert apex body)) (convexHull ℝ (insert apex face)) := by
  obtain ⟨height, level, flat, raised⟩ := exists_pyramid_height (hface.1.mono hface.subset) apex outside
  rcases polytope with ⟨vertices, rfl⟩
  have face_rep := hface.eq_convexHull_inter vertices.finite_toSet
  have selected_nonempty : ((vertices : Set E) ∩ face).Nonempty := by
    have hull_nonempty : (convexHull ℝ ((vertices : Set E) ∩ face)).Nonempty := by
      rw [← face_rep]
      exact hface.1
    exact convexHull_nonempty_iff.mp hull_nonempty
  obtain ⟨base, base_vertex, base_face⟩ := selected_nonempty
  obtain ⟨functional, face_eq⟩ := hface.2 hface.1
  have maximal : ∀ point ∈ convexHull ℝ (vertices : Set E), functional point ≤ functional base := by
    have member := base_face
    rw [face_eq] at member
    exact member.2
  let exposing : StrongDual ℝ E := functional + (functional base - functional apex) • height
  have apex_equal : exposing apex = exposing base := by
    have base_flat := flat base (subset_convexHull ℝ _ base_vertex)
    simp only [exposing, add_apply, smul_apply, smul_eq_mul, raised, base_flat]
    ring
  have vertex_compare (point : E) (member : point ∈ vertices) :
      exposing point ≤ exposing base ∧ (exposing point = exposing base ↔ point ∈ face) := by
    have point_body := subset_convexHull ℝ (vertices : Set E) member
    have point_flat := flat point point_body
    have base_flat := flat base (subset_convexHull ℝ _ base_vertex)
    have bound := maximal point point_body
    have equal_iff : functional point = functional base ↔ point ∈ face := by
      constructor
      · intro same
        rw [face_eq]
        exact ⟨point_body, fun other member => (maximal other member).trans_eq same.symm⟩
      · intro member
        rw [face_eq] at member
        exact le_antisymm bound (member.2 base (subset_convexHull ℝ _ base_vertex))
    simp only [exposing, add_apply, smul_apply, smul_eq_mul, point_flat, base_flat]
    exact ⟨by linarith, by simpa only [add_left_inj] using equal_iff⟩
  have selected : {point ∈ insert apex (vertices : Set E) | exposing point = exposing base} =
      insert apex ((vertices : Set E) ∩ face) := by
    ext point
    constructor
    · rintro ⟨rfl | member, same⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨member, (vertex_compare point member).2.mp same⟩
    · rintro (rfl | ⟨member, face_member⟩)
      · exact ⟨Set.mem_insert _ _, apex_equal⟩
      · exact ⟨Set.mem_insert_of_mem _ member, (vertex_compare point member).2.mpr face_member⟩
  have result := isFace_convexHull_level (vertices.finite_toSet.insert apex) exposing (exposing base)
    (by
      intro point member
      rcases member with rfl | member
      · exact apex_equal.le
      · exact (vertex_compare point member).1)
    ⟨apex, Set.mem_insert _ _, apex_equal⟩
  rw [selected] at result
  rw [face_rep, convexHull_insert_convexHull, convexHull_insert_convexHull]
  exact result

end HibiLi
