/-
HibiLiLean — the face-count recurrence for a pyramid.
-/
import HibiLi.Polytope.PyramidClassification

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsFace.pyramid_base {body face : Set E} (polytope : IsPolytope body)
    (hface : IsFace body face) (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    IsFace (convexHull ℝ (insert apex body)) face :=
  IsFace.trans (polytope.convexHull_insert apex)
    (pyramid_base_and_apex_faces polytope (hface.1.mono hface.subset) apex outside).1 hface

theorem IsFace.pyramid_adim {body face : Set E} (hface : IsFace body face)
    (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    adim (convexHull ℝ (insert apex face)) = adim face + 1 :=
  adim_convexHull_insert hface.1 apex (fun member => outside ((affineSpan_mono ℝ hface.subset) member))

theorem pyramid_faces_zero {body : Set E} (polytope : IsPolytope body)
    (nonempty : body.Nonempty) (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    faces (convexHull ℝ (insert apex body)) 0 = insert {apex} (faces body 0) := by
  ext face
  constructor
  · rintro ⟨hface, dimension⟩
    rcases pyramid_face_classification polytope nonempty apex outside hface with
      rfl | base_face | ⟨baseFace, base_face, rfl⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨base_face, dimension⟩
    · rw [base_face.pyramid_adim apex outside] at dimension
      omega
  · rintro (rfl | ⟨base_face, dimension⟩)
    · exact ⟨(pyramid_base_and_apex_faces polytope nonempty apex outside).2, by simp [adim]⟩
    · exact ⟨base_face.pyramid_base polytope apex outside, dimension⟩

theorem pyramid_faces_succ {body : Set E} (polytope : IsPolytope body)
    (nonempty : body.Nonempty) (apex : E) (outside : apex ∉ affineSpan ℝ body) (dim : ℕ) :
    faces (convexHull ℝ (insert apex body)) (dim + 1) = faces body (dim + 1) ∪
      (fun face => convexHull ℝ (insert apex face)) '' faces body dim := by
  ext face
  constructor
  · rintro ⟨hface, dimension⟩
    rcases pyramid_face_classification polytope nonempty apex outside hface with
      rfl | base_face | ⟨baseFace, base_face, rfl⟩
    · have singleton_dim : adim ({apex} : Set E) = 0 := by simp [adim]
      rw [singleton_dim] at dimension
      omega
    · exact Or.inl ⟨base_face, dimension⟩
    · right
      refine ⟨baseFace, ⟨base_face, ?_⟩, rfl⟩
      rw [base_face.pyramid_adim apex outside] at dimension
      omega
  · rintro (⟨base_face, dimension⟩ | ⟨baseFace, ⟨base_face, dimension⟩, rfl⟩)
    · exact ⟨base_face.pyramid_base polytope apex outside, dimension⟩
    · exact ⟨base_face.pyramid_join polytope apex outside,
        (base_face.pyramid_adim apex outside).trans (congrArg (· + 1) dimension)⟩

theorem pyramid_fNum_zero {body : Set E} (polytope : IsPolytope body)
    (nonempty : body.Nonempty) (apex : E) (outside : apex ∉ affineSpan ℝ body) :
    fNum (convexHull ℝ (insert apex body)) 0 = fNum body 0 + 1 := by
  unfold fNum
  rw [pyramid_faces_zero polytope nonempty apex outside]
  apply Set.ncard_insert_of_notMem _ (polytope.faces_finite 0)
  intro member
  exact outside (subset_affineSpan ℝ body (member.1.subset (Set.mem_singleton apex)))

theorem pyramid_fNum_succ {body : Set E} (polytope : IsPolytope body)
    (nonempty : body.Nonempty) (apex : E) (outside : apex ∉ affineSpan ℝ body) (dim : ℕ) :
    fNum (convexHull ℝ (insert apex body)) (dim + 1) = fNum body (dim + 1) + fNum body dim := by
  unfold fNum
  rw [pyramid_faces_succ polytope nonempty apex outside dim]
  have disjoint : Disjoint (faces body (dim + 1))
      ((fun face => convexHull ℝ (insert apex face)) '' faces body dim) := by
    apply Set.disjoint_left.mpr
    rintro joined base_member ⟨baseFace, _, rfl⟩
    exact outside (subset_affineSpan ℝ body
      (base_member.1.subset (subset_convexHull ℝ _ (Set.mem_insert _ _))))
  rw [Set.ncard_union_eq disjoint (polytope.faces_finite _)
    ((polytope.faces_finite _).image _)]
  congr 1
  apply (Set.ncard_image_iff (polytope.faces_finite dim)).mpr
  exact (pyramid_join_injective polytope apex outside).mono (fun _ member => member.1)

end HibiLi
