/-
HibiLi/Proofs/PyramidFacesIff.lean — paper Section 2: the nonempty faces of a pyramid over `Q` are exactly the faces of
`Q`, the apex, and the apex joins of faces of `Q` (statement `sec2_pyramid_faces` of HibiLi/Paper/Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Polytope.PyramidClassification
import HibiLi.Polytope.PyramidDimension

namespace HibiLi.Proofs

open HibiLi

/-- The only nonempty face of a point is the point itself. -/
theorem isFace_singleton_iff {ι : Type*} [Fintype ι] (v : ι → ℝ) (F : Set (ι → ℝ)) :
    IsFace {v} F ↔ F = {v} := by
  constructor
  · intro hface
    exact hface.1.subset_singleton_iff.mp hface.subset
  · rintro rfl
    exact IsFace.refl (Set.singleton_nonempty v)

theorem sec2_pyramid_faces_proved {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (v : ι → ℝ)
    (hv : v ∉ affineSpan ℝ Q) (F : Set (ι → ℝ)) :
    IsFace (convexHull ℝ (insert v Q)) F ↔
      IsFace Q F ∨ F = {v} ∨ ∃ G, IsFace Q G ∧ F = convexHull ℝ (insert v G) := by
  rcases Q.eq_empty_or_nonempty with rfl | nonempty
  · have no_face (G : Set (ι → ℝ)) : ¬ IsFace ∅ G := fun hface =>
      hface.1.ne_empty (Set.subset_empty_iff.mp hface.subset)
    simp only [LawfulSingleton.insert_empty_eq, convexHull_singleton, isFace_singleton_iff, no_face, false_and,
      exists_false, false_or, or_false]
  · constructor
    · intro hface
      rcases pyramid_face_classification hQ nonempty v hv hface with apex | base | join
      · exact Or.inr (Or.inl apex)
      · exact Or.inl base
      · exact Or.inr (Or.inr join)
    · have base_and_apex := pyramid_base_and_apex_faces hQ nonempty v hv
      rintro (base | rfl | ⟨G, hG, rfl⟩)
      · exact IsFace.trans (hQ.convexHull_insert v) base_and_apex.1 base
      · exact base_and_apex.2
      · exact hG.pyramid_join hQ v hv

end HibiLi.Proofs
