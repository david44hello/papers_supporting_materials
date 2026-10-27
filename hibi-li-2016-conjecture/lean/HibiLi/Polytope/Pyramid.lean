/-
HibiLiLean — paper equation (1), the pyramid face-polynomial rule.
-/
import HibiLi.Polytope.PyramidCounts
import HibiLi.Proofs.FacePoly

namespace HibiLi

open Polynomial

variable {ι : Type*} [Fintype ι]

theorem fNum_empty (dim : ℕ) : fNum (∅ : Set (ι → ℝ)) dim = 0 := by
  have empty_faces : faces (∅ : Set (ι → ℝ)) dim = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro face ⟨hface, _⟩
    obtain ⟨point, member⟩ := hface.1
    exact hface.subset member
  simp [fNum, empty_faces]

theorem facePoly_empty : facePoly (∅ : Set (ι → ℝ)) = 0 := by
  ext dim
  simp [Proofs.facePoly_coeff, fNum_empty]

theorem faces_singleton (point : ι → ℝ) (dim : ℕ) :
    faces {point} dim = if dim = 0 then {{point}} else ∅ := by
  ext face
  constructor
  · rintro ⟨hface, dimension⟩
    obtain ⟨member, inFace⟩ := hface.1
    have same : member = point := hface.subset inFace
    have face_eq : face = {point} := Set.Subset.antisymm hface.subset
      (Set.singleton_subset_iff.mpr (same ▸ inFace))
    subst face
    have singleton_dim : adim ({point} : Set (ι → ℝ)) = 0 := by simp [adim]
    have zero : dim = 0 := dimension.symm.trans singleton_dim
    simp [zero]
  · split_ifs with zero
    · rintro rfl
      exact ⟨IsFace.refl (Set.singleton_nonempty point), by simp [adim, zero]⟩
    · simp

theorem facePoly_singleton (point : ι → ℝ) : facePoly {point} = 1 := by
  ext dim
  rw [Proofs.facePoly_coeff]
  unfold fNum
  rw [faces_singleton]
  by_cases zero : dim = 0 <;> simp [zero, coeff_one]

theorem eq_1_pyramid_proved (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (v : ι → ℝ)
    (hv : v ∉ affineSpan ℝ Q) :
    facePoly (convexHull ℝ (insert v Q)) = 1 + (1 + X) * facePoly Q := by
  rcases Q.eq_empty_or_nonempty with rfl | nonempty
  · simp [facePoly_empty, facePoly_singleton]
  · ext dim
    rw [add_mul, one_mul]
    cases dim with
    | zero =>
      simp only [coeff_add, coeff_one_zero, coeff_X_mul_zero, add_zero, Proofs.facePoly_coeff]
      rw [pyramid_fNum_zero hQ nonempty v hv]
      push_cast
      ring
    | succ dim =>
      simp only [coeff_add, coeff_one, Nat.add_one_ne_zero, ite_false,
        coeff_X_mul, zero_add, Proofs.facePoly_coeff]
      rw [pyramid_fNum_succ hQ nonempty v hv]
      push_cast
      rfl

end HibiLi
