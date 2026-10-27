/-
HibiLiLean — affine transport of faces and their dimensions.
-/
import HibiLi.Defs.Poset

namespace HibiLi

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ G] in
theorem adim_image_affineEquiv (equiv : E ≃ᵃ[ℝ] G) (face : Set E) :
    adim (equiv '' face) = adim face := by
  unfold adim
  change Module.finrank ℝ (vectorSpan ℝ (equiv.toAffineMap '' face)) = _
  rw [← equiv.toAffineMap.map_vectorSpan]
  exact equiv.linear.finrank_map_eq _

omit [FiniteDimensional ℝ E] in
theorem IsFace.image_affineEquiv {body face : Set E} (hface : IsFace body face)
    (equiv : E ≃ᵃ[ℝ] G) : IsFace (equiv '' body) (equiv '' face) := by
  obtain ⟨functional, representation⟩ := hface.2 hface.1
  let pulled := functional.comp equiv.symm.linear.toLinearMap.toContinuousLinearMap
  have difference (point other : E) :
      pulled (equiv point) - pulled (equiv other) = functional point - functional other := by
    have mapped := congrArg functional
      (equiv.symm.toAffineMap.linear_apply_vsub (equiv point) (equiv other))
    simpa [pulled] using mapped
  refine ⟨hface.1.image equiv, fun _ => ⟨pulled, ?_⟩⟩
  ext imagePoint
  constructor
  · rintro ⟨point, member, rfl⟩
    rw [representation] at member
    refine ⟨⟨point, member.1, rfl⟩, ?_⟩
    rintro _ ⟨other, inBody, rfl⟩
    have bound := member.2 other inBody
    have comparison := difference other point
    linarith
  · rintro ⟨⟨point, inBody, rfl⟩, maximal⟩
    refine ⟨point, ?_, rfl⟩
    rw [representation]
    refine ⟨inBody, fun other member => ?_⟩
    have bound := maximal (equiv other) ⟨other, member, rfl⟩
    have comparison := difference other point
    linarith

theorem isFace_image_affineEquiv_iff (equiv : E ≃ᵃ[ℝ] G) (body face : Set E) :
    IsFace (equiv '' body) (equiv '' face) ↔ IsFace body face := by
  constructor
  · intro hface
    have inverse := hface.image_affineEquiv equiv.symm
    simpa only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply,
      Set.image_id'] using inverse
  · exact fun hface => hface.image_affineEquiv equiv

theorem faces_image_affineEquiv (equiv : E ≃ᵃ[ℝ] G) (body : Set E) (dim : ℕ) :
    faces (equiv '' body) dim = (fun face => equiv '' face) '' faces body dim := by
  ext face
  constructor
  · rintro ⟨hface, dimension⟩
    refine ⟨equiv.symm '' face, ⟨?_, ?_⟩, ?_⟩
    · have inverse := hface.image_affineEquiv equiv.symm
      simpa only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply,
        Set.image_id'] using inverse
    · exact (adim_image_affineEquiv equiv.symm face).trans dimension
    · simp only [Set.image_image, AffineEquiv.apply_symm_apply,
        Set.image_id']
  · rintro ⟨original, ⟨hface, dimension⟩, rfl⟩
    exact ⟨hface.image_affineEquiv equiv, (adim_image_affineEquiv equiv original).trans dimension⟩

theorem fNum_image_affineEquiv (equiv : E ≃ᵃ[ℝ] G) (body : Set E) (dim : ℕ) :
    fNum (equiv '' body) dim = fNum body dim := by
  unfold fNum
  rw [faces_image_affineEquiv]
  exact Set.ncard_image_of_injective _ (Set.image_injective.mpr equiv.injective)

theorem UnimodEquiv.fNum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {body target : Set (ι → ℝ)} (equivalent : UnimodEquiv body target) (dim : ℕ) :
    fNum body dim = fNum target dim := by
  rcases equivalent with ⟨matrix, determinant, shift, rfl⟩
  have determinant_ne : matrix.det ≠ 0 := by
    rcases determinant with positive | negative
    · simp [positive]
    · simp [negative]
  have real_determinant_ne : (matrix.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast determinant_ne
  let linear := LinearEquiv.ofInjectiveEndo (matrix.map (Int.cast : ℤ → ℝ)).mulVecLin
    (Matrix.mulVec_injective_of_det_ne_zero real_determinant_ne)
  let equiv := linear.toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ (ι → ℝ) (fun coord => (shift coord : ℝ)))
  have function_eq : (equiv : (ι → ℝ) → (ι → ℝ)) =
      fun point => (matrix.map (Int.cast : ℤ → ℝ)).mulVec point +
        (fun coord => (shift coord : ℝ)) := by
    funext point
    change (fun coord => (shift coord : ℝ)) +
      (matrix.map (Int.cast : ℤ → ℝ)).mulVec point = _
    exact add_comm _ _
  have counts := fNum_image_affineEquiv equiv body dim
  rw [function_eq] at counts
  exact counts.symm

end HibiLi
