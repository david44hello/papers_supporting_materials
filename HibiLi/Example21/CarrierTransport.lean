/-
HibiLi — affine coordinate transport of carriers and their counts.
-/
import HibiLi.Polytope.Affine
import HibiLi.Polytope.Faces

namespace HibiLi.Example21

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

theorem carrier_image_affineEquiv {body face cell : Set E} (carrier : IsCarrier body face cell)
    (equiv : E ≃ᵃ[ℝ] G) : IsCarrier (equiv '' body) (equiv '' face) (equiv '' cell) := by
  refine ⟨carrier.1.image_affineEquiv equiv, Set.image_mono carrier.2.1, ?_⟩
  intro other otherFace contains
  have preFace := otherFace.image_affineEquiv equiv.symm
  simp only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply, Set.image_id'] at preFace
  have preContains : cell ⊆ equiv.symm '' other := by
    intro point member
    exact ⟨equiv point, contains ⟨point, member, rfl⟩, equiv.symm_apply_apply point⟩
  have minimal := carrier.2.2 _ preFace preContains
  rintro _ ⟨point, member, rfl⟩
  obtain ⟨otherPoint, hm, same⟩ := minimal member
  simpa only [← same, AffineEquiv.apply_symm_apply] using hm

theorem carrier_image_affineEquiv_iff (equiv : E ≃ᵃ[ℝ] G) (body face cell : Set E) :
    IsCarrier (equiv '' body) (equiv '' face) (equiv '' cell) ↔ IsCarrier body face cell := by
  constructor
  · intro carrier
    have inverse := carrier_image_affineEquiv carrier equiv.symm
    simpa only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply, Set.image_id'] using inverse
  · exact fun carrier => carrier_image_affineEquiv carrier equiv

noncomputable def carriedCount (body : Set E) (family : Set (Set E)) (face : Set E) (dim : ℕ) : ℕ :=
  {cell | cell ∈ family ∧ adim cell = dim ∧ IsCarrier body face cell}.ncard

theorem carriedCount_image_affineEquiv (equiv : E ≃ᵃ[ℝ] G)
    (body : Set E) (family : Set (Set E)) (face : Set E) (dim : ℕ) :
    carriedCount (equiv '' body) ((fun cell => equiv '' cell) '' family) (equiv '' face) dim =
      carriedCount body family face dim := by
  have equal : {cell | cell ∈ (fun cell => equiv '' cell) '' family ∧ adim cell = dim ∧
      IsCarrier (equiv '' body) (equiv '' face) cell} =
      (fun cell => equiv '' cell) '' {cell | cell ∈ family ∧ adim cell = dim ∧ IsCarrier body face cell} := by
    ext cell
    constructor
    · rintro ⟨⟨original, member, rfl⟩, dimension, carrier⟩
      rw [adim_image_affineEquiv] at dimension
      exact ⟨original, ⟨member, dimension, (carrier_image_affineEquiv_iff equiv body face original).mp carrier⟩, rfl⟩
    · rintro ⟨original, ⟨member, dimension, carrier⟩, rfl⟩
      exact ⟨⟨original, member, rfl⟩, (adim_image_affineEquiv equiv original).trans dimension,
        carrier_image_affineEquiv carrier equiv⟩
  unfold carriedCount
  rw [equal]
  exact Set.ncard_image_of_injective _ (Set.image_injective.mpr equiv.injective)

end HibiLi.Example21
