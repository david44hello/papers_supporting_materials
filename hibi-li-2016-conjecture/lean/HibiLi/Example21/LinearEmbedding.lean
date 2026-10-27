/-
HibiLi/Example21/LinearEmbedding.lean — geometric faces under linear embeddings with a retraction.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Polytope.Affine
import HibiLi.Proofs.FacePoly

namespace HibiLi

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem adim_image_linear_injective (emb : E →L[ℝ] G) (hinj : Function.Injective emb)
    (face : Set E) : adim (emb '' face) = adim face := by
  unfold adim
  change Module.finrank ℝ (vectorSpan ℝ (emb.toLinearMap.toAffineMap '' face)) = _
  rw [← emb.toLinearMap.toAffineMap.map_vectorSpan]
  exact (Submodule.equivMapOfInjective emb.toLinearMap hinj (vectorSpan ℝ face)).finrank_eq.symm

theorem IsFace.image_linear_retract {body face : Set E} (hface : IsFace body face)
    (emb : E →L[ℝ] G) (retr : G →L[ℝ] E) (hleft : Function.LeftInverse retr emb) :
    IsFace (emb '' body) (emb '' face) := by
  obtain ⟨ell, hell⟩ := hface.2 hface.1
  refine ⟨hface.1.image emb, fun _ => ⟨ell.comp retr, ?_⟩⟩
  ext point
  constructor
  · rintro ⟨orig, horig, rfl⟩
    rw [hell] at horig
    refine ⟨⟨orig, horig.1, rfl⟩, ?_⟩
    rintro _ ⟨other, hother, rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, hleft other, hleft orig] using horig.2 other hother
  · rintro ⟨⟨orig, horig, rfl⟩, hmax⟩
    refine ⟨orig, ?_, rfl⟩
    rw [hell]
    refine ⟨horig, fun other hother => ?_⟩
    simpa only [ContinuousLinearMap.comp_apply, hleft other, hleft orig] using
      hmax (emb other) ⟨other, hother, rfl⟩

theorem IsFace.preimage_linear_injective (emb : E →L[ℝ] G) (hinj : Function.Injective emb)
    {body : Set E} {face : Set G} (hface : IsFace (emb '' body) face) :
    IsFace body (emb ⁻¹' face) := by
  obtain ⟨point, hpoint⟩ := hface.1
  obtain ⟨orig, horig, rfl⟩ := hface.2.subset hpoint
  obtain ⟨ell, hell⟩ := hface.2 hface.1
  refine ⟨⟨orig, hpoint⟩, fun _ => ⟨ell.comp emb, ?_⟩⟩
  ext point
  change emb point ∈ face ↔ _
  rw [hell]
  constructor
  · rintro ⟨⟨other, hother, heq⟩, hmax⟩
    have hsame := hinj heq
    subst other
    exact ⟨hother, fun other hother => hmax (emb other) ⟨other, hother, rfl⟩⟩
  · rintro ⟨hpoint, hmax⟩
    refine ⟨⟨point, hpoint, rfl⟩, ?_⟩
    rintro _ ⟨other, hother, rfl⟩
    exact hmax other hother

theorem faces_image_linear_retract (emb : E →L[ℝ] G) (retr : G →L[ℝ] E)
    (hleft : Function.LeftInverse retr emb) (body : Set E) (dim : ℕ) :
    faces (emb '' body) dim = (fun face => emb '' face) '' faces body dim := by
  ext face
  constructor
  · rintro ⟨hface, hdim⟩
    have himage : emb '' (emb ⁻¹' face) = face := by
      rw [Set.image_preimage_eq_inter_range]
      exact Set.inter_eq_left.mpr (hface.2.subset.trans (Set.image_subset_range _ _))
    refine ⟨emb ⁻¹' face, ⟨hface.preimage_linear_injective emb hleft.injective, ?_⟩, himage⟩
    rw [← adim_image_linear_injective emb hleft.injective, himage]
    exact hdim
  · rintro ⟨original, ⟨hface, hdim⟩, rfl⟩
    exact ⟨hface.image_linear_retract emb retr hleft,
      (adim_image_linear_injective emb hleft.injective original).trans hdim⟩

theorem fNum_image_linear_retract (emb : E →L[ℝ] G) (retr : G →L[ℝ] E)
    (hleft : Function.LeftInverse retr emb) (body : Set E) (dim : ℕ) :
    fNum (emb '' body) dim = fNum body dim := by
  rw [fNum, faces_image_linear_retract emb retr hleft]
  exact Set.ncard_image_of_injective _ (Set.image_injective.mpr hleft.injective)

theorem facePoly_image_linear_retract {ι κ : Type*} [Fintype ι] [Fintype κ]
    (emb : (ι → ℝ) →L[ℝ] (κ → ℝ)) (retr : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (hleft : Function.LeftInverse retr emb) (body : Set (ι → ℝ)) :
    facePoly (emb '' body) = facePoly body := by
  ext dim
  simp only [Proofs.facePoly_coeff, fNum_image_linear_retract emb retr hleft]

end HibiLi
