/-
HibiLi/Polytope/SubdivisionTransport.lean — affine-coordinate transport of finite subdivisions.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Subdivision
import HibiLi.Polytope.Affine
import HibiLi.Cited.CJK

namespace HibiLi
namespace SubdivisionTransport

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G]

theorem adim_image (emb : E →ᵃ[ℝ] G) (hinj : Function.Injective emb) (cell : Set E) :
    adim (emb '' cell) = adim cell := by
  unfold adim
  rw [← emb.map_vectorSpan]
  exact (Submodule.equivMapOfInjective emb.linear
    (emb.linear_injective_iff.mpr hinj) (vectorSpan ℝ cell)).finrank_eq.symm

theorem polytope_image (emb : E →ᵃ[ℝ] G) {body : Set E} (hbody : IsPolytope body) :
    IsPolytope (emb '' body) := by
  classical
  obtain ⟨vertices, rfl⟩ := hbody
  refine ⟨vertices.image emb, ?_⟩
  rw [Finset.coe_image]
  exact emb.image_convexHull _

theorem face_image (emb : E →ᵃ[ℝ] G) (retr : G →ᵃ[ℝ] E)
    (hleft : Function.LeftInverse retr emb) {body cell : Set E} (hcell : IsFace body cell) :
    IsFace (emb '' body) (emb '' cell) := by
  obtain ⟨ell, hell⟩ := hcell.2 hcell.1
  let pulled := ell.comp retr.linear.toContinuousLinearMap
  have difference (point other : E) :
      pulled (emb point) - pulled (emb other) = ell point - ell other := by
    have hh := congrArg ell (retr.linear_apply_vsub (emb point) (emb other))
    simpa [pulled, hleft point, hleft other] using hh
  refine ⟨hcell.1.image emb, fun _ => ⟨pulled, ?_⟩⟩
  ext point
  constructor
  · rintro ⟨orig, horig, rfl⟩
    rw [hell] at horig
    refine ⟨⟨orig, horig.1, rfl⟩, ?_⟩
    rintro _ ⟨other, hother, rfl⟩
    have hbound := horig.2 other hother
    have hd := difference other orig
    linarith
  · rintro ⟨⟨orig, horig, rfl⟩, hmax⟩
    refine ⟨orig, ?_, rfl⟩
    rw [hell]
    refine ⟨horig, fun other hother => ?_⟩
    have hb := hmax (emb other) ⟨other, hother, rfl⟩
    have hd := difference other orig
    linarith

theorem face_preimage (emb : E →ᵃ[ℝ] G) (hinj : Function.Injective emb)
    {body : Set E} {cell : Set G} (hcell : IsFace (emb '' body) cell) :
    IsFace body (emb ⁻¹' cell) := by
  obtain ⟨point, hpoint⟩ := hcell.1
  obtain ⟨orig, horig, rfl⟩ := hcell.2.subset hpoint
  obtain ⟨ell, hell⟩ := hcell.2 hcell.1
  let pulled := ell.comp emb.linear.toContinuousLinearMap
  have difference (point other : E) :
      pulled point - pulled other = ell (emb point) - ell (emb other) := by
    have hh := congrArg ell (emb.linear_apply_vsub point other)
    simpa [pulled] using hh
  refine ⟨⟨orig, hpoint⟩, fun _ => ⟨pulled, ?_⟩⟩
  ext point
  change emb point ∈ cell ↔ _
  rw [hell]
  constructor
  · rintro ⟨⟨other, hother, heq⟩, hmax⟩
    have hsame := hinj heq
    subst other
    refine ⟨hother, fun other hother => ?_⟩
    have hb := hmax (emb other) ⟨other, hother, rfl⟩
    have hd := difference other point
    linarith
  · rintro ⟨hpoint, hmax⟩
    refine ⟨⟨point, hpoint, rfl⟩, ?_⟩
    rintro _ ⟨other, hother, rfl⟩
    have hb := hmax other hother
    have hd := difference other point
    linarith

theorem face_image_iff (emb : E →ᵃ[ℝ] G) (retr : G →ᵃ[ℝ] E)
    (hleft : Function.LeftInverse retr emb) (body cell : Set E) :
    IsFace (emb '' body) (emb '' cell) ↔ IsFace body cell := by
  constructor
  · intro hh
    simpa only [Set.preimage_image_eq _ hleft.injective] using face_preimage emb hleft.injective hh
  · exact face_image emb retr hleft

theorem affine_leftInverse (emb : E →ᵃ[ℝ] G) (hinj : Function.Injective emb) :
    ∃ retr : G →ᵃ[ℝ] E, Function.LeftInverse retr emb := by
  obtain ⟨lin, hlin⟩ := emb.linear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (emb.linear_injective_iff.mpr hinj))
  let retr : G →ᵃ[ℝ] E := lin.toAffineMap.comp
    (AffineEquiv.constVAdd ℝ G (-emb 0)).toAffineMap
  refine ⟨retr, fun point => ?_⟩
  have hdiff : -emb 0 + emb point = emb.linear point := by
    have hh := emb.linear_apply_vsub point 0
    simpa [sub_eq_add_neg, add_comm] using hh.symm
  change lin (-emb 0 + emb point) = point
  rw [hdiff]
  exact DFunLike.congr_fun hlin point

noncomputable def imageCells (emb : E →ᵃ[ℝ] G) (cells : Finset (Set E)) : Finset (Set G) := by
  classical
  exact cells.image (fun cell => emb '' cell)

section Coordinates

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def maxCellImage (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (hinj : Function.Injective emb) (cells : Finset (Set (ι → ℝ)))
    (cell : MaxSubdivisionCell cells) : MaxSubdivisionCell (imageCells emb cells) := by
  classical
  refine ⟨emb '' cell.1, Finset.mem_image.mpr ⟨cell.1, cell.2.1, rfl⟩, ?_⟩
  intro other hother hsub
  obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hother
  have hinside : cell.1 ⊆ original := (Set.image_subset_image_iff hinj).mp hsub
  exact congrArg (Set.image emb) (cell.2.2 original horiginal hinside)

theorem maxCellImage_injective (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (hinj : Function.Injective emb) (cells : Finset (Set (ι → ℝ))) :
    Function.Injective (maxCellImage emb hinj cells) := by
  intro first second hsame
  apply Subtype.ext
  apply Set.image_injective.mpr hinj
  exact congrArg Subtype.val hsame

theorem maxCellImage_surjective (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (hinj : Function.Injective emb) (cells : Finset (Set (ι → ℝ))) :
    Function.Surjective (maxCellImage emb hinj cells) := by
  classical
  intro cell
  obtain ⟨original, horiginal, himage⟩ := Finset.mem_image.mp cell.2.1
  have hmax : ∀ other ∈ cells, original ⊆ other → other = original := by
    intro other hother hsub
    have heq := cell.2.2 (emb '' other) (Finset.mem_image.mpr ⟨other, hother, rfl⟩)
      (himage ▸ Set.image_mono hsub)
    exact (Set.image_injective.mpr hinj) (heq.trans himage.symm)
  exact ⟨⟨original, horiginal, hmax⟩, Subtype.ext himage⟩

noncomputable def maxCellImageEquiv (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (hinj : Function.Injective emb) (cells : Finset (Set (ι → ℝ))) :
    MaxSubdivisionCell cells ≃ MaxSubdivisionCell (imageCells emb cells) :=
  Equiv.ofBijective (maxCellImage emb hinj cells)
    ⟨maxCellImage_injective emb hinj cells, maxCellImage_surjective emb hinj cells⟩

noncomputable def dualGraphIso (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (retr : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ)) (hleft : Function.LeftInverse retr emb)
    (cells : Finset (Set (ι → ℝ))) :
    subdivisionDualGraph cells ≃g subdivisionDualGraph (imageCells emb cells) where
  toEquiv := maxCellImageEquiv emb hleft.injective cells
  map_rel_iff' := by
    intro first second
    change (maxCellImage emb hleft.injective cells first ≠ maxCellImage emb hleft.injective cells second ∧
      (emb '' first.1 ∩ emb '' second.1).Nonempty ∧
      IsFace (emb '' first.1) (emb '' first.1 ∩ emb '' second.1) ∧
      IsFace (emb '' second.1) (emb '' first.1 ∩ emb '' second.1) ∧
      adim (emb '' first.1 ∩ emb '' second.1) + 1 = adim (emb '' first.1) ∧
      adim (emb '' first.1 ∩ emb '' second.1) + 1 = adim (emb '' second.1)) ↔ _
    rw [← Set.image_inter hleft.injective]
    simp only [(maxCellImage_injective emb hleft.injective cells).ne_iff, Set.image_nonempty,
      face_image_iff emb retr hleft, adim_image emb hleft.injective]
    rfl

theorem image_retract (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (retr : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ)) (hleft : Function.LeftInverse retr emb)
    (body : Set (ι → ℝ)) : retr '' (emb '' body) = body := by
  ext point
  constructor
  · rintro ⟨_, ⟨orig, horig, rfl⟩, rfl⟩
    simpa only [hleft orig] using horig
  · intro hpoint
    exact ⟨emb point, ⟨point, hpoint, rfl⟩, hleft point⟩

theorem sUnion_imageCells (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (cells : Finset (Set (ι → ℝ))) :
    ⋃₀ (imageCells emb cells : Set (Set (κ → ℝ))) = emb '' ⋃₀ (cells : Set (Set (ι → ℝ))) := by
  classical
  ext point
  constructor
  · rintro ⟨cell, hcell, hpoint⟩
    obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
    obtain ⟨orig, horig, rfl⟩ := hpoint
    exact ⟨orig, ⟨original, horiginal, horig⟩, rfl⟩
  · rintro ⟨orig, ⟨cell, hcell, horig⟩, rfl⟩
    exact ⟨emb '' cell, Finset.mem_image.mpr ⟨cell, hcell, rfl⟩, ⟨orig, horig, rfl⟩⟩

theorem subdivision_image_iff (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (retr : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ)) (hleft : Function.LeftInverse retr emb)
    (base : Set (ι → ℝ)) (cells : Finset (Set (ι → ℝ))) :
    IsFinitePolytopalSubdivision (emb '' base) (imageCells emb cells) ↔
      IsFinitePolytopalSubdivision base cells := by
  classical
  constructor
  · intro hh
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro cell hcell
      have hp := hh.1 (emb '' cell) (Finset.mem_image.mpr ⟨cell, hcell, rfl⟩)
      have hpoly := polytope_image retr hp.1
      rw [image_retract emb retr hleft] at hpoly
      exact ⟨hpoly, Set.image_nonempty.mp hp.2⟩
    · apply Set.image_injective.mpr hleft.injective
      have hcover := hh.2.1
      rwa [sUnion_imageCells] at hcover
    · intro cell hcell face hface
      have hmem := hh.2.2.1 (emb '' cell) (Finset.mem_image.mpr ⟨cell, hcell, rfl⟩)
        (emb '' face) (face_image emb retr hleft hface)
      obtain ⟨original, horiginal, heq⟩ := Finset.mem_image.mp hmem
      have hsame := Set.image_injective.mpr hleft.injective heq
      simpa only [hsame] using horiginal
    · intro left hleftCell right hrightCell hn
      have himage : emb '' left ∩ emb '' right = emb '' (left ∩ right) :=
        (Set.image_inter hleft.injective).symm
      have hp := hh.2.2.2 (emb '' left) (Finset.mem_image.mpr ⟨left, hleftCell, rfl⟩)
        (emb '' right) (Finset.mem_image.mpr ⟨right, hrightCell, rfl⟩)
        (himage ▸ hn.image emb)
      rw [himage] at hp
      exact ⟨(face_image_iff emb retr hleft _ _).mp hp.1,
        (face_image_iff emb retr hleft _ _).mp hp.2⟩
  · intro hh
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro cell hcell
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      exact ⟨polytope_image emb (hh.1 original horiginal).1, (hh.1 original horiginal).2.image emb⟩
    · rw [sUnion_imageCells, hh.2.1]
    · intro cell hcell face hface
      obtain ⟨original, horiginal, rfl⟩ := Finset.mem_image.mp hcell
      have hp := face_preimage emb hleft.injective hface
      have hmember := hh.2.2.1 original horiginal (emb ⁻¹' face) hp
      refine Finset.mem_image.mpr ⟨emb ⁻¹' face, hmember, ?_⟩
      rw [Set.image_preimage_eq_inter_range]
      exact Set.inter_eq_left.mpr (hface.2.subset.trans (Set.image_subset_range _ _))
    · intro left hleftCell right hrightCell hn
      obtain ⟨originalLeft, hOriginalLeft, rfl⟩ := Finset.mem_image.mp hleftCell
      obtain ⟨originalRight, hOriginalRight, rfl⟩ := Finset.mem_image.mp hrightCell
      rw [← Set.image_inter hleft.injective] at hn ⊢
      have hp := hh.2.2.2 originalLeft hOriginalLeft originalRight hOriginalRight
        (Set.image_nonempty.mp hn)
      exact ⟨face_image emb retr hleft hp.1, face_image emb retr hleft hp.2⟩

theorem image_embedding_retract (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (retr : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ)) (hleft : Function.LeftInverse retr emb)
    {body : Set (κ → ℝ)} (hbody : body ⊆ Set.range emb) : emb '' (retr '' body) = body := by
  have hright (point : κ → ℝ) (hp : point ∈ body) : emb (retr point) = point := by
    obtain ⟨orig, rfl⟩ := hbody hp
    rw [hleft orig]
  ext point
  constructor
  · rintro ⟨_, ⟨orig, horig, rfl⟩, rfl⟩
    simpa only [hright orig horig] using horig
  · intro hp
    exact ⟨retr point, ⟨point, hp, rfl⟩, hright point hp⟩

theorem imageCells_embedding_retract (emb : (ι → ℝ) →ᵃ[ℝ] (κ → ℝ))
    (retr : (κ → ℝ) →ᵃ[ℝ] (ι → ℝ)) (hleft : Function.LeftInverse retr emb)
    (cells : Finset (Set (κ → ℝ))) (hinside : ∀ cell ∈ cells, cell ⊆ Set.range emb) :
    imageCells emb (imageCells retr cells) = cells := by
  classical
  unfold imageCells
  rw [Finset.image_image]
  have hh : cells.image (fun cell => emb '' (retr '' cell)) = cells.image id := by
    apply Finset.image_congr
    intro cell hcell
    exact image_embedding_retract emb retr hleft (hinside cell hcell)
  simpa only [Finset.image_id, Function.comp_def] using hh

theorem fullSpan_coordinates (base : Set (ι → ℝ)) (hn : base.Nonempty) :
    ∃ (dimension : ℕ) (emb : (Fin dimension → ℝ) →ᵃ[ℝ] (ι → ℝ))
      (retr : (ι → ℝ) →ᵃ[ℝ] (Fin dimension → ℝ)),
      Function.LeftInverse retr emb ∧ base ⊆ Set.range emb ∧
      affineSpan ℝ (retr '' base) = ⊤ := by
  classical
  obtain ⟨origin, horigin⟩ := hn
  let space := affineSpan ℝ base
  let origin' : space := ⟨origin, subset_affineSpan ℝ base horigin⟩
  letI : Nonempty space := ⟨origin'⟩
  let basis := Module.finBasis ℝ space.direction
  let chart : space ≃ᵃ[ℝ] (Fin (Module.finrank ℝ space.direction) → ℝ) :=
    (AffineEquiv.constVSub ℝ origin').trans basis.equivFun.toAffineEquiv
  let emb : (Fin (Module.finrank ℝ space.direction) → ℝ) →ᵃ[ℝ] (ι → ℝ) :=
    space.subtype.comp chart.symm.toAffineMap
  have hinj : Function.Injective emb := by
    intro first second hsame
    apply chart.symm.injective
    exact Subtype.ext hsame
  obtain ⟨retr, hleft⟩ := affine_leftInverse emb hinj
  have hrange : Set.range emb = (space : Set (ι → ℝ)) := by
    ext point
    constructor
    · rintro ⟨coord, rfl⟩
      exact (chart.symm coord).2
    · intro hp
      refine ⟨chart ⟨point, hp⟩, ?_⟩
      simp [emb]
  refine ⟨Module.finrank ℝ space.direction, emb, retr, hleft, ?_, ?_⟩
  · rw [hrange]
    exact subset_affineSpan ℝ base
  · have htop : space.map retr = ⊤ := by
      apply top_unique
      intro coord _
      change coord ∈ retr '' (space : Set (ι → ℝ))
      exact ⟨emb coord, (chart.symm coord).2, hleft coord⟩
    simpa only [space, AffineSubspace.map_span] using htop

end Coordinates
end SubdivisionTransport

theorem subdivisionDualGraph_connected {ι : Type*} [Fintype ι]
    (base : Set (ι → ℝ)) (cells : Finset (Set (ι → ℝ)))
    (hbase : IsPolytope base) (hn : base.Nonempty)
    (hsub : IsFinitePolytopalSubdivision base cells) :
    (subdivisionDualGraph cells).Connected := by
  classical
  obtain ⟨dimension, emb, retr, hleft, hinside, hspan⟩ :=
    SubdivisionTransport.fullSpan_coordinates base hn
  have hcellInside : ∀ cell ∈ cells, cell ⊆ Set.range emb := by
    intro cell hcell point hp
    apply hinside
    rw [← hsub.2.1]
    exact ⟨cell, hcell, hp⟩
  have hbodyEq := SubdivisionTransport.image_embedding_retract emb retr hleft hinside
  have hcellsEq := SubdivisionTransport.imageCells_embedding_retract emb retr hleft cells hcellInside
  have hsubCoord : IsFinitePolytopalSubdivision (retr '' base)
      (SubdivisionTransport.imageCells retr cells) := by
    apply (SubdivisionTransport.subdivision_image_iff emb retr hleft _ _).mp
    simpa only [hbodyEq, hcellsEq] using hsub
  have hconnected := Cited.cjk_dual_connected (retr '' base)
    (SubdivisionTransport.imageCells retr cells) (SubdivisionTransport.polytope_image retr hbase)
    (hn.image retr) hspan hsubCoord
  have htransport := (SubdivisionTransport.dualGraphIso emb retr hleft
    (SubdivisionTransport.imageCells retr cells)).connected_iff.mp hconnected
  rw [hcellsEq] at htransport
  exact htransport

end HibiLi
