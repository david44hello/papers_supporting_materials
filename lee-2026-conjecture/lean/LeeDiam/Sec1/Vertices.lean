/-
Vertex descriptions, complementary coordinates, and vertex counts.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs

namespace LeeDiam

variable {P : Type} [Fintype P] [PartialOrder P]

theorem sec1_order_vertices_proved (P : Type) [Fintype P] [PartialOrder P] (v : P → ℝ) :
    HibiLi.IsFace (orderPolytope P) {v} ↔ ∃ I : Set P, IsIdeal I ∧ v = HibiLi.setVector I :=
  order_vertex_iff_ideal v

theorem sec1_chain_vertices_proved (P : Type) [Fintype P] [PartialOrder P] (v : P → ℝ) :
    HibiLi.IsFace (chainPolytope P) {v} ↔ ∃ A : Set P, IsAntichainSet A ∧ v = HibiLi.setVector A :=
  chain_vertex_iff_antichain v

omit [PartialOrder P] in
theorem face_image_affine {body face : Set (P → ℝ)} (hface : HibiLi.IsFace body face)
    (equiv : (P → ℝ) ≃ᵃ[ℝ] (P → ℝ)) : HibiLi.IsFace (equiv '' body) (equiv '' face) := by
  obtain ⟨functional, representation⟩ := hface.2 hface.1
  let pulled := functional.comp equiv.symm.linear.toLinearMap.toContinuousLinearMap
  have difference (point other : P → ℝ) :
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

omit [PartialOrder P] in
theorem face_image_affine_iff (equiv : (P → ℝ) ≃ᵃ[ℝ] (P → ℝ))
    (body face : Set (P → ℝ)) :
    HibiLi.IsFace (equiv '' body) (equiv '' face) ↔ HibiLi.IsFace body face := by
  constructor
  · intro hface
    have inverse := face_image_affine hface equiv.symm
    simpa only [Set.image_image, Function.comp_def, AffineEquiv.symm_apply_apply,
      Set.image_id'] using inverse
  · exact fun hface => face_image_affine hface equiv

noncomputable def polyGraph_affineIso (body : Set (P → ℝ))
    (equiv : (P → ℝ) ≃ᵃ[ℝ] (P → ℝ)) : polyGraph body ≃g polyGraph (equiv '' body) := by
  let vertices : {v : P → ℝ // HibiLi.IsFace body {v}} ≃
      {v : P → ℝ // HibiLi.IsFace (equiv '' body) {v}} := {
    toFun := fun vertex => ⟨equiv vertex.1, by
      simpa only [Set.image_singleton] using face_image_affine vertex.2 equiv⟩
    invFun := fun vertex => ⟨equiv.symm vertex.1, by
      have pulled := face_image_affine vertex.2 equiv.symm
      simpa only [Set.image_singleton, Set.image_image, Function.comp_def,
        AffineEquiv.symm_apply_apply, Set.image_id'] using pulled⟩
    left_inv := fun vertex => Subtype.ext (equiv.symm_apply_apply vertex.1)
    right_inv := fun vertex => Subtype.ext (equiv.apply_symm_apply vertex.1) }
  refine { toEquiv := vertices, map_rel_iff' := ?_ }
  intro left right
  change (vertices left ≠ vertices right ∧
      HibiLi.IsFace (equiv '' body) (segment ℝ (equiv left.1) (equiv right.1))) ↔
    (left ≠ right ∧ HibiLi.IsFace body (segment ℝ left.1 right.1))
  have segment_image : equiv '' segment ℝ left.1 right.1 =
      segment ℝ (equiv left.1) (equiv right.1) :=
    image_segment ℝ equiv.toAffineMap left.1 right.1
  rw [← segment_image, face_image_affine_iff]
  exact and_congr (not_congr vertices.injective.eq_iff) Iff.rfl

noncomputable def complementaryCoordinates : (P → ℝ) ≃ᵃ[ℝ] (P → ℝ) :=
  (LinearEquiv.neg ℝ).toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (P → ℝ) 1)

omit [Fintype P] [PartialOrder P] in
@[simp] theorem complementaryCoordinates_apply (point : P → ℝ) :
    complementaryCoordinates point = 1 - point := by
  change 1 + -point = 1 - point
  exact (sub_eq_add_neg _ _).symm

omit [Fintype P] in
theorem complementary_order_image :
    orderPolytope P = (fun point : P → ℝ => 1 - point) '' HibiLi.orderPolytope P := by
  ext point
  constructor
  · intro member
    refine ⟨1 - point, ⟨?_, ?_⟩, ?_⟩
    · intro coord
      change 0 ≤ 1 - point coord ∧ 1 - point coord ≤ 1
      constructor <;> linarith [(member.1 coord).1, (member.1 coord).2]
    · intro lower upper relation
      change 1 - point lower ≤ 1 - point upper
      linarith [member.2 lower upper relation]
    · ext coord
      simp
  · rintro ⟨original, member, rfl⟩
    refine ⟨?_, ?_⟩
    · intro coord
      change 0 ≤ 1 - original coord ∧ 1 - original coord ≤ 1
      constructor <;> linarith [(member.1 coord).1, (member.1 coord).2]
    · intro lower upper relation
      change 1 - original upper ≤ 1 - original lower
      linarith [member.2 lower upper relation]

theorem sec1_footnote_stanley_proved (P : Type) [Fintype P] [PartialOrder P] :
    orderPolytope P = (fun x => 1 - x) '' HibiLi.orderPolytope P ∧
      Nonempty (polyGraph (HibiLi.orderPolytope P) ≃g polyGraph (orderPolytope P)) := by
  refine ⟨complementary_order_image, ?_⟩
  have same : complementaryCoordinates '' HibiLi.orderPolytope P = orderPolytope P := by
    have function_eq : (complementaryCoordinates : (P → ℝ) → (P → ℝ)) =
        fun point => 1 - point := funext complementaryCoordinates_apply
    rw [function_eq]
    exact complementary_order_image.symm
  exact ⟨same ▸ polyGraph_affineIso (HibiLi.orderPolytope P) complementaryCoordinates⟩

theorem sec1_same_vertices_proved (P : Type) [Fintype P] [PartialOrder P] :
    Nat.card {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} =
      Nat.card {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} := by
  let ideals : {I : Set P // IsIdeal I} ≃
      {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} := Equiv.ofBijective
    (fun ideal => oVtx ideal.1 ideal.2) (by
      constructor
      · intro left right same
        exact Subtype.ext (indicator_injective (congrArg Subtype.val same))
      · intro vertex
        obtain ⟨ideal, valid, same⟩ := (order_vertex_iff_ideal vertex.1).mp vertex.2
        exact ⟨⟨ideal, valid⟩, Subtype.ext same.symm⟩)
  let antichains : {A : Set P // IsAntichainSet A} ≃
      {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} := Equiv.ofBijective
    (fun antichain => cVtx antichain.1 antichain.2) (by
      constructor
      · intro left right same
        exact Subtype.ext (indicator_injective (congrArg Subtype.val same))
      · intro vertex
        obtain ⟨antichain, valid, same⟩ := (chain_vertex_iff_antichain vertex.1).mp vertex.2
        exact ⟨⟨antichain, valid⟩, Subtype.ext same.symm⟩)
  let complement : {I : Set P // IsIdeal I} ≃ {U : Set P // IsUpperSet U} := {
    toFun := fun ideal => ⟨ideal.1ᶜ, ideal.2.compl⟩
    invFun := fun upper => ⟨upper.1ᶜ, upper.2.compl⟩
    left_inv := fun _ => Subtype.ext (compl_compl _)
    right_inv := fun _ => Subtype.ext (compl_compl _) }
  exact Nat.card_congr (ideals.symm.trans
    (complement.trans (HibiLi.upperAntichainEquiv.trans antichains)))

end LeeDiam

