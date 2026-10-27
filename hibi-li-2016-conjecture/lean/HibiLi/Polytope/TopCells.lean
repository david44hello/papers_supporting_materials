/-
HibiLiLean — restrictions and full-dimensional cells with a prescribed carrier.
-/
import HibiLi.Polytope.CarrierCounts

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsFace.inter_subset {body face inside : Set E} (hface : IsFace body face)
    (subset : inside ⊆ body) (nonempty : (inside ∩ face).Nonempty) : IsFace inside (inside ∩ face) := by
  obtain ⟨base, base_inside, base_face⟩ := nonempty
  obtain ⟨functional, representation⟩ := hface.2 hface.1
  have base_max := base_face
  rw [representation] at base_max
  refine ⟨⟨base, base_inside, base_face⟩, fun _ => ⟨functional, ?_⟩⟩
  ext point
  constructor
  · rintro ⟨member, face_member⟩
    rw [representation] at face_member
    exact ⟨member, fun other other_member => face_member.2 other (subset other_member)⟩
  · rintro ⟨member, maximal⟩
    refine ⟨member, ?_⟩
    rw [representation]
    exact ⟨subset member, fun other inBody => (base_max.2 other inBody).trans (maximal base base_inside)⟩

theorem IsFace.eq_of_adim_eq {body face : Set E} (hface : IsFace body face)
    (dimension : adim face = adim body) : face = body := by
  have direction_eq : vectorSpan ℝ face = vectorSpan ℝ body :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hface.subset) dimension
  have span_eq : affineSpan ℝ face = affineSpan ℝ body :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le
      (by simpa only [direction_affineSpan] using direction_eq)
      (hface.1.mono (subset_affineSpan ℝ face)) (affineSpan_mono ℝ hface.subset)
  rw [hface.eq_inter_affineSpan, span_eq]
  exact Set.inter_eq_left.mpr (subset_affineSpan ℝ body)

theorem isCarrier_of_subset_of_adim_eq {body face cell : Set E} (hface : IsFace body face)
    (nonempty : cell.Nonempty) (inside : cell ⊆ face) (dimension : adim cell = adim face) :
    IsCarrier body face cell := by
  refine ⟨hface, inside, ?_⟩
  intro other hother contains
  have in_inter : cell ⊆ face ∩ other := fun _ member => ⟨inside member, contains member⟩
  have inter_face : IsFace face (face ∩ other) := hother.inter_subset hface.subset (nonempty.mono in_inter)
  have lower : adim cell ≤ adim (face ∩ other) := Submodule.finrank_mono (vectorSpan_mono ℝ in_inter)
  have upper : adim (face ∩ other) ≤ adim face :=
    Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
  have same : face ∩ other = face := inter_face.eq_of_adim_eq (by omega)
  exact Set.inter_eq_left.mp same

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem restrict_cellsS_subset {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    switch.restrict switch.cellsS face ⊆ switch.cellsS := by
  rintro cell ⟨nonempty, original, ⟨branch, valid, full, horiginal⟩, rfl⟩
  refine ⟨branch, valid, full, ?_⟩
  have domain_subset : switch.domL branch ⊆ switch.B := fun _ member => member.1
  have common_nonempty : (switch.domL branch ∩ face).Nonempty := by
    obtain ⟨point, original_member, face_member⟩ := nonempty
    exact ⟨point, horiginal.subset original_member, face_member⟩
  have domain_face := hface.inter_subset domain_subset common_nonempty
  have combined := horiginal.inter domain_face
    (nonempty.mono fun _ member => ⟨member.1, horiginal.subset member.1, member.2⟩)
  have same : original ∩ (switch.domL branch ∩ face) = original ∩ face := by
    ext point
    constructor
    · exact fun member => ⟨member.1, member.2.2⟩
    · exact fun member => ⟨member.1, horiginal.subset member.1, member.2⟩
  simpa only [same] using combined

theorem restrict_cellsT_subset {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    switch.restrict switch.cellsT face ⊆ switch.cellsT := by
  rintro cell ⟨nonempty, original, ⟨branch, valid, full, horiginal⟩, rfl⟩
  refine ⟨branch, valid, full, ?_⟩
  have domain_subset : switch.domU branch ⊆ switch.B := fun _ member => member.1
  have common_nonempty : (switch.domU branch ∩ face).Nonempty := by
    obtain ⟨point, original_member, face_member⟩ := nonempty
    exact ⟨point, horiginal.subset original_member, face_member⟩
  have domain_face := hface.inter_subset domain_subset common_nonempty
  have combined := horiginal.inter domain_face
    (nonempty.mono fun _ member => ⟨member.1, horiginal.subset member.1, member.2⟩)
  have same : original ∩ (switch.domU branch ∩ face) = original ∩ face := by
    ext point
    constructor
    · exact fun member => ⟨member.1, member.2.2⟩
    · exact fun member => ⟨member.1, horiginal.subset member.1, member.2⟩
  simpa only [same] using combined

theorem restrict_cellsR_subset {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    switch.restrict switch.cellsR face ⊆ switch.cellsR := by
  rintro cell ⟨nonempty, original, ⟨_, left, hleft, right, hright, rfl⟩, rfl⟩
  have left_nonempty : (left ∩ face).Nonempty := nonempty.mono fun _ member => ⟨member.1.1, member.2⟩
  have right_nonempty : (right ∩ face).Nonempty := nonempty.mono fun _ member => ⟨member.1.2, member.2⟩
  refine ⟨nonempty, left ∩ face, switch.restrict_cellsS_subset hface ⟨left_nonempty, left, hleft, rfl⟩,
    right ∩ face, switch.restrict_cellsT_subset hface ⟨right_nonempty, right, hright, rfl⟩, ?_⟩
  ext point
  simp only [Set.mem_inter_iff]
  tauto

theorem topCells_eq_carried {family : Set (Set (switch.P' → ℝ))} {face : Set (switch.P' → ℝ)}
    (hface : IsFace switch.B face) (closed : switch.restrict family face ⊆ family)
    (nonempty_cells : ∀ cell ∈ family, cell.Nonempty) :
    switch.topCells family face = {cell | cell ∈ family ∧ adim cell = adim face ∧ IsCarrier switch.B face cell} := by
  ext cell
  constructor
  · rintro ⟨restricted, dimension⟩
    have nonempty := restricted.1
    have inside : cell ⊆ face := by
      obtain ⟨_, original, _, rfl⟩ := restricted
      exact Set.inter_subset_right
    exact ⟨closed restricted, dimension, isCarrier_of_subset_of_adim_eq hface nonempty inside dimension⟩
  · rintro ⟨member, dimension, carrier⟩
    have nonempty := nonempty_cells cell member
    exact ⟨⟨nonempty, cell, member, (Set.inter_eq_left.mpr carrier.2.1).symm⟩, dimension⟩

theorem topCellsS_eq_carried {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    switch.topCells switch.cellsS face =
      {cell | cell ∈ switch.cellsS ∧ adim cell = adim face ∧ IsCarrier switch.B face cell} :=
  switch.topCells_eq_carried hface (switch.restrict_cellsS_subset hface)
    (fun _ member => (switch.cellsS_properties member).1)

theorem topCellsT_eq_carried {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    switch.topCells switch.cellsT face =
      {cell | cell ∈ switch.cellsT ∧ adim cell = adim face ∧ IsCarrier switch.B face cell} :=
  switch.topCells_eq_carried hface (switch.restrict_cellsT_subset hface)
    (fun _ member => (switch.cellsT_properties member).1)

theorem topCellsR_eq_carried {face : Set (switch.P' → ℝ)} (hface : IsFace switch.B face) :
    switch.topCells switch.cellsR face =
      {cell | cell ∈ switch.cellsR ∧ adim cell = adim face ∧ IsCarrier switch.B face cell} :=
  switch.topCells_eq_carried hface (switch.restrict_cellsR_subset hface)
    (fun _ member => (switch.cellsR_properties member).1)

end Switch
end HibiLi
