/-
HibiLi/Proofs/AffineFace.lean — Proposition 5.1's general step: if L (or U) is affine on a face E of B, then S|_E (or T|_E) is the faces
of E, R|_E = T|_E (or S|_E) and delta_E = 0 (paper v2.10 lines 913-921; helpers; the row sec5_affine_face is in
Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs
import HibiLi.Cited.Fourier
import HibiLi.Cited.Others
import HibiLi.Polytope.Connectivity
import HibiLi.Proofs.OrderTheory
import HibiLi.Proofs.FacePoly
import HibiLi.Proofs.Summation
import HibiLi.Proofs.SwitchFacts
import HibiLi.Proofs.LU
import HibiLi.Proofs.Prop31
import HibiLi.Polytope.Pyramid
import HibiLi.Example21.Result
import HibiLi.Proofs.Lemma44
import HibiLi.Proofs.LUPiecewise
import HibiLi.Example21.Triangles
import HibiLi.Proofs.Lemma48
import HibiLi.Proofs.Lemma45
import HibiLi.Polytope.CarrierInterior
import HibiLi.Polytope.CarrierSum
import HibiLi.Example21.ZeroOneResult
import HibiLi.Proofs.Lemma36
import HibiLi.Example21.VertexBijection
import HibiLi.Polytope.Dimension
import HibiLi.Polytope.Conventions
import HibiLi.Polytope.Unimodular
import HibiLi.Polytope.Affine
import HibiLi.Polytope.Endpoints
import HibiLi.Polytope.DeltaNonnegative
import HibiLi.Proofs.Lemma46
import HibiLi.Example21.SharpFamily
import HibiLi.Proofs.Lemma42
import HibiLi.Defs.ExtraDefs
import HibiLi.Proofs.SmallClaims
import HibiLi.Proofs.PyramidFacesIff
import HibiLi.Proofs.Chain2Example
import HibiLi.Proofs.Lemma45Full
import HibiLi.Example21.OtherSwitches
import HibiLi.Example21.CenterResult
import HibiLi.Proofs.V060Claims
import HibiLi.Polytope.RelintPartition
import HibiLi.Proofs.R3Small
import HibiLi.Proofs.QEPaper
import HibiLi.Proofs.SPaperDefFull
import HibiLi.Census.Result
import HibiLi.Polytope.AffinityComplex
import HibiLi.Polytope.TopCells
import HibiLi.Polytope.Transitivity
import HibiLi.Polytope.Faces

namespace HibiLi

namespace B3

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

theorem cellsS_subset_B {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS) : C ⊆ s.B := by
  obtain ⟨K, _, _, hK⟩ := hC
  exact hK.subset.trans fun _ hu => hu.1

theorem cellsT_subset_B {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsT) : C ⊆ s.B := by
  obtain ⟨j, _, _, hj⟩ := hC
  exact hj.subset.trans fun _ hu => hu.1

theorem cellsS_nonempty {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS) : C.Nonempty := by
  obtain ⟨K, _, _, hK⟩ := hC
  exact hK.1

theorem cellsT_nonempty {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsT) : C.Nonempty := by
  obtain ⟨j, _, _, hj⟩ := hC
  exact hj.1

theorem face_convex {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) : Convex ℝ E :=
  hE.2.convex s.B_isPolytope.convex

theorem isCarrier_self {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) : IsCarrier s.B E E :=
  ⟨hE, subset_rfl, fun _ _ h => h⟩

/-! ### `L` affine on `E` -/

/-- (1) If `L` is affine on the face `E`, then `E` is a cell of `S`. -/
theorem mem_cellsS_of_affineOn {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hL : AffineOn s.L E) : E ∈ s.cellsS := by
  obtain ⟨C, hC, hEC⟩ := (Proofs.lemma_3_6_cover_proved s E hE E subset_rfl (face_convex s hE) rfl).1 hL
  have hCE : C ⊆ E := by
    obtain ⟨⟨_, A, _, rfl⟩, _⟩ := hC
    exact Set.inter_subset_right
  have hCeq : C = E := hCE.antisymm hEC
  rw [← hCeq]
  exact s.restrict_cellsS_subset hE hC.1

/-- (2) `S|_E` is the set of faces of `E` when `E` is a cell of `S`. -/
theorem restrict_cellsS_eq_faces {E : Set (s.P' → ℝ)} (hES : E ∈ s.cellsS) :
    s.restrict s.cellsS E = {C | IsFace E C} := by
  ext C
  constructor
  · rintro ⟨hne, A, hA, rfl⟩
    exact (s.cellsS_inter_faces hA hES hne).2
  · intro hC
    exact ⟨hC.1, C, s.cellsS_face_closed hES hC, (Set.inter_eq_left.mpr hC.subset).symm⟩

/-- (3) A cell of `S` carried by `E` is `E`. -/
theorem carrier_eq_of_cellsS {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hES : E ∈ s.cellsS)
    {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS) (hcar : IsCarrier s.B E C) : C = E := by
  have hCE : C ⊆ E := hcar.2.1
  have hmem : C ∈ s.restrict s.cellsS E := ⟨cellsS_nonempty s hC, C, hC, (Set.inter_eq_left.mpr hCE).symm⟩
  rw [restrict_cellsS_eq_faces s hES] at hmem
  exact hCE.antisymm (hcar.2.2 C (IsFace.trans s.B_isPolytope hE hmem) subset_rfl)

/-- `R|_E = T|_E` when `E` is a cell of `S`. -/
theorem restrict_cellsR_eq_T {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hES : E ∈ s.cellsS) :
    s.restrict s.cellsR E = s.restrict s.cellsT E := by
  ext C
  constructor
  · rintro ⟨hne, R, ⟨_, A, hA, D, hD, rfl⟩, rfl⟩
    have hne' : (A ∩ E).Nonempty := hne.mono fun x hx => ⟨hx.1.1, hx.2⟩
    have hAE : IsFace E (A ∩ E) := (s.cellsS_inter_faces hA hES hne').2
    have hFB : IsFace s.B (A ∩ E) := IsFace.trans s.B_isPolytope hE hAE
    have hne2 : (D ∩ (A ∩ E)).Nonempty := hne.mono fun x hx => ⟨hx.1.2, hx.1.1, hx.2⟩
    have hDF : IsFace D (D ∩ (A ∩ E)) := hFB.inter_subset (cellsT_subset_B s hD) hne2
    refine ⟨hne, D ∩ (A ∩ E), s.cellsT_face_closed hD hDF, ?_⟩
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  · rintro ⟨hne, D, hD, rfl⟩
    refine ⟨hne, E ∩ D, ⟨hne.mono fun x hx => ⟨hx.2, hx.1⟩, E, hES, D, hD, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff]
    tauto

/-- (4) For `C ⊆ E`: a cell of `R` is a cell of `T`. -/
theorem mem_cellsT_of_cellsR_subset {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hES : E ∈ s.cellsS)
    {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsR) (hCE : C ⊆ E) : C ∈ s.cellsT := by
  obtain ⟨hne, A, hA, D, hD, rfl⟩ := hC
  have hne' : (A ∩ E).Nonempty := hne.mono fun x hx => ⟨hx.1, hCE hx⟩
  have hAE : IsFace E (A ∩ E) := (s.cellsS_inter_faces hA hES hne').2
  have hFB : IsFace s.B (A ∩ E) := IsFace.trans s.B_isPolytope hE hAE
  have hne2 : (D ∩ (A ∩ E)).Nonempty := hne.mono fun x hx => ⟨hx.2, hx.1, hCE hx⟩
  have hDF : IsFace D (D ∩ (A ∩ E)) := hFB.inter_subset (cellsT_subset_B s hD) hne2
  have heq : D ∩ (A ∩ E) = A ∩ D := by
    ext x
    constructor
    · rintro ⟨hxD, hxA, -⟩
      exact ⟨hxA, hxD⟩
    · intro hx
      exact ⟨hx.2, hx.1, hCE hx⟩
  rw [← heq]
  exact s.cellsT_face_closed hD hDF

theorem carrierNum_R_eq_T {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hES : E ∈ s.cellsS) (k : ℕ) :
    s.carrierNum s.cellsR E k = s.carrierNum s.cellsT E k := by
  unfold Switch.carrierNum
  congr 1
  ext C
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hC, hdim, hcar⟩
    exact ⟨mem_cellsT_of_cellsR_subset s hE hES hC hcar.2.1, hdim, hcar⟩
  · rintro ⟨hC, hdim, hcar⟩
    exact ⟨⟨cellsT_nonempty s hC, E, hES, C, hC, (Set.inter_eq_right.mpr hcar.2.1).symm⟩, hdim, hcar⟩

theorem carrierNum_S_eq {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hES : E ∈ s.cellsS) (k : ℕ) :
    s.carrierNum s.cellsS E k = if k = adim E then 1 else 0 := by
  unfold Switch.carrierNum
  split_ifs with hk
  · rw [Set.ncard_eq_one]
    refine ⟨E, ?_⟩
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hC, -, hcar⟩
      exact carrier_eq_of_cellsS s hE hES hC hcar
    · rintro rfl
      exact ⟨hES, hk.symm, isCarrier_self s hE⟩
  · have hempty : {C | C ∈ s.cellsS ∧ adim C = k ∧ IsCarrier s.B E C} = ∅ := by
      ext C
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hC, hdim, hcar⟩
      rw [carrier_eq_of_cellsS s hE hES hC hcar] at hdim
      exact hk hdim.symm
    rw [hempty, Set.ncard_empty]

theorem deltaCoeff_eq_zero_of_S {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hES : E ∈ s.cellsS) (k : ℕ) :
    s.deltaCoeff E k = 0 := by
  unfold Switch.deltaCoeff
  rw [carrierNum_R_eq_T s hE hES k, carrierNum_S_eq s hE hES k]
  split_ifs <;> push_cast <;> ring

/-! ### `U` affine on `E` (the mirror image) -/

theorem mem_cellsT_of_affineOn {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hU : AffineOn s.U E) : E ∈ s.cellsT := by
  obtain ⟨C, hC, hEC⟩ := (Proofs.lemma_3_6_cover_proved s E hE E subset_rfl (face_convex s hE) rfl).2 hU
  have hCE : C ⊆ E := by
    obtain ⟨⟨_, A, _, rfl⟩, _⟩ := hC
    exact Set.inter_subset_right
  have hCeq : C = E := hCE.antisymm hEC
  rw [← hCeq]
  exact s.restrict_cellsT_subset hE hC.1

theorem restrict_cellsT_eq_faces {E : Set (s.P' → ℝ)} (hET : E ∈ s.cellsT) :
    s.restrict s.cellsT E = {C | IsFace E C} := by
  ext C
  constructor
  · rintro ⟨hne, D, hD, rfl⟩
    exact (s.cellsT_inter_faces hD hET hne).2
  · intro hC
    exact ⟨hC.1, C, s.cellsT_face_closed hET hC, (Set.inter_eq_left.mpr hC.subset).symm⟩

theorem carrier_eq_of_cellsT {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hET : E ∈ s.cellsT)
    {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsT) (hcar : IsCarrier s.B E C) : C = E := by
  have hCE : C ⊆ E := hcar.2.1
  have hmem : C ∈ s.restrict s.cellsT E := ⟨cellsT_nonempty s hC, C, hC, (Set.inter_eq_left.mpr hCE).symm⟩
  rw [restrict_cellsT_eq_faces s hET] at hmem
  exact hCE.antisymm (hcar.2.2 C (IsFace.trans s.B_isPolytope hE hmem) subset_rfl)

theorem restrict_cellsR_eq_S {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hET : E ∈ s.cellsT) :
    s.restrict s.cellsR E = s.restrict s.cellsS E := by
  ext C
  constructor
  · rintro ⟨hne, R, ⟨_, A, hA, D, hD, rfl⟩, rfl⟩
    have hne' : (D ∩ E).Nonempty := hne.mono fun x hx => ⟨hx.1.2, hx.2⟩
    have hDE : IsFace E (D ∩ E) := (s.cellsT_inter_faces hD hET hne').2
    have hFB : IsFace s.B (D ∩ E) := IsFace.trans s.B_isPolytope hE hDE
    have hne2 : (A ∩ (D ∩ E)).Nonempty := hne.mono fun x hx => ⟨hx.1.1, hx.1.2, hx.2⟩
    have hAF : IsFace A (A ∩ (D ∩ E)) := hFB.inter_subset (cellsS_subset_B s hA) hne2
    refine ⟨hne, A ∩ (D ∩ E), s.cellsS_face_closed hA hAF, ?_⟩
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  · rintro ⟨hne, A, hA, rfl⟩
    refine ⟨hne, A ∩ E, ⟨hne, A, hA, E, hET, rfl⟩, ?_⟩
    ext x
    simp only [Set.mem_inter_iff]
    tauto

theorem mem_cellsS_of_cellsR_subset {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hET : E ∈ s.cellsT)
    {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsR) (hCE : C ⊆ E) : C ∈ s.cellsS := by
  obtain ⟨hne, A, hA, D, hD, rfl⟩ := hC
  have hne' : (D ∩ E).Nonempty := hne.mono fun x hx => ⟨hx.2, hCE hx⟩
  have hDE : IsFace E (D ∩ E) := (s.cellsT_inter_faces hD hET hne').2
  have hFB : IsFace s.B (D ∩ E) := IsFace.trans s.B_isPolytope hE hDE
  have hne2 : (A ∩ (D ∩ E)).Nonempty := hne.mono fun x hx => ⟨hx.1, hx.2, hCE hx⟩
  have hAF : IsFace A (A ∩ (D ∩ E)) := hFB.inter_subset (cellsS_subset_B s hA) hne2
  have heq : A ∩ (D ∩ E) = A ∩ D := by
    ext x
    constructor
    · rintro ⟨hxA, hxD, -⟩
      exact ⟨hxA, hxD⟩
    · intro hx
      exact ⟨hx.1, hx.2, hCE hx⟩
  rw [← heq]
  exact s.cellsS_face_closed hA hAF

theorem carrierNum_R_eq_S {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hET : E ∈ s.cellsT) (k : ℕ) :
    s.carrierNum s.cellsR E k = s.carrierNum s.cellsS E k := by
  unfold Switch.carrierNum
  congr 1
  ext C
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hC, hdim, hcar⟩
    exact ⟨mem_cellsS_of_cellsR_subset s hE hET hC hcar.2.1, hdim, hcar⟩
  · rintro ⟨hC, hdim, hcar⟩
    exact ⟨⟨cellsS_nonempty s hC, C, hC, E, hET, (Set.inter_eq_left.mpr hcar.2.1).symm⟩, hdim, hcar⟩

theorem carrierNum_T_eq {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hET : E ∈ s.cellsT) (k : ℕ) :
    s.carrierNum s.cellsT E k = if k = adim E then 1 else 0 := by
  unfold Switch.carrierNum
  split_ifs with hk
  · rw [Set.ncard_eq_one]
    refine ⟨E, ?_⟩
    ext C
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hC, -, hcar⟩
      exact carrier_eq_of_cellsT s hE hET hC hcar
    · rintro rfl
      exact ⟨hET, hk.symm, isCarrier_self s hE⟩
  · have hempty : {C | C ∈ s.cellsT ∧ adim C = k ∧ IsCarrier s.B E C} = ∅ := by
      ext C
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hC, hdim, hcar⟩
      rw [carrier_eq_of_cellsT s hE hET hC hcar] at hdim
      exact hk hdim.symm
    rw [hempty, Set.ncard_empty]

theorem deltaCoeff_eq_zero_of_T {E : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hET : E ∈ s.cellsT) (k : ℕ) :
    s.deltaCoeff E k = 0 := by
  unfold Switch.deltaCoeff
  rw [carrierNum_R_eq_S s hE hET k, carrierNum_T_eq s hE hET k]
  split_ifs <;> push_cast <;> ring

end B3

end HibiLi
