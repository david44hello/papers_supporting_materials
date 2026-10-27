/-
HibiLi/Proofs/V060Claims.lean — proofs of the claims added or reworded in paper v0.60 (kept in v1.00; see
work/REALIGN_v060.md).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs
import HibiLi.Proofs.Lemma36
import HibiLi.Proofs.SwitchFacts
import HibiLi.Polytope.TopCells
import HibiLi.Polytope.CellGeometry
import HibiLi.Polytope.CellHalfspaces
import HibiLi.Polytope.RefinementSubdivision
import HibiLi.Polytope.SubdivisionPurity
import HibiLi.Polytope.FiniteFaces

namespace HibiLi.Proofs

open HibiLi Set

/-- Two linear forms are linearly independent iff both are nonzero and their kernels differ. -/
theorem linearIndependent_pair_iff_ker_ne {W : Type*} [AddCommGroup W] [Module ℝ W] (f g : W →ₗ[ℝ] ℝ) :
    LinearIndependent ℝ ![f, g] ↔ f ≠ 0 ∧ g ≠ 0 ∧ LinearMap.ker f ≠ LinearMap.ker g := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h
    have hf : f ≠ 0 := fun hf => by have := h 1 0 (by simp [hf]); simp at this
    refine ⟨hf, fun hg => by have := h 0 1 (by simp [hg]); simp at this, fun hk => ?_⟩
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hc
      exact hf (LinearMap.ext fun x => not_not.mp (not_exists.mp hc x))
    have key : ∀ x, g x = (g v / f v) * f x := by
      intro x
      have hx : x - (f x / f v) • v ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
      rw [hk, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hx
      rw [hx]
      ring
    have := h (g v / f v) (-1) (by ext x; simp [key x])
    norm_num at this
  · rintro ⟨hf, hg, hk⟩ s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hf, rfl⟩
    · exfalso
      apply hk
      have hgf : g = (-s / t) • f := by
        ext x
        have := congrArg (fun F : W →ₗ[ℝ] ℝ => F x) hst
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at this
        simp only [LinearMap.smul_apply, smul_eq_mul]
        field_simp
        linarith
      have hs : -s / t ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hgf
        exact hg hgf
      rw [hgf, LinearMap.ker_smul _ _ hs]

/-- For `w ∈ aff(E)`: `{u ∈ aff E | φ u = φ w} = {u ∈ aff E | ψ u = ψ w}` iff the restrictions of `φ, ψ` to `dir(E)`
have the same kernel. -/
theorem hyperplanes_eq_iff_ker_eq {V : Type*} [AddCommGroup V] [Module ℝ V] (E : Set V) {w : V}
    (hw : w ∈ affineSpan ℝ E) (φ ψ : V →ₗ[ℝ] ℝ) :
    {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} = {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} ↔
      LinearMap.ker (φ.domRestrict (vectorSpan ℝ E)) = LinearMap.ker (ψ.domRestrict (vectorSpan ℝ E)) := by
  have hdir : ∀ u, u ∈ affineSpan ℝ E ↔ u - w ∈ vectorSpan ℝ E := fun u => by
    rw [← direction_affineSpan, ← vsub_eq_sub, AffineSubspace.vsub_right_mem_direction_iff_mem hw]
  constructor
  · intro h
    ext x
    have hxw : (x : V) + w ∈ affineSpan ℝ E := (hdir _).mpr (by simp)
    have := Set.ext_iff.mp h ((x : V) + w)
    simp only [Set.mem_ofPred_eq, hxw, true_and, map_add, add_eq_right] at this
    simp [LinearMap.mem_ker, this]
  · intro h
    ext u
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hu, hφ⟩
      refine ⟨hu, ?_⟩
      have hmem : (⟨u - w, (hdir u).mp hu⟩ : vectorSpan ℝ E) ∈
          LinearMap.ker (φ.domRestrict (vectorSpan ℝ E)) := by
        simp [LinearMap.mem_ker, hφ]
      rw [h] at hmem
      simpa [LinearMap.mem_ker, sub_eq_zero] using hmem
    · rintro ⟨hu, hψ⟩
      refine ⟨hu, ?_⟩
      have hmem : (⟨u - w, (hdir u).mp hu⟩ : vectorSpan ℝ E) ∈
          LinearMap.ker (ψ.domRestrict (vectorSpan ℝ E)) := by
        simp [LinearMap.mem_ker, hψ]
      rw [← h] at hmem
      simpa [LinearMap.mem_ker, sub_eq_zero] using hmem

/-- Lemma 4.2, v0.41 vs v0.60 wording: for `w ∈ aff(E)`, the forms `φ, ψ` are linearly independent on `dir(E)` iff
`H_S = {φ = φ w}` and `H_T = {ψ = ψ w}` are hyperplanes of `aff(E)` (nonzero forms on `dir(E)`) and `H_S ≠ H_T`. -/
theorem linearIndependent_pair_iff_hyperplanes_ne {V : Type*} [AddCommGroup V] [Module ℝ V] (E : Set V) {w : V}
    (hw : w ∈ affineSpan ℝ E) (φ ψ : V →ₗ[ℝ] ℝ) :
    LinearIndependent ℝ ![φ.domRestrict (vectorSpan ℝ E), ψ.domRestrict (vectorSpan ℝ E)] ↔
      φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} := by
  rw [linearIndependent_pair_iff_ker_ne, Ne, Ne, Ne, Ne, hyperplanes_eq_iff_ker_eq E hw]

/-- `CrossingAt` is exactly the v0.60–v1.00 hypothesis of Lemma 4.2 (v1.00 lines 419–427): `H_S = {φ = φ w}`,
`H_T = {ψ = ψ w}` hyperplanes of `aff(E)` through `w`, and `H_S ≠ H_T`. -/
theorem crossingAt_iff_v060_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (w : s.P' → ℝ) :
    CrossingAt s E w ↔
      w ∈ intrinsicInterior ℝ E ∧
      ∃ N : Set (s.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧ N ∈ nhdsWithin w E ∧
      ∃ (S₁ S₂ T₁ T₂ : Set (s.P' → ℝ)) (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ),
        S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
        T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
        (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} := by
  unfold CrossingAt
  constructor
  · rintro ⟨hw, N, h1, h2, h3, S₁, S₂, T₁, T₂, φ, ψ, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hli⟩
    exact ⟨hw, N, h1, h2, h3, S₁, S₂, T₁, T₂, φ, ψ, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      (linearIndependent_pair_iff_hyperplanes_ne E
        (subset_affineSpan ℝ E (intrinsicInterior_subset hw)) φ ψ).mp hli⟩
  · rintro ⟨hw, N, h1, h2, h3, S₁, S₂, T₁, T₂, φ, ψ, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hne⟩
    exact ⟨hw, N, h1, h2, h3, S₁, S₂, T₁, T₂, φ, ψ, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      (linearIndependent_pair_iff_hyperplanes_ne E
        (subset_affineSpan ℝ E (intrinsicInterior_subset hw)) φ ψ).mpr hne⟩

/-- A finite family of nonempty polytopes in `B`, covering `B`, closed under nonempty faces and meeting face to face, is
a subdivision of `B` (the paper's definition, v1.00 lines 271–274). -/
theorem subdivision_of_parts {ι : Type*} [Fintype ι] (base : Set (ι → ℝ)) (K : Set (Set (ι → ℝ)))
    (hfin : K.Finite) (hpoly : ∀ C ∈ K, IsPolytope C) (hne : ∀ C ∈ K, C.Nonempty) (hsub : ∀ C ∈ K, C ⊆ base)
    (hcov : base ⊆ ⋃ C : K, (C : Set (ι → ℝ))) (hface : ∀ C ∈ K, ∀ F, IsFace C F → F ∈ K)
    (hinter : ∀ C ∈ K, ∀ D ∈ K, (C ∩ D).Nonempty → IsFace C (C ∩ D) ∧ IsFace D (C ∩ D)) :
    IsFinitePolytopalSubdivision base hfin.toFinset := by
  refine ⟨fun C hC => ⟨hpoly C (hfin.mem_toFinset.mp hC), hne C (hfin.mem_toFinset.mp hC)⟩, ?_,
    fun C hC F hF => hfin.mem_toFinset.mpr (hface C (hfin.mem_toFinset.mp hC) F hF),
    fun C hC D hD h => hinter C (hfin.mem_toFinset.mp hC) D (hfin.mem_toFinset.mp hD) h⟩
  apply Set.Subset.antisymm
  · rintro u ⟨C, hC, huC⟩
    exact hsub C (hfin.mem_toFinset.mp hC) huC
  · intro u hu
    obtain ⟨C, huC⟩ := Set.mem_iUnion.mp (hcov hu)
    exact ⟨C.1, hfin.mem_toFinset.mpr C.2, huC⟩

/-- v1.00 lines 281–284: `S`, `T` and `R` are subdivisions of `B` [Fourier, Section 4] (here proved). -/
theorem sec3_subdivisions_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∃ cS cT cR : Finset (Set (s.P' → ℝ)),
      (cS : Set (Set (s.P' → ℝ))) = s.cellsS ∧ (cT : Set (Set (s.P' → ℝ))) = s.cellsT ∧
      (cR : Set (Set (s.P' → ℝ))) = s.cellsR ∧
      IsFinitePolytopalSubdivision s.B cS ∧ IsFinitePolytopalSubdivision s.B cT ∧
      IsFinitePolytopalSubdivision s.B cR := by
  classical
  have hS_B : ∀ C ∈ s.cellsS, C ⊆ s.B := by
    rintro C ⟨K, -, -, hface⟩ u hu
    exact (hface.subset hu).1
  have hT_B : ∀ C ∈ s.cellsT, C ⊆ s.B := by
    rintro C ⟨j, -, -, hface⟩ u hu
    exact (hface.subset hu).1
  refine ⟨s.cellsS_finite.toFinset, s.cellsT_finite.toFinset, s.cellsR_finite.toFinset, by simp, by simp, by simp,
    ?_, ?_, ?_⟩
  · exact subdivision_of_parts _ _ _ (fun C hC => s.cellsS_isPolytope hC)
      (fun C hC => by obtain ⟨_, _, _, hf⟩ := hC; exact hf.1) hS_B s.cellsS_cover
      (fun C hC F hF => s.cellsS_face_closed hC hF) (fun C hC D hD h => s.cellsS_inter_faces hC hD h)
  · exact subdivision_of_parts _ _ _ (fun C hC => s.cellsT_isPolytope hC)
      (fun C hC => by obtain ⟨_, _, _, hf⟩ := hC; exact hf.1) hT_B s.cellsT_cover
      (fun C hC F hF => s.cellsT_face_closed hC hF) (fun C hC D hD h => s.cellsT_inter_faces hC hD h)
  · exact subdivision_of_parts _ _ _ (fun C hC => s.cellsR_isPolytope hC) (fun C hC => hC.1)
      (fun C hC => by obtain ⟨_, A, hA, D, -, rfl⟩ := hC; exact fun u hu => hS_B A hA hu.1) s.cellsR_cover
      (fun C hC F hF => s.cellsR_face_closed hC hF) (fun C hC D hD h => s.cellsR_inter_faces hC hD h)

/-- v1.00 lines 321–322: `L` depends only on the coordinates `x_p` with `p < q`, and `U` only on the `y_r` with
`r > q`. -/
theorem sec3_L_U_locality_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (u v : s.P' → ℝ) :
    ((∀ p : s.P', p.1 < s.q → u p = v p) → s.L u = s.L v) ∧
      ((∀ r : s.P', s.q < r.1 → u r = v r) → s.U u = s.U v) := by
  classical
  constructor
  · intro h
    unfold Switch.L
    refine Finset.sup'_congr _ rfl fun K hK => ?_
    unfold Switch.chainSum
    refine Finset.sum_congr rfl fun p hp => h p ?_
    simp only [Switch.lowBranches, Finset.mem_filter] at hK
    exact hK.2.2.2 p hp
  · intro h
    unfold Switch.U
    refine Finset.inf'_congr _ rfl fun j hj => ?_
    simp only [Switch.upBranches, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    rcases hj with rfl | ⟨r, hr, rfl⟩
    · rfl
    · exact h r hr

/-- Generic form: in a family `K` of polytopes with finite halfspace representations, closed under nonempty faces
and meeting face to face, covering `B`, every point of a face `E` of `B` lies in the relative interior of exactly one
member of `K|_E` (members of `K` lie in `B`). -/
theorem unique_restrict_cell {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (K : Set (Set (s.P' → ℝ)))
    (hsub : ∀ C ∈ K, C ⊆ s.B) (hpoly : ∀ C ∈ K, IsPolytope C) (hrep : ∀ C ∈ K, HasFiniteHalfspaceRep C)
    (hcov : s.B ⊆ ⋃ C : K, (C : Set (s.P' → ℝ))) (hface : ∀ C ∈ K, ∀ F, IsFace C F → F ∈ K)
    (hinter : ∀ C ∈ K, ∀ D ∈ K, (C ∩ D).Nonempty → IsFace C (C ∩ D) ∧ IsFace D (C ∩ D))
    (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (u : s.P' → ℝ) (hu : u ∈ E) :
    ∃! A, A ∈ s.restrict K E ∧ u ∈ intrinsicInterior ℝ A := by
  -- restricted cells are cells
  have hrK : ∀ A ∈ s.restrict K E, A ∈ K := by
    rintro A ⟨hne, C, hC, rfl⟩
    exact hface C hC _ (hE.inter_subset (hsub C hC) hne)
  obtain ⟨⟨C, hC⟩, huC⟩ := Set.mem_iUnion.mp (hcov (hE.subset hu))
  obtain ⟨F, hF, -⟩ := (hpoly C hC).existsUnique_carrier (Set.singleton_nonempty u)
    (Set.singleton_subset_iff.mpr huC)
  have huF : u ∈ intrinsicInterior ℝ F :=
    hF.intrinsicInterior_subset (hrep C hC) (by rw [intrinsicInterior_singleton]; rfl)
  have hFK : F ∈ K := hface C hC F hF.1
  have hFE : F ∩ E = F :=
    (hE.inter_subset (hsub F hFK) ⟨u, intrinsicInterior_subset huF, hu⟩).eq_of_mem_intrinsicInterior
      ⟨intrinsicInterior_subset huF, hu⟩ huF
  refine ⟨F, ⟨⟨⟨u, intrinsicInterior_subset huF⟩, F, hFK, hFE.symm⟩, huF⟩, ?_⟩
  rintro A ⟨hA, huA⟩
  have hAK := hrK A hA
  have hne : (A ∩ F).Nonempty := ⟨u, intrinsicInterior_subset huA, intrinsicInterior_subset huF⟩
  obtain ⟨h1, h2⟩ := hinter A hAK F hFK hne
  have e1 := h1.eq_of_mem_intrinsicInterior ⟨intrinsicInterior_subset huA, intrinsicInterior_subset huF⟩ huA
  have e2 := h2.eq_of_mem_intrinsicInterior ⟨intrinsicInterior_subset huA, intrinsicInterior_subset huF⟩ huF
  rw [← e1, e2]

/-- Definition 3.3, "the unique cells" (v1.00 lines 316–317). -/
theorem def_3_3_unique_cells_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (u : s.P' → ℝ) (hu : u ∈ intrinsicInterior ℝ E) :
    (∃! A, A ∈ s.restrict s.cellsS E ∧ u ∈ intrinsicInterior ℝ A) ∧
      (∃! D, D ∈ s.restrict s.cellsT E ∧ u ∈ intrinsicInterior ℝ D) := by
  have huE := intrinsicInterior_subset hu
  constructor
  · exact unique_restrict_cell s s.cellsS (fun C hC => by obtain ⟨_, _, _, hf⟩ := hC; exact fun v hv => (hf.subset hv).1)
      (fun C hC => s.cellsS_isPolytope hC) (fun C hC => s.cellsS_halfspaces hC) s.cellsS_cover
      (fun C hC F hF => s.cellsS_face_closed hC hF) (fun C hC D hD h => s.cellsS_inter_faces hC hD h) E hE u huE
  · exact unique_restrict_cell s s.cellsT (fun C hC => by obtain ⟨_, _, _, hf⟩ := hC; exact fun v hv => (hf.subset hv).1)
      (fun C hC => s.cellsT_isPolytope hC) (fun C hC => s.cellsT_halfspaces hC) s.cellsT_cover
      (fun C hC F hF => s.cellsT_face_closed hC hF) (fun C hC D hD h => s.cellsT_inter_faces hC hD h) E hE u huE

/-- Generic second clause of Lemma 3.6: an `e`-dimensional convex subset of the face `E` on which `F` is affine lies
in an `e`-cell of the restricted affinity subdivision. -/
theorem pwTop_cover {ι β : Type*} [Fintype ι] {B : Set (ι → ℝ)} {S : Finset β} {f : β → (ι → ℝ) →ᵃ[ℝ] ℝ}
    {F : (ι → ℝ) → ℝ} (hle : ∀ i ∈ S, ∀ u, f i u ≤ F u) (hex : ∀ u, ∃ i ∈ S, F u = f i u)
    (hBc : Convex ℝ B) (hBcl : IsClosed B) (hBdim : adim B = Fintype.card ι)
    {E : Set (ι → ℝ)} (hE : IsFace B E) {A : Set (ι → ℝ)} (hAE : A ⊆ E) (hAc : Convex ℝ A)
    (hdim : adim A = adim E) (hA : AffineOn F A) : ∃ C ∈ pwTop B S f F E, A ⊆ C := by
  -- a full-dimensional branch domain containing `A` and meeting `E`
  obtain ⟨i, hi, hfull, x, hxE, hxi, hAi⟩ : ∃ i ∈ S, adim (pwDom B f F i) = Fintype.card ι ∧
      ∃ x ∈ E, x ∈ pwDom B f F i ∧ A ⊆ pwDom B f F i := by
    rcases A.eq_empty_or_nonempty with rfl | hAne
    · obtain ⟨x, hx⟩ := hE.1
      obtain ⟨i, hi, hfull, hxi⟩ := pw_cover hle hex hBc hBcl hBdim (hE.subset hx)
      exact ⟨i, hi, hfull, x, hx, hxi, empty_subset _⟩
    · obtain ⟨g, hg⟩ := hA
      obtain ⟨x, hx⟩ := hAne.intrinsicInterior hAc
      have hxA : x ∈ A := intrinsicInterior_subset hx
      obtain ⟨i, hi, hfull, hxi⟩ := pw_cover hle hex hBc hBcl hBdim (hE.subset (hAE hxA))
      have hzero := affine_eq_of_intrinsicInterior_min hx (g - f i) (fun y hy => by
        simp only [AffineMap.coe_sub, Pi.sub_apply]
        linarith [hg x hxA, hg y hy, hxi.2, hle i hi y])
      refine ⟨i, hi, hfull, x, hAE hxA, hxi, fun y hy => ⟨hE.subset (hAE hy), ?_⟩⟩
      have hy0 := hzero y hy
      simp only [AffineMap.coe_sub, Pi.sub_apply] at hy0
      linarith [hg x hxA, hg y hy, hxi.2]
  have hne : (pwDom B f F i ∩ E).Nonempty := ⟨x, hxi, hxE⟩
  have hface : IsFace (pwDom B f F i) (pwDom B f F i ∩ E) :=
    isFace_inter_of_isFace hE (fun u hu => hu.1) hne
  refine ⟨pwDom B f F i ∩ E, ⟨⟨hne, _, ⟨i, hi, hfull, hface⟩, by rw [inter_assoc, inter_self]⟩, ?_⟩,
    subset_inter hAi hAE⟩
  apply le_antisymm
  · exact Submodule.finrank_mono (vectorSpan_mono ℝ inter_subset_right)
  · rw [← hdim]
    exact Submodule.finrank_mono (vectorSpan_mono ℝ (subset_inter hAi hAE))

/-- Lemma 3.6, second clause (v1.00 lines 382–383). -/
theorem lemma_3_6_cover_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (D : Set (s.P' → ℝ)) (hDE : D ⊆ E) (hDc : Convex ℝ D) (hDdim : adim D = adim E) :
    (AffineOn s.L D → ∃ C ∈ s.topCells s.cellsS E, D ⊆ C) ∧
      (AffineOn s.U D → ∃ C ∈ s.topCells s.cellsT E, D ⊆ C) := by
  obtain ⟨hBc, hBcl⟩ := B_convex_closed s
  have hBdim : adim s.B = Fintype.card s.P' := chainOrderPolytope_adim _ _
  constructor
  · intro hL
    rw [← pwTop_L]
    refine pwTop_cover (fun K hK u => (chainSumAff_apply s K u).trans_le (chainSum_le_L s hK u))
      (fun u => ?_) hBc hBcl hBdim hE hDE hDc hDdim hL
    obtain ⟨K, hK, hmax⟩ := Finset.exists_mem_eq_sup' s.lowBranches_nonempty (fun K => s.chainSum K u)
    exact ⟨K, hK, hmax.trans (chainSumAff_apply s K u).symm⟩
  · intro hU
    rw [← pwTop_U]
    refine pwTop_cover (S := s.upBranches) (f := fun j => -upAff s j) (F := fun u => -s.U u)
      (fun j hj u => by simpa [upAff_apply] using U_le_upVal s hj u) (fun u => ?_) hBc hBcl hBdim hE hDE hDc
      hDdim (affineOn_neg_iff.mpr hU)
    obtain ⟨j, hj, hmin⟩ := Finset.exists_mem_eq_inf' s.upBranches_nonempty (fun j => s.upVal j u)
    exact ⟨j, hj, by simp only [AffineMap.coe_neg, Pi.neg_apply, upAff_apply, neg_inj]; exact hmin⟩

end HibiLi.Proofs
