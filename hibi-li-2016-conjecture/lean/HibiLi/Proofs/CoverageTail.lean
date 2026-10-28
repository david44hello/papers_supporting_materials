/-
Additional proof-step coverage for the Hibi–Li paper, rows B10(k)–(s).
-/
import HibiLi.Polytope.DeltaNonnegative
import HibiLi.Polytope.AffinityCells
import HibiLi.Proofs.Lemma36
import HibiLi.Proofs.OrderTheory
import HibiLi.Proofs.Lemma44
import HibiLi.Proofs.Lemma48
import HibiLi.Proofs.FacePoly

namespace HibiLi.Proofs

section Cells

variable {P : Type*} [Fintype P] [PartialOrder P]

/-- Paper lines 528–531: the three dimension ranges in the carrier-count argument. -/
theorem lemma_3_5_iii_steps (s : Switch P) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (hT : s.Transverse) :
    (∀ k, adim E < k → s.carrierNum s.cellsS E k = 0 ∧
      s.carrierNum s.cellsT E k = 0 ∧ s.carrierNum s.cellsR E k = 0) ∧
    (∀ k, k < adim E → s.carrierNum s.cellsS E k + s.carrierNum s.cellsT E k ≤
      s.carrierNum s.cellsR E k) ∧
    {C | C ∈ s.cellsS ∧ adim C = adim E ∧ IsCarrier s.B E C} = s.topCells s.cellsS E ∧
    {C | C ∈ s.cellsT ∧ adim C = adim E ∧ IsCarrier s.B E C} = s.topCells s.cellsT E ∧
    {C | C ∈ s.cellsR ∧ adim C = adim E ∧ IsCarrier s.B E C} = s.topCells s.cellsR E := by
  refine ⟨?_, ?_, (s.topCellsS_eq_carried hE).symm,
    (s.topCellsT_eq_carried hE).symm, (s.topCellsR_eq_carried hE).symm⟩
  · intro k above
    exact ⟨s.carrierNum_eq_zero_of_adim_lt _ E k above,
      s.carrierNum_eq_zero_of_adim_lt _ E k above,
      s.carrierNum_eq_zero_of_adim_lt _ E k above⟩
  · exact fun k below => s.low_carrier_count_bound hT E hE k below

/-- Paper lines 543–548: each top cell on a face is a full branch domain restricted to that face. -/
theorem lemma_3_6_cell_branch_L (s : Switch P) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (A : Set (s.P' → ℝ)) (hA : A ∈ s.topCells s.cellsS E) :
    ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ A = s.domL K ∩ E ∧
      A = {u ∈ E | s.L u = s.chainSum K u} := by
  have maximal := ((lemma_3_6_proved s E hE A).1.mp hA).2.2.2.2
  obtain ⟨⟨_nonempty, _original, ⟨K, member, full, face⟩, equation⟩, _⟩ := hA
  have inside : A ⊆ s.domL K ∩ E := by
    rw [equation]
    exact fun _ hu => ⟨face.subset hu.1, hu.2⟩
  have affine : AffineOn s.L (s.domL K ∩ E) :=
    ⟨s.chainSumAffine K, fun _ hu => by simpa using hu.1.2⟩
  have equal : s.domL K ∩ E = A := maximal _ inside Set.inter_subset_right
    ((s.domL_isPolytope K member).convex.inter (hE.2.convex (B_convex_closed s).1)) affine
  refine ⟨K, member, full, equal.symm, ?_⟩
  rw [← equal]
  ext u
  constructor
  · exact fun hu => ⟨hu.2, hu.1.2⟩
  · exact fun hu => ⟨⟨hE.subset hu.1, hu.2⟩, hu.1⟩

/-- The upper-envelope version of the same branch-domain description. -/
theorem lemma_3_6_cell_branch_U (s : Switch P) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
    (A : Set (s.P' → ℝ)) (hA : A ∈ s.topCells s.cellsT E) :
    ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ A = s.domU j ∩ E ∧
      A = {u ∈ E | s.U u = s.upVal j u} := by
  have maximal := ((lemma_3_6_proved s E hE A).2.mp hA).2.2.2.2
  obtain ⟨⟨_nonempty, _original, ⟨j, member, full, face⟩, equation⟩, _⟩ := hA
  have inside : A ⊆ s.domU j ∩ E := by
    rw [equation]
    exact fun _ hu => ⟨face.subset hu.1, hu.2⟩
  have affine : AffineOn s.U (s.domU j ∩ E) :=
    ⟨s.upValAffine j, fun _ hu => by simpa using hu.1.2⟩
  have equal : s.domU j ∩ E = A := maximal _ inside Set.inter_subset_right
    ((s.domU_isPolytope j member).convex.inter (hE.2.convex (B_convex_closed s).1)) affine
  refine ⟨j, member, full, equal.symm, ?_⟩
  rw [← equal]
  ext u
  constructor
  · exact fun hu => ⟨hu.2, hu.1.2⟩
  · exact fun hu => ⟨⟨hE.subset hu.1, hu.2⟩, hu.1⟩

end Cells

section Affinity

variable {ι : Type*} [Fintype ι]

/-- Equal affine branches on a full-dimensional nonempty subset agree throughout the ambient face. -/
theorem equal_affinity_sections (base E : Set (ι → ℝ)) (value : (ι → ℝ) → ℝ)
    (f g : (ι → ℝ) →ᵃ[ℝ] ℝ)
    (nonempty : ({u ∈ base | value u = f u} ∩ E).Nonempty)
    (inside : {u ∈ base | value u = f u} ∩ E ⊆ {u ∈ base | value u = g u} ∩ E)
    (dimension : adim ({u ∈ base | value u = f u} ∩ E) = adim E) :
    {u ∈ base | value u = f u} ∩ E = {u ∈ base | value u = g u} ∩ E := by
  have span := affineSpan_eq_of_subset_of_adim_eq nonempty Set.inter_subset_right dimension
  have agree : ({u ∈ base | value u = f u} ∩ E).EqOn f g := by
    intro u hu
    exact hu.1.2.symm.trans (inside hu).1.2
  have everywhere : E.EqOn f g := by
    intro u hu
    apply AffineMap.eqOn_affineSpan agree
    rw [span]
    exact subset_affineSpan ℝ E hu
  apply Set.Subset.antisymm inside
  intro u hu
  exact ⟨⟨hu.1.1, hu.1.2.trans (everywhere hu.2).symm⟩, hu.2⟩

end Affinity

/-- Paper lines 555–557, with the paper's nonempty-cell convention explicit (also for dimension zero). -/
theorem lemma_3_6_nested_L {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (K K' : Finset s.P') (E : Set (s.P' → ℝ)) (nonempty : (s.domL K ∩ E).Nonempty)
    (inside : s.domL K ∩ E ⊆ s.domL K' ∩ E) (dimension : adim (s.domL K ∩ E) = adim E) :
    s.domL K ∩ E = s.domL K' ∩ E := by
  simpa only [Switch.chainSumAffine_apply, Switch.domL] using
    equal_affinity_sections s.B E s.L (s.chainSumAffine K) (s.chainSumAffine K')
      (by simpa only [Switch.chainSumAffine_apply, Switch.domL] using nonempty)
      (by simpa only [Switch.chainSumAffine_apply, Switch.domL] using inside)
      (by simpa only [Switch.chainSumAffine_apply, Switch.domL] using dimension)

/-- The upper-envelope version of the nested-cell statement. -/
theorem lemma_3_6_nested_U {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (j j' : Option s.P') (E : Set (s.P' → ℝ)) (nonempty : (s.domU j ∩ E).Nonempty)
    (inside : s.domU j ∩ E ⊆ s.domU j' ∩ E) (dimension : adim (s.domU j ∩ E) = adim E) :
    s.domU j ∩ E = s.domU j' ∩ E := by
  simpa only [Switch.upValAffine_apply, Switch.domU] using
    equal_affinity_sections s.B E s.U (s.upValAffine j) (s.upValAffine j')
      (by simpa only [Switch.upValAffine_apply, Switch.domU] using nonempty)
      (by simpa only [Switch.upValAffine_apply, Switch.domU] using inside)
      (by simpa only [Switch.upValAffine_apply, Switch.domU] using dimension)

/-- Paper lines 693–695: a strict upper element lies above an upper cover. -/
theorem sec4_upper_cover_below {P : Type*} [Fintype P] [PartialOrder P] (q r : P) (h : q < r) :
    ∃ s', q ⋖ s' ∧ s' ≤ r := exists_covBy_le_of_lt h

/-- Paper lines 709–710: every remaining order coordinate lies strictly above q. -/
theorem sec4_remaining_above_q {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → x.q < r.1 :=
  fun _ hr => Lemma44.q_lt_of_notMem x hr

/-- Paper lines 729–730 and 770–771: no remaining order coordinate is below either chosen cover. -/
theorem sec4_no_remaining_below_covers {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∀ r : P, r ∉ x.toSwitch.I → r ≠ x.q → ¬ r < x.g' ∧ ¬ r < x.h' := by
  intro r hr different
  have above : x.q < r := lt_of_le_of_ne (not_not.mp hr) different.symm
  exact ⟨fun below => x.q_covby_g'.2 above below, fun below => x.q_covby_h'.2 above below⟩

/-- Paper lines 852–855: the two lower bounds used in the simplex-bound induction. -/
theorem lemma_4_7_facet_counts {ι : Type*} [Fintype ι] (Q D : Set (ι → ℝ))
    (hQ : IsPolytope Q) (hD : IsFace Q D) (facet : adim D + 1 = adim Q)
    (v : ι → ℝ) (hv : IsFace Q {v}) (κ : ℕ) :
    Nat.choose (adim Q) (κ + 1) ≤ {F | IsFace Q F ∧ adim F = κ ∧ F ⊆ D}.ncard ∧
    (1 ≤ κ → Nat.choose (adim Q) κ ≤ {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F}.ncard) := by
  constructor
  · by_cases below : κ ≤ adim D
    · have lower := lemma_4_8_simplex_proved D (hQ.face hD) hD.1 κ below
      rw [facet] at lower
      have finite : {F | IsFace Q F ∧ adim F = κ ∧ F ⊆ D}.Finite :=
        hQ.finite_faces.subset (fun _ hF => hF.1)
      exact lower.trans (Set.ncard_le_ncard (fun _ hF =>
        ⟨IsFace.trans hQ hD hF.1, hF.2, hF.1.subset⟩) finite)
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _
  · intro _positive
    by_cases below : κ ≤ adim Q
    · have lower := lemma_4_8_proved Q hQ {v} hv κ (by simpa [adim_singleton] using below)
      have same : {G | IsFace Q G ∧ {v} ⊆ G ∧ adim G = adim ({v} : Set (ι → ℝ)) + κ} =
          {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F} := by
        ext F
        simp only [Set.mem_ofPred_eq, Set.singleton_subset_iff, adim_singleton, zero_add]
        tauto
      rw [same] at lower
      simpa only [adim_singleton, Nat.sub_zero] using lower
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _

/-- No face is both contained in the chosen facet and incident to a vertex outside it. -/
theorem sec4_facet_families_disjoint {ι : Type*} [Fintype ι] (Q D : Set (ι → ℝ))
    (v : ι → ℝ) (outside : v ∉ D) (κ : ℕ) :
    Disjoint {F | IsFace Q F ∧ adim F = κ ∧ F ⊆ D} {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F} := by
  exact Set.disjoint_left.mpr (fun _ hD hv => outside (hD.2.2 hv.2.2))

/-- Paper lines 976–977: every relevant coefficient is a positive binomial coefficient. -/
theorem cor_5_3_gap_coefficient (n k : ℕ) (hn : 5 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n - 1) :
    (gapPoly n).coeff k = (Nat.choose (n - 3) (k - 2) : ℤ) ∧ 1 ≤ Nat.choose (n - 3) (k - 2) := by
  constructor
  · simp only [gapPoly_coeff, hk, ite_true]
  · exact Nat.choose_pos (by omega)

/-- Paper lines 450–451: base inequalities couple a lower coordinate to an upper coordinate. -/
theorem sec3_coupled_coordinates {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ∀ p r : s.P', p.1 ∈ s.I → p.1 < s.q → s.q < r.1 → ∀ u ∈ s.B, u p ≤ u r := by
  classical
  intro p r hp hpq hqr u hu
  have hr : r ∉ s.I' := fun member => s.q_notMem (s.isLowerSet hqr.le member)
  have hpr : p < r := hpq.trans hqr
  simpa using hu.2.2.2.1 r hr {p} (by simpa [Switch.I'] using hp) (by simp [IsChainSet]) (by simpa using hpr)

end HibiLi.Proofs

