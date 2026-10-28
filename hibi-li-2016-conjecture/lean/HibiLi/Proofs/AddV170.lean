/-
HibiLi/Proofs/AddV170.lean — proofs of the in-text claims F1-F7, F11, F12 of the v1.70 delta (rows in Statements.lean);
all are still in v2.10, at the v2.10 lines given below.
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


namespace HibiLi.Proofs.AddV170

open HibiLi

local instance : DecidableLT XElem := decidableLTOfDecidableLE

/-- F1 (v2.10 l. 95-97): `P` contains `X` iff some order embedding `X ↪o P` exists. -/
theorem containsX_iff_embedding_proved (P : Type*) [PartialOrder P] : ContainsX P ↔ Nonempty (XElem ↪o P) := by
  constructor
  · rintro ⟨a, b, c, g, h, hX⟩
    obtain ⟨f, -⟩ := sec1_X_copy_induced_proved (a := a) (b := b) (c := c) (g := g) (h := h) hX
    exact ⟨f⟩
  · rintro ⟨f⟩
    refine ⟨f .a, f .b, f .c, f .g, f .h, ?_⟩
    simp only [f.lt_iff_lt, f.le_iff_le]
    decide

/-- F1, the induced-subposet wording: `P` contains `X` iff some subset of `P`, with the induced order, is
isomorphic to `X`. -/
theorem containsX_iff_subposet_proved (P : Type*) [PartialOrder P] :
    ContainsX P ↔ ∃ S : Set P, Nonempty (XElem ≃o S) := by
  rw [containsX_iff_embedding_proved]
  constructor
  · rintro ⟨f⟩
    exact ⟨Set.range f, ⟨OrderEmbedding.orderIso (f := f)⟩⟩
  · rintro ⟨S, ⟨e⟩⟩
    exact ⟨e.toOrderEmbedding.trans (OrderEmbedding.subtype (· ∈ S))⟩

open Classical in
/-- F4 (v2.10 l. 737-742): for a chain `K` of `L` with `pc ∈ K` (`pc` = `a` or `b`), the linear form
`Σ_{p ∈ K ∖ {pc}} x_p` factors through `ζ` by a linear map. -/
theorem family_form_zeta_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) {pc : x.toSwitch.P'}
    (hpc : pc = x.pa ∨ pc = x.pb) (hcK : pc ∈ K) :
    ∃ F : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] ℝ, ∀ u, x.toSwitch.chainSum (K.erase pc) u = F (x.zeta u) := by
  refine ⟨∑ p ∈ (K.erase pc).attach,
    LinearMap.proj (R := ℝ) (φ := fun _ : {p // p ∉ x.special} => ℝ)
      ⟨p.1, Lemma46.form_not_special x hK hpc hcK p.2⟩, fun u => ?_⟩
  rw [LinearMap.sum_apply]
  simp only [LinearMap.proj_apply, XSwitch.zeta, Switch.chainSum]
  exact (Finset.sum_attach _ (fun p => u p)).symm

/-- F7 (v2.10 l. 341-345): the order polytope of the chain `p₁ < p₂` is the triangle `0 ≤ x_{p₁} ≤ z ≤ 1`. -/
theorem chain2_orderPolytope_eq : orderPolytope Chain2 = {u | 0 ≤ u 0 ∧ u 0 ≤ u 1 ∧ u 1 ≤ 1} := by
  ext u
  simp only [orderPolytope, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hle⟩
    exact ⟨(hb 0).1, hle 0 1 (by decide), (hb 1).2⟩
  · rintro ⟨h0, h01, h1⟩
    refine ⟨Fin.forall_fin_two.2 ⟨⟨h0, by linarith⟩, ⟨by linarith, h1⟩⟩, ?_⟩
    rw [Fin.forall_fin_two]
    exact ⟨Fin.forall_fin_two.2 ⟨fun _ => le_rfl, fun _ => h01⟩,
      Fin.forall_fin_two.2 ⟨fun hle => absurd hle (by decide), fun _ => le_rfl⟩⟩

/-- F7 (v2.10 l. 346): the chain polytope of the chain `p₁ < p₂` is the triangle `x_{p₁} ≥ 0, 0 ≤ z ≤ 1 − x_{p₁}`. -/
theorem chain2_chainPolytope_eq : chainPolytope Chain2 = {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 1 ≤ 1 - u 0} := by
  ext u
  simp only [chainPolytope, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hnn, hch⟩
    have hsum := hch Finset.univ (fun p _ r _ _ => le_total p r)
    rw [Fin.sum_univ_two] at hsum
    exact ⟨hnn 0, hnn 1, by linarith⟩
  · rintro ⟨h0, h1, h01⟩
    have hnn : ∀ p, 0 ≤ u p := Fin.forall_fin_two.2 ⟨h0, h1⟩
    refine ⟨hnn, fun K _ => ?_⟩
    calc ∑ p ∈ K, u p ≤ ∑ p, u p :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ K) (fun p _ _ => hnn p)
      _ = u 0 + u 1 := Fin.sum_univ_two u
      _ ≤ 1 := by linarith

section CenterCuts

open Example21.CenterSwitch Example21.CenterGeometry

/-- F2 helper: for the switch of `c` on `X`, the domain of the branch `{a}` of `L = max(x_a, x_b)`. -/
theorem center_domL_true :
    center.domL (lowerBranch true) = {u | u ∈ center.B ∧ u canonical.pb ≤ u canonical.pa} := by
  ext u
  constructor
  · rintro ⟨hB, hL⟩
    refine ⟨hB, ?_⟩
    rw [L_eq hB] at hL
    simpa [lowerBranch, Switch.chainSum] using hL
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    rw [L_eq hB]
    simp [lowerBranch, Switch.chainSum, h]

theorem center_domL_false :
    center.domL (lowerBranch false) = {u | u ∈ center.B ∧ u canonical.pa ≤ u canonical.pb} := by
  ext u
  constructor
  · rintro ⟨hB, hL⟩
    refine ⟨hB, ?_⟩
    rw [L_eq hB] at hL
    simpa [lowerBranch, Switch.chainSum] using hL
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    rw [L_eq hB]
    simp [lowerBranch, Switch.chainSum, h]

theorem center_domU_true :
    center.domU (upperBranch true) = {u | u ∈ center.B ∧ u canonical.ph ≤ u canonical.pg} := by
  ext u
  constructor
  · rintro ⟨hB, hU⟩
    refine ⟨hB, ?_⟩
    rw [U_eq hB] at hU
    simpa [upperBranch, Switch.upVal] using hU
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    rw [U_eq hB]
    simp [upperBranch, Switch.upVal, h]

theorem center_domU_false :
    center.domU (upperBranch false) = {u | u ∈ center.B ∧ u canonical.pg ≤ u canonical.ph} := by
  ext u
  constructor
  · rintro ⟨hB, hU⟩
    refine ⟨hB, ?_⟩
    rw [U_eq hB] at hU
    simpa [upperBranch, Switch.upVal] using hU
  · rintro ⟨hB, h⟩
    refine ⟨hB, ?_⟩
    rw [U_eq hB]
    simp [upperBranch, Switch.upVal, h]

/-- F2 (v2.10 l. 361-362): the maximal (full-dimensional) cells of `S` for the switch of `c` on `X`. -/
theorem center_S_top : {C | C ∈ center.cellsS ∧ adim C = Fintype.card center.P'} =
    {{u | u ∈ center.B ∧ u canonical.pb ≤ u canonical.pa}, {u | u ∈ center.B ∧ u canonical.pa ≤ u canonical.pb}} := by
  rw [← center_domL_true, ← center_domL_false]
  ext C
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hC, hdim⟩
    obtain ⟨cut, hface⟩ := (cellsS_iff C).1 hC
    have hEq := hface.eq_of_adim_eq (hdim.trans (domL_full cut).symm)
    cases cut
    · exact Or.inr hEq
    · exact Or.inl hEq
  · rintro (rfl | rfl)
    · refine ⟨(cellsS_iff _).2 ⟨true, IsFace.refl ⟨0, ?_⟩⟩, domL_full true⟩
      rw [center_domL_true]
      exact ⟨zero_mem_B, le_rfl⟩
    · refine ⟨(cellsS_iff _).2 ⟨false, IsFace.refl ⟨0, ?_⟩⟩, domL_full false⟩
      rw [center_domL_false]
      exact ⟨zero_mem_B, le_rfl⟩

/-- F2 (v2.10 l. 362): the maximal (full-dimensional) cells of `T` for the switch of `c` on `X`. -/
theorem center_T_top : {C | C ∈ center.cellsT ∧ adim C = Fintype.card center.P'} =
    {{u | u ∈ center.B ∧ u canonical.ph ≤ u canonical.pg}, {u | u ∈ center.B ∧ u canonical.pg ≤ u canonical.ph}} := by
  rw [← center_domU_true, ← center_domU_false]
  ext C
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hC, hdim⟩
    obtain ⟨cut, hface⟩ := (cellsT_iff C).1 hC
    have hEq := hface.eq_of_adim_eq (hdim.trans (domU_full cut).symm)
    cases cut
    · exact Or.inr hEq
    · exact Or.inl hEq
  · rintro (rfl | rfl)
    · refine ⟨(cellsT_iff _).2 ⟨true, IsFace.refl ⟨0, ?_⟩⟩, domU_full true⟩
      rw [center_domU_true]
      exact ⟨zero_mem_B, le_rfl⟩
    · refine ⟨(cellsT_iff _).2 ⟨false, IsFace.refl ⟨0, ?_⟩⟩, domU_full false⟩
      rw [center_domU_false]
      exact ⟨zero_mem_B, le_rfl⟩

end CenterCuts

open Classical in
/-- F3 helper: restricting a subdivision of `base` to a face `E` of `base` gives a subdivision of `E`, and every
nonempty `A ∩ E` (`A` a cell) is a face of `A` and itself a cell. -/
theorem restrict_subdivision {ι : Type*} [Fintype ι] {base E : Set (ι → ℝ)} {cells : Finset (Set (ι → ℝ))}
    (hsub : IsFinitePolytopalSubdivision base cells) (hE : IsFace base E) :
    IsFinitePolytopalSubdivision E ((cells.image (· ∩ E)).filter Set.Nonempty) ∧
    (∀ A ∈ cells, (A ∩ E).Nonempty → IsFace A (A ∩ E) ∧ A ∩ E ∈ cells) ∧
    (∀ C, C ∈ (cells.image (· ∩ E)).filter Set.Nonempty ↔ C.Nonempty ∧ ∃ A ∈ cells, C = A ∩ E) := by
  obtain ⟨hpoly, hcover, hclosed, hinter⟩ := hsub
  have hAB : ∀ A ∈ cells, A ⊆ base := fun A hA x hx => hcover ▸ Set.mem_sUnion.2 ⟨A, hA, hx⟩
  have key : ∀ A ∈ cells, (A ∩ E).Nonempty → IsFace A (A ∩ E) ∧ A ∩ E ∈ cells := by
    intro A hA hne
    have hf : IsFace A (A ∩ E) := hE.inter_subset (hAB A hA) hne
    exact ⟨hf, hclosed A hA _ hf⟩
  have hmem : ∀ C, C ∈ (cells.image (· ∩ E)).filter Set.Nonempty ↔ C.Nonempty ∧ ∃ A ∈ cells, C = A ∩ E := by
    intro C
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨A, hA, rfl⟩, hne⟩
      exact ⟨hne, A, hA, rfl⟩
    · rintro ⟨hne, A, hA, rfl⟩
      exact ⟨⟨A, hA, rfl⟩, hne⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, key, hmem⟩
  · intro C hC
    obtain ⟨hne, A, hA, rfl⟩ := (hmem C).1 hC
    exact hpoly _ (key A hA hne).2
  · ext x
    simp only [Set.mem_sUnion, Finset.mem_coe]
    constructor
    · rintro ⟨C, hC, hx⟩
      obtain ⟨-, A, hA, rfl⟩ := (hmem C).1 hC
      exact hx.2
    · intro hx
      have hxb : x ∈ base := hE.subset hx
      rw [← hcover] at hxb
      obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.1 hxb
      exact ⟨A ∩ E, (hmem _).2 ⟨⟨x, hxA, hx⟩, A, hA, rfl⟩, hxA, hx⟩
  · intro C hC F hF
    obtain ⟨hne, A, hA, rfl⟩ := (hmem C).1 hC
    have hFc := hclosed _ (key A hA hne).2 F hF
    have hFE : F ⊆ E := fun y hy => (hF.subset hy).2
    exact (hmem F).2 ⟨hF.1, F, hFc, (Set.inter_eq_left.2 hFE).symm⟩
  · intro C hC C' hC' hne
    obtain ⟨hne1, A, hA, rfl⟩ := (hmem C).1 hC
    obtain ⟨hne2, A', hA', rfl⟩ := (hmem C').1 hC'
    exact hinter _ (key A hA hne1).2 _ (key A' hA' hne2).2 hne

open Classical in
/-- F5 (v2.10 l. 783-787): Lemma 4.5 with, on the same `N₀`, the strict part of its proof: on `B ∩ N₀` only chains
containing `a` or `b` attain `L`, and only the terms `γ`, `η` attain `U`. -/
theorem lemma_4_5_strict_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → ∀ u ∈ x.N0 V4 Vz, ∀ v ∈ x.N0 V4 Vz,
        x.zeta u = x.zeta v → (u ∈ E ↔ v ∈ E)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        (∀ K ∈ x.toSwitch.lowBranches, x.toSwitch.chainSum K u = x.toSwitch.L u → x.pa ∈ K ∨ x.pb ∈ K) ∧
        (∀ j ∈ x.toSwitch.upBranches, x.toSwitch.upVal j u = x.toSwitch.U u → j = some x.pg ∨ j = some x.ph)) := by
  refine ⟨Lemma45.box (x.alphaPart x.u0) (Lemma45.eps x), Lemma45.box (x.zeta x.u0) (Lemma45.eps x),
    Lemma45.isOpen_box _ _, Lemma45.isOpen_box _ _, Lemma45.center_mem_box _ (Lemma45.eps_pos x),
    Lemma45.center_mem_box _ (Lemma45.eps_pos x), ?_, fun u _ hu => ?_, fun u _ hu => ?_⟩
  · intro E hE hE0 u hu v hv huv
    exact ⟨Lemma45.face_transfer x hE hE0 (Lemma45.close_of_mem x hu) (Lemma45.close_of_mem x hv) huv,
      Lemma45.face_transfer x hE hE0 (Lemma45.close_of_mem x hv) (Lemma45.close_of_mem x hu) huv.symm⟩
  · exact ⟨Lemma45.L_eq x (Lemma45.close_of_mem x hu), Lemma45.U_eq x (Lemma45.close_of_mem x hu)⟩
  · have hc := Lemma45.close_of_mem x hu
    refine ⟨fun K hK hKL => ?_, fun j hj hjU => ?_⟩
    · by_contra hab
      rw [not_or] at hab
      obtain ⟨ha, hb⟩ := hab
      have hKI : ↑K ⊆ x.toSwitch.I' := by
        simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hK
        exact hK.1
      have h0 : ∑ p ∈ K, x.u0 p = 0 := Finset.sum_eq_zero fun p hp =>
        Lemma45.u0_I x (Lemma45.not_special_I x (hKI hp) (fun e => ha (e ▸ hp)) (fun e => hb (e ▸ hp))) (hKI hp)
      have hsum := Lemma45.sum_le hc K
      have hpa := (Lemma45.special_bounds hc (show x.pa ∈ x.special by simp [XSwitch.special])).1
      have hLa : x.toSwitch.chainSum {x.pa} u ≤ x.toSwitch.L u :=
        Finset.le_sup' (fun K => x.toSwitch.chainSum K u) x.singleton_pa_mem
      simp only [Switch.chainSum, Finset.sum_singleton] at hLa
      unfold Switch.chainSum at hKL
      linarith
    · rw [Lemma45.U_eq x hc] at hjU
      have hpg := Lemma45.special_bounds hc (show x.pg ∈ x.special by simp [XSwitch.special])
      have hmin : min (u x.pg) (u x.ph) < 7 / 8 := lt_of_le_of_lt (min_le_left _ _) hpg.2
      cases j with
      | none =>
        exfalso
        have h1 : x.toSwitch.upVal none u = 1 := rfl
        linarith
      | some r =>
        simp only [Switch.upBranches, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and, Option.some.injEq, false_or] at hj
        obtain ⟨r', hq, rfl⟩ := hj
        have hr : r'.1 ∉ x.toSwitch.I := fun h => h hq.le
        by_cases hs : r' ∈ x.special
        · rcases Lemma45.special_J x hs hr with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exfalso
          have h78 := Lemma45.J_nonspecial hc hr hs
          have h1 : x.toSwitch.upVal (some r') u = u r' := rfl
          linarith

open Classical in
/-- F3 (v2.10 l. 397-403) for one family `K` of cells that is (the set of) a subdivision `c` of `B`. -/
theorem restrict_family {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {E : Set (s.P' → ℝ)}
    (hE : IsFace s.B E) (K : Set (Set (s.P' → ℝ))) (c : Finset (Set (s.P' → ℝ)))
    (hc : (c : Set (Set (s.P' → ℝ))) = K) (hsub : IsFinitePolytopalSubdivision s.B c) :
    (∀ A ∈ K, (A ∩ E).Nonempty → IsFace A (A ∩ E)) ∧ s.restrict K E ⊆ K ∧
      ∃ c' : Finset (Set (s.P' → ℝ)), (c' : Set (Set (s.P' → ℝ))) = s.restrict K E ∧
        IsFinitePolytopalSubdivision E c' := by
  obtain ⟨hE', key, hmem⟩ := restrict_subdivision hsub hE
  have hK : ∀ A, A ∈ K ↔ A ∈ c := fun A => by rw [← hc, Finset.mem_coe]
  refine ⟨fun A hA hne => (key A ((hK A).1 hA) hne).1, ?_, (c.image (· ∩ E)).filter Set.Nonempty, ?_, hE'⟩
  · rintro C ⟨hne, A, hA, rfl⟩
    exact (hK _).2 (key A ((hK A).1 hA) hne).2
  · ext C
    rw [Finset.mem_coe, hmem]
    constructor
    · rintro ⟨hne, A, hA, rfl⟩
      exact ⟨hne, A, (hK A).2 hA, rfl⟩
    · rintro ⟨hne, A, hA, rfl⟩
      exact ⟨hne, A, (hK A).1 hA, rfl⟩

/-- F12 (v2.10 l. 234-238): the unimodular map `v ↦ Mv + w` is an affine bijection of `ℝ^ι`, and `F ↦ M(F) + w`
maps the `j`-faces of any set `Q` one-to-one onto the `j`-faces of `M(Q) + w`. (The equivalence is the one built in
`UnimodEquiv.fNum_eq`.) -/
theorem unimod_faces_proved {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (hM : M.det = 1 ∨ M.det = -1) (w : ι → ℤ) :
    ∃ f : (ι → ℝ) ≃ᵃ[ℝ] (ι → ℝ),
      (f : (ι → ℝ) → (ι → ℝ)) = (fun v => (M.map (Int.cast : ℤ → ℝ)).mulVec v + (fun i => (w i : ℝ))) ∧
      ∀ (Q : Set (ι → ℝ)) (j : ℕ), faces (f '' Q) j = (fun F => f '' F) '' faces Q j ∧
        Set.InjOn (fun F => f '' F) (faces Q j) := by
  have determinant_ne : M.det ≠ 0 := by
    rcases hM with positive | negative
    · simp [positive]
    · simp [negative]
  have real_determinant_ne : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast determinant_ne
  let linear := LinearEquiv.ofInjectiveEndo (M.map (Int.cast : ℤ → ℝ)).mulVecLin
    (Matrix.mulVec_injective_of_det_ne_zero real_determinant_ne)
  let equiv := linear.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (ι → ℝ) (fun i => (w i : ℝ)))
  refine ⟨equiv, ?_, fun Q j => ⟨faces_image_affineEquiv equiv Q j, ?_⟩⟩
  · funext v
    change (fun i => (w i : ℝ)) + (M.map (Int.cast : ℤ → ℝ)).mulVec v = _
    exact add_comm _ _
  · exact (Set.image_injective.mpr equiv.injective).injOn

/-- F11 helper: for a convex nonempty `Q ⊆ ℝ^P`, placed in the hyperplane `v ⊥ = 0` by `bottomLift`, and an apex
with `apex ⊥ = 1`, the section of the pyramid `conv({apex} ∪ bottomLift(Q))` at `v ⊥ = θ` (`0 ≤ θ ≤ 1`) is
`θ • apex + (1 − θ) • bottomLift(Q)`. -/
theorem bottom_pyramid_section {P : Type*} [Fintype P] {Q : Set (P → ℝ)} (hQ : Convex ℝ Q) (hne : Q.Nonempty)
    {apex : WithBot P → ℝ} (hapex : apex ⊥ = 1) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    {v | v ∈ convexHull ℝ (insert apex (bottomLift '' Q)) ∧ v ⊥ = θ} =
      (fun w : P → ℝ => θ • apex + (1 - θ) • bottomLift w) '' Q := by
  have hconv : Convex ℝ (bottomLift '' Q) := hQ.linear_image bottomLift.toLinearMap
  rw [convexHull_insert (hne.image _), hconv.convexHull_eq]
  ext v
  constructor
  · rintro ⟨hv, hbot⟩
    obtain ⟨a, ha, b, hb, hseg⟩ := mem_convexJoin.1 hv
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨w, hw, rfl⟩ := hb
    obtain ⟨α, β, -, -, hαβ, rfl⟩ := hseg
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hapex, bottomLift_bot, mul_one, mul_zero,
      add_zero] at hbot
    refine ⟨w, hw, ?_⟩
    rw [← hbot, show β = 1 - α by linarith]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨mem_convexJoin.2 ⟨apex, Set.mem_singleton apex, bottomLift w, ⟨w, hw, rfl⟩,
      θ, 1 - θ, h0, by linarith, by ring, rfl⟩, ?_⟩
    simp [hapex]

/-- F11 (v2.10 l. 948-959): adjoining a new minimum `⊥` to `P`: the sections of `O(P ∪ {⊥})` and `C(P ∪ {⊥})` at
`v ⊥ = θ`, the two pyramids (convex hull of apex and lifted base, apex off the base's affine hull), the two apexes,
and "every maximal chain contains `⊥`". -/
theorem bottom_pyramids_proved (P : Type*) [Fintype P] [PartialOrder P] :
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      {v | v ∈ orderPolytope (WithBot P) ∧ v ⊥ = θ} =
        (fun w : P → ℝ => θ • orderBottomApex + (1 - θ) • bottomLift w) '' orderPolytope P) ∧
    orderPolytope (WithBot P) = convexHull ℝ (insert orderBottomApex (bottomLift '' orderPolytope P)) ∧
    orderBottomApex ∉ affineSpan ℝ (bottomLift '' orderPolytope P) ∧
    (∀ pp : WithBot P, orderBottomApex (P := P) pp = 1) ∧
    (∀ K : Set (WithBot P), IsMaxChain (· ≤ ·) K → ⊥ ∈ K) ∧
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      {x | x ∈ chainPolytope (WithBot P) ∧ x ⊥ = θ} =
        (fun w : P → ℝ => θ • chainBottomApex + (1 - θ) • bottomLift w) '' chainPolytope P) ∧
    chainPolytope (WithBot P) = convexHull ℝ (insert chainBottomApex (bottomLift '' chainPolytope P)) ∧
    chainBottomApex ∉ affineSpan ℝ (bottomLift '' chainPolytope P) ∧
    chainBottomApex (P := P) ⊥ = 1 ∧ (∀ pp : P, chainBottomApex (P := P) pp = 0) := by
  have hO0 : (0 : P → ℝ) ∈ orderPolytope P := ⟨fun _ => by simp, fun _ _ _ => by simp⟩
  have hC0 : (0 : P → ℝ) ∈ chainPolytope P := ⟨fun _ => by simp, fun _ _ => by simp⟩
  refine ⟨fun θ h0 h1 => ?_, orderPolytope_withBot_pyramid P, bottomLift_apex_outside _ _ (by simp),
    fun _ => rfl, fun _ hK => hK.bot_mem, fun θ h0 h1 => ?_, chainPolytope_withBot_pyramid P,
    bottomLift_apex_outside _ _ (by simp), rfl, fun _ => rfl⟩
  · rw [orderPolytope_withBot_pyramid P]
    exact bottom_pyramid_section (orderPolytope_convex P) ⟨0, hO0⟩ (by simp) h0 h1
  · rw [chainPolytope_withBot_pyramid P]
    exact bottom_pyramid_section (chainPolytope_convex P) ⟨0, hC0⟩ (by simp) h0 h1

/-! F6 (v2.10 l. 898-903): the four switches of `X` other than `c` along the linear extension `a, b, c, g, h`
(the switch of `c`, at `I = {a, b}`, is `Example21.CenterSwitch.canonical`). -/

/-- F6: the switch of `a` at `I = ∅`. -/
def switchXa : Switch XElem where
  I := ∅
  isLowerSet := isLowerSet_empty
  q := .a
  q_notMem := by decide
  q_minimal := by decide

/-- F6: the switch of `b` at `I = {a}`. -/
def switchXb : Switch XElem where
  I := {XElem.a}
  isLowerSet := by unfold IsLowerSet; decide
  q := .b
  q_notMem := by decide
  q_minimal := by decide

/-- F6: the switch of `g` at `I = {c, a, b}`. -/
def switchXg : Switch XElem where
  I := {XElem.c, XElem.a, XElem.b}
  isLowerSet := by unfold IsLowerSet; decide
  q := .g
  q_notMem := by decide
  q_minimal := by decide

/-- F6: the switch of `h` at `I = {g, c, a, b}`. -/
def switchXh : Switch XElem where
  I := {XElem.g, XElem.c, XElem.a, XElem.b}
  isLowerSet := by unfold IsLowerSet; decide
  q := .h
  q_notMem := by decide
  q_minimal := by decide

end HibiLi.Proofs.AddV170
