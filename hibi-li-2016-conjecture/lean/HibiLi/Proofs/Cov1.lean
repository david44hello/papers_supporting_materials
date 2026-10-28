/-
HibiLi/Proofs/Cov1.lean — proofs for the coverage rows of review REVIEW_006_cov (items B1, B2, B3, B4, B5(b), B6), paper
v2.10: purity of subdivisions, the bipartite graph `G_E` (vertices on edges, adjacent cells), Stanley's vertex
description, the Section 4.4 sum identity, and Lemma 4.6 with the v2.10 wording of Lemma 4.2's hypothesis.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Subdivision
import HibiLi.Polytope.SubdivisionPurity
import HibiLi.Polytope.TopCells
import HibiLi.Polytope.DomainCover
import HibiLi.Polytope.GraphCells
import HibiLi.Polytope.AffinityCells
import HibiLi.Polytope.RefinementGraph
import HibiLi.Polytope.RefinementAdjacency
import HibiLi.Polytope.RefinementCover
import HibiLi.Polytope.RefinementDisjoint
import HibiLi.Polytope.RelintPartition
import HibiLi.Example21.ZeroOneFaces
import HibiLi.Example21.VertexBijection
import HibiLi.Proofs.Lemma36
import HibiLi.Proofs.Lemma42
import HibiLi.Proofs.Lemma46
import HibiLi.Proofs.V060Claims

noncomputable section

namespace HibiLi.Proofs.Cov1

open HibiLi

section Purity

variable {ι : Type*} [Fintype ι]

/-- The maximal cells of a finite polytopal subdivision of a nonempty polytope `E` are exactly its cells of the
dimension of `E` (the subdivision is pure). -/
theorem max_iff_full {E : Set (ι → ℝ)} {c : Finset (Set (ι → ℝ))} (hE : IsPolytope E) (hne : E.Nonempty)
    (hsub : IsFinitePolytopalSubdivision E c) :
    ∀ C ∈ c, (∀ C' ∈ c, C ⊆ C' → C' = C) ↔ adim C = adim E := by
  intro C hC
  constructor
  · intro hmax
    exact subdivision_max_adim hE hne hsub ⟨C, hC, hmax⟩
  · intro hdim C' hC' hCC'
    have hC'E : C' ⊆ E := by
      rw [← hsub.2.1]
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.mpr hC')
    have hne' : (C ∩ C').Nonempty := by
      obtain ⟨x, hx⟩ := (hsub.1 C hC).2
      exact ⟨x, hx, hCC' hx⟩
    have hface : IsFace C' (C ∩ C') := (hsub.2.2.2 C hC C' hC' hne').2
    rw [Set.inter_eq_left.mpr hCC'] at hface
    have h1 : adim C ≤ adim C' := Submodule.finrank_mono (vectorSpan_mono ℝ hCC')
    have h2 : adim C' ≤ adim E := Submodule.finrank_mono (vectorSpan_mono ℝ hC'E)
    exact (hface.eq_of_adim_eq (by omega)).symm

/-- Two faces of a polytope whose relative interiors share a point are equal. -/
theorem face_eq_of_mem_intrinsicInterior {Q F G : Set (ι → ℝ)} (hF : IsFace Q F) (hG : IsFace Q G) {u : ι → ℝ}
    (huF : u ∈ intrinsicInterior ℝ F) (huG : u ∈ intrinsicInterior ℝ G) : F = G := by
  have hu : u ∈ F ∩ G := ⟨intrinsicInterior_subset huF, intrinsicInterior_subset huG⟩
  have hFG : IsFace F (F ∩ G) := hG.inter_subset hF.subset ⟨u, hu⟩
  have hGF : IsFace G (G ∩ F) := hF.inter_subset hG.subset ⟨u, hu.2, hu.1⟩
  have e1 : F ∩ G = F := hFG.eq_of_mem_intrinsicInterior hu huF
  have e2 : G ∩ F = G := hGF.eq_of_mem_intrinsicInterior ⟨hu.2, hu.1⟩ huG
  calc F = F ∩ G := e1.symm
    _ = G ∩ F := Set.inter_comm F G
    _ = G := e2

end Purity

section Graph

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- An `e`-cell of `S|_E` lies on an edge of `G_E`. -/
theorem vertex_on_edge_S {E S : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hS : S ∈ s.topCells s.cellsS E) :
    ∃ T ∈ s.topCells s.cellsT E, S ∩ T ∈ s.topCells s.cellsR E := by
  obtain ⟨R, hR⟩ := s.RR_nonempty_of_mem_cellsS (s.restrict_cellsS_subset hE hS.1)
  have inside : R ⊆ E := hR.2.1.trans (s.restrict_cell_subset hS.1)
  have dimension : adim R = adim E := hR.2.2.trans hS.2
  have top : R ∈ s.topCells s.cellsR E :=
    ⟨⟨hR.1.1, R, hR.1, (Set.inter_eq_left.mpr inside).symm⟩, dimension⟩
  obtain ⟨left, hleft, right, hright, hRe⟩ := s.topR_exists_pair hE top
  have hRleft : R ⊆ left := by
    rw [hRe]
    exact Set.inter_subset_left
  have hsub : R ⊆ S ∩ left := fun x hx => ⟨hR.2.1 hx, hRleft hx⟩
  have hSleft : S = left := by
    refine s.topCellsS_eq_of_full_inter hE hS hleft (top.1.1.mono hsub) (le_antisymm ?_ ?_)
    · exact Submodule.finrank_mono
        (vectorSpan_mono ℝ (Set.inter_subset_left.trans (s.restrict_cell_subset hS.1)))
    · rw [← dimension]
      exact Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  refine ⟨right, hright, ?_⟩
  rw [hSleft, ← hRe]
  exact top

/-- An `e`-cell of `T|_E` lies on an edge of `G_E`. -/
theorem vertex_on_edge_T {E T : Set (s.P' → ℝ)} (hE : IsFace s.B E) (hT : T ∈ s.topCells s.cellsT E) :
    ∃ S ∈ s.topCells s.cellsS E, S ∩ T ∈ s.topCells s.cellsR E := by
  obtain ⟨R, hR⟩ := s.RR_nonempty_of_mem_cellsT (s.restrict_cellsT_subset hE hT.1)
  have inside : R ⊆ E := hR.2.1.trans (s.restrict_cell_subset hT.1)
  have dimension : adim R = adim E := hR.2.2.trans hT.2
  have top : R ∈ s.topCells s.cellsR E :=
    ⟨⟨hR.1.1, R, hR.1, (Set.inter_eq_left.mpr inside).symm⟩, dimension⟩
  obtain ⟨left, hleft, right, hright, hRe⟩ := s.topR_exists_pair hE top
  have hRright : R ⊆ right := by
    rw [hRe]
    exact Set.inter_subset_right
  have hsub : R ⊆ T ∩ right := fun x hx => ⟨hR.2.1 hx, hRright hx⟩
  have hTright : T = right := by
    refine s.topCellsT_eq_of_full_inter hE hT hright (top.1.1.mono hsub) (le_antisymm ?_ ?_)
    · exact Submodule.finrank_mono
        (vectorSpan_mono ℝ (Set.inter_subset_left.trans (s.restrict_cell_subset hT.1)))
    · rw [← dimension]
      exact Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  refine ⟨left, hleft, ?_⟩
  rw [hTright, ← hRe]
  exact top

/-- Lemma 3.5(ii), proof (l. 518-523): two adjacent `e`-cells `S ∩ T`, `S' ∩ T'` of `R|_E` (a common face of
dimension `e - 1`) are edges of `G_E` with a common vertex: `S = S'` or `T = T'`. -/
theorem adjacent_common_vertex (hT : s.Transverse) {E S S' T T' : Set (s.P' → ℝ)} (hE : IsFace s.B E)
    (hS : S ∈ s.topCells s.cellsS E) (hS' : S' ∈ s.topCells s.cellsS E)
    (hT₁ : T ∈ s.topCells s.cellsT E) (hT₂ : T' ∈ s.topCells s.cellsT E)
    (hR : S ∩ T ∈ s.topCells s.cellsR E) (hR' : S' ∩ T' ∈ s.topCells s.cellsR E) (hne : S ∩ T ≠ S' ∩ T')
    (hD : IsFace (S ∩ T) (S ∩ T ∩ (S' ∩ T')) ∧ IsFace (S' ∩ T') (S ∩ T ∩ (S' ∩ T')))
    (hdim : adim (S ∩ T ∩ (S' ∩ T')) + 1 = adim E) : S = S' ∨ T = T' := by
  let X : MaxSubdivisionCell (s.refinementCells E) := ⟨S ∩ T, s.refinement_top_is_max hE ⟨_, hR⟩⟩
  let X' : MaxSubdivisionCell (s.refinementCells E) := ⟨S' ∩ T', s.refinement_top_is_max hE ⟨_, hR'⟩⟩
  have hadj : (subdivisionDualGraph (s.refinementCells E)).Adj X X' :=
    ⟨fun h => hne (congrArg Subtype.val h), hD.1.1, hD.1, hD.2, hdim.trans hR.2.symm, hdim.trans hR'.2.symm⟩
  have hX : s.refinementMaxPair hE X = (⟨S, hS⟩, ⟨T, hT₁⟩) := by
    apply s.top_pairs_eq_of_inter_eq hE
    · rw [s.refinementMaxPair_inter hE X]
      exact hR
    · exact s.refinementMaxPair_inter hE X
  have hX' : s.refinementMaxPair hE X' = (⟨S', hS'⟩, ⟨T', hT₂⟩) := by
    apply s.top_pairs_eq_of_inter_eq hE
    · rw [s.refinementMaxPair_inter hE X']
      exact hR'
    · exact s.refinementMaxPair_inter hE X'
  have hpair := s.refinement_adjacent_pairs hE hT X X' hadj
  rw [hX, hX'] at hpair
  rcases hpair with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

end Graph

section Stanley

variable (P : Type*) [Fintype P] [PartialOrder P]

/-- Stanley's description of the vertices of `O(P)` (l. 227-228): the indicator vectors of the upper sets. -/
theorem stanley_order :
    faces (orderPolytope P) 0 = (fun S : Set P => ({S.indicator 1} : Set (P → ℝ))) '' {S | IsUpperSet S} := by
  rw [faces_zero_eq_singletons Set.inter_subset_right (orderPolytope_eq_convexHull_zeroOne P) (fun _ hw => hw.1)]
  ext F
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(upperVectorEquiv (P := P)).symm ⟨v, hv⟩, ((upperVectorEquiv (P := P)).symm ⟨v, hv⟩).2, ?_⟩
    have h := congrArg Subtype.val ((upperVectorEquiv (P := P)).apply_symm_apply ⟨v, hv⟩)
    exact congrArg (fun w : P → ℝ => ({w} : Set (P → ℝ))) h
  · rintro ⟨S, hS, rfl⟩
    exact ⟨_, (upperVectorEquiv (P := P) ⟨S, hS⟩).2, rfl⟩

/-- Stanley's description of the vertices of `C(P)` (l. 228-229): the indicator vectors of the antichains. -/
theorem stanley_chain :
    faces (chainPolytope P) 0 =
      (fun A : Set P => ({A.indicator 1} : Set (P → ℝ))) '' {A | IsAntichain (· ≤ ·) A} := by
  rw [faces_zero_eq_singletons Set.inter_subset_right (chainPolytope_eq_convexHull_zeroOne P) (fun v hv pp => by
      refine ⟨hv.1 pp, ?_⟩
      have hh := hv.2 {pp} (by simp [IsChainSet])
      simpa using hh)]
  ext F
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(antichainVectorEquiv (P := P)).symm ⟨v, hv⟩, ((antichainVectorEquiv (P := P)).symm ⟨v, hv⟩).2, ?_⟩
    have h := congrArg Subtype.val ((antichainVectorEquiv (P := P)).apply_symm_apply ⟨v, hv⟩)
    exact congrArg (fun w : P → ℝ => ({w} : Set (P → ℝ))) h
  · rintro ⟨A, hA, rfl⟩
    exact ⟨_, (antichainVectorEquiv (P := P) ⟨A, hA⟩).2, rfl⟩

end Stanley

section Crossing

variable {P : Type*} [Fintype P] [PartialOrder P]

/-- If `X ∩ N` is the part of `N` where `p` holds and `M ⊆ N`, then `X ∩ M` is the part of `M` where `p` holds. -/
theorem inter_eq_sep_mono {V : Type*} {X N M : Set V} {p : V → Prop} (hMN : M ⊆ N)
    (h : X ∩ N = {u ∈ N | p u}) : X ∩ M = {u ∈ M | p u} := by
  ext u
  constructor
  · rintro ⟨hX, hu⟩
    have h' : u ∈ X ∩ N := ⟨hX, hMN hu⟩
    rw [h] at h'
    exact ⟨hu, h'.2⟩
  · rintro ⟨hu, hp⟩
    have h' : u ∈ {u ∈ N | p u} := ⟨hMN hu, hp⟩
    rw [← h] at h'
    exact ⟨h'.1, hu⟩

/-- A crossing at `w` (`CrossingAt`: `N` a convex neighbourhood of `w` in `E`) gives the v2.10 wording of the hypothesis
of Lemma 4.2: shrink `N` to `ball(w, ε) ∩ aff(E)`, a convex set open in `aff(E)`, inside `N` and containing `w`. -/
theorem crossing_v190 (s : Switch P) (E : Set (s.P' → ℝ)) (w : s.P' → ℝ) (hc : CrossingAt s E w) :
    w ∈ intrinsicInterior ℝ E ∧ ∃ N : Set (s.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧
      (∃ O : Set (s.P' → ℝ), IsOpen O ∧ N = O ∩ (affineSpan ℝ E : Set (s.P' → ℝ))) ∧ w ∈ N ∧
      ∃ (S₁ S₂ T₁ T₂ : Set (s.P' → ℝ)) (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ),
        S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
        T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
        (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} := by
  obtain ⟨hw, N, -, hNE, hnhds, S₁, S₂, T₁, T₂, φ, ψ, h1, h2, h3, h4, hA, hD, e1, e2, e3, e4, n1, n2, hne⟩ :=
    (crossingAt_iff_v060_proved s E w).1 hc
  obtain ⟨ε, hε, hball⟩ := L42.exists_ball hw hnhds
  have hwE : w ∈ affineSpan ℝ E := subset_affineSpan ℝ E (intrinsicInterior_subset hw)
  have hMN : Metric.ball w ε ∩ (affineSpan ℝ E : Set (s.P' → ℝ)) ⊆ N := by
    intro u hu
    have hv : u - w ∈ vectorSpan ℝ E := by
      rw [← direction_affineSpan, ← vsub_eq_sub]
      exact AffineSubspace.vsub_mem_direction hu.2 hwE
    have hu' := hball (u - w) hv (by rw [← dist_eq_norm]; exact hu.1)
    rwa [add_sub_cancel] at hu'
  refine ⟨hw, _, (convex_ball w ε).inter (affineSpan ℝ E).convex, hMN.trans hNE, ⟨_, Metric.isOpen_ball, rfl⟩,
    ⟨Metric.mem_ball_self hε, hwE⟩, S₁, S₂, T₁, T₂, φ, ψ, h1, h2, h3, h4,
    fun A hA' hAM => hA A hA' (hAM.mono (Set.inter_subset_inter_right _ hMN)),
    fun D hD' hDM => hD D hD' (hDM.mono (Set.inter_subset_inter_right _ hMN)),
    inter_eq_sep_mono (p := fun u => φ w ≤ φ u) hMN e1, inter_eq_sep_mono (p := fun u => φ u ≤ φ w) hMN e2,
    inter_eq_sep_mono (p := fun u => ψ w ≤ ψ u) hMN e3, inter_eq_sep_mono (p := fun u => ψ u ≤ ψ w) hMN e4,
    n1, n2, hne⟩

/-- **Lemma 4.6** with the v2.10 wording of the hypothesis of Lemma 4.2 (`N` convex, open in `aff(E)`). -/
theorem lemma_4_6_v190_proved (x : XSwitch P) (E : Set (x.toSwitch.P' → ℝ)) (hE : IsFace x.toSwitch.B E)
    (hE0 : x.E0 ⊆ E) :
    ∃ w ∈ intrinsicInterior ℝ E, ∃ N : Set (x.toSwitch.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧
      (∃ O : Set (x.toSwitch.P' → ℝ), IsOpen O ∧ N = O ∩ (affineSpan ℝ E : Set (x.toSwitch.P' → ℝ))) ∧ w ∈ N ∧
      ∃ (S₁ S₂ T₁ T₂ : Set (x.toSwitch.P' → ℝ)) (φ ψ : (x.toSwitch.P' → ℝ) →ₗ[ℝ] ℝ),
        S₁ ∈ x.toSwitch.topCells x.toSwitch.cellsS E ∧ S₂ ∈ x.toSwitch.topCells x.toSwitch.cellsS E ∧
        T₁ ∈ x.toSwitch.topCells x.toSwitch.cellsT E ∧ T₂ ∈ x.toSwitch.topCells x.toSwitch.cellsT E ∧
        (∀ A ∈ x.toSwitch.topCells x.toSwitch.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
        (∀ D ∈ x.toSwitch.topCells x.toSwitch.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
        S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
        T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
        φ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧ ψ.domRestrict (vectorSpan ℝ E) ≠ 0 ∧
        {u | u ∈ affineSpan ℝ E ∧ φ u = φ w} ≠ {u | u ∈ affineSpan ℝ E ∧ ψ u = ψ w} := by
  obtain ⟨w, hw⟩ := lemma_4_6_of_3_6 x (fun E hE A => lemma_3_6_proved x.toSwitch E hE A) E hE hE0
  obtain ⟨hwi, rest⟩ := crossing_v190 x.toSwitch E w hw
  exact ⟨w, hwi, rest⟩

end Crossing

section Rows

open Polynomial Finset

/-- **Section 4.4** (v2.10 l. 876-877), the displayed identity
`∑_{e=4}^{n-1} C(n-5, e-4) t^{e-2}(1+t)² = t²(1+t)^{n-3}` (as polynomials in `t = X`). -/
theorem sum_identity (n : ℕ) (hn : 5 ≤ n) :
    ∑ e ∈ Finset.Icc 4 (n - 1), (Nat.choose (n - 5) (e - 4) : ℤ[X]) * (X ^ (e - 2) * (1 + X) ^ 2) =
      X ^ 2 * (1 + X) ^ (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have hI : Finset.Icc 4 (m + 5 - 1) = (Finset.range (m + 1)).map (addLeftEmbedding 4) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply]
    constructor
    · intro h
      exact ⟨e - 4, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [hI, Finset.sum_map]
  simp only [addLeftEmbedding_apply, show m + 5 - 5 = m by omega, show m + 5 - 3 = m + 2 by omega]
  have hpow : ((1 : ℤ[X]) + X) ^ m = ∑ j ∈ Finset.range (m + 1), X ^ j * 1 ^ (m - j) * (Nat.choose m j : ℤ[X]) := by
    rw [add_comm]
    exact add_pow X 1 m
  calc ∑ j ∈ Finset.range (m + 1), (Nat.choose m (4 + j - 4) : ℤ[X]) * (X ^ (4 + j - 2) * (1 + X) ^ 2)
      = ∑ j ∈ Finset.range (m + 1), X ^ 2 * (1 + X) ^ 2 * (X ^ j * 1 ^ (m - j) * (Nat.choose m j : ℤ[X])) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show 4 + j - 4 = j by omega, show 4 + j - 2 = j + 2 by omega]
        ring
    _ = X ^ 2 * (1 + X) ^ (m + 2) := by
        rw [← Finset.mul_sum, ← hpow]
        ring

/-- **Section 2** (v2.10 l. 211), a standard fact the paper uses: every point `u` of a polytope `Q` lies in the
relative interior of exactly one face of `Q`. -/
theorem faces_relint_partition {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q) (u : ι → ℝ)
    (hu : u ∈ Q) : ∃! F, IsFace Q F ∧ u ∈ intrinsicInterior ℝ F := by
  obtain ⟨F, hF, huF⟩ := hQ.exists_face_mem_intrinsicInterior hu
  exact ⟨F, ⟨hF, huF⟩, fun G hG => (face_eq_of_mem_intrinsicInterior hF hG.1 huF hG.2).symm⟩

/-- **Lemma 3.5(i)** (v2.10 l. 487-488): "In particular (take `S = T = Y`), no `k`-cell `Y` with carrier `E` is a cell
of both `S` and `T`" (`k < e = dim E`). -/
theorem not_both {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (hT : s.Transverse)
    (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (Y : Set (s.P' → ℝ)) (hYS : Y ∈ s.cellsS) (hYT : Y ∈ s.cellsT)
    (hYE : IsCarrier s.B E Y) (hdim : adim Y < adim E) : False := by
  obtain ⟨⟨R, hR⟩, -⟩ := lemma_3_5_i_cover_proved s hT E hE Y (Or.inl hYS) hYE hdim
  exact Set.disjoint_left.mp (lemma_3_5_i_disjoint_proved s hT E hE Y Y (Or.inr (Or.inr ⟨hYS, hYT⟩)) hYE hYE rfl hdim)
    hR hR

end Rows

end HibiLi.Proofs.Cov1

end
