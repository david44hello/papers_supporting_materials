/-
HibiLi/Proofs/RoundJClaims.lean — proofs of the in-text claims of paper v2.10 that Lean proved but did not state (or
stated too weakly) before: P1-P11, W1, W2, M1 of the round-J delta (rows in Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.VertexBijection
import HibiLi.Proofs.PyramidFacesIff
import HibiLi.Polytope.PyramidCounts
import HibiLi.Polytope.PyramidClassification
import HibiLi.Proofs.Lemma36
import HibiLi.Proofs.LUPiecewise
import HibiLi.Proofs.Prop31
import HibiLi.Polytope.SwitchDomains
import HibiLi.Polytope.TopCells
import HibiLi.Proofs.V060Claims
import HibiLi.Polytope.CarrierInterior
import HibiLi.Polytope.RefinementCover
import HibiLi.Proofs.Lemma44
import HibiLi.Proofs.Lemma45
import HibiLi.Proofs.SmallClaims
import HibiLi.Example21.OtherSwitches
import HibiLi.Proofs.Chain2Example
import HibiLi.Example21.CenterResult
import HibiLi.Proofs.QEPaper
import HibiLi.Proofs.Lemma45Full

namespace HibiLi.Proofs

open HibiLi Finset

/-! ### P1 -/

theorem rj_upperClosure_eq_setOf {P : Type*} [PartialOrder P] (A : Set P) :
    {r | ∃ p ∈ A, p ≤ r} = ((upperClosure A : UpperSet P) : Set P) := by
  ext r
  simp [mem_upperClosure]

theorem sec1_upper_antichain_bij_proved (P : Type*) [Fintype P] [PartialOrder P] :
    (∀ S : Set P, IsUpperSet S →
      IsAntichain (· ≤ ·) {p | Minimal (· ∈ S) p} ∧ {r | ∃ p ∈ {p | Minimal (· ∈ S) p}, p ≤ r} = S) ∧
    (∀ A : Set P, IsAntichain (· ≤ ·) A →
      IsUpperSet {r | ∃ p ∈ A, p ≤ r} ∧ {p | Minimal (· ∈ {r | ∃ p ∈ A, p ≤ r}) p} = A) ∧
    fNum (orderPolytope P) 0 = fNum (chainPolytope P) 0 := by
  refine ⟨fun S hS => ⟨setOfPred_minimal_antichain _, ?_⟩, fun A hA => ⟨?_, ?_⟩, sec1_same_vertices_proved P⟩
  · have h : ((upperClosure {p | Minimal (· ∈ S) p} : UpperSet P) : Set P) = S :=
      congrArg Subtype.val ((upperAntichainEquiv (P := P)).left_inv ⟨S, hS⟩)
    rw [rj_upperClosure_eq_setOf]
    exact h
  · exact fun a b hab ⟨p, hp, hpa⟩ => ⟨p, hp, hpa.trans hab⟩
  · have h : {p | Minimal (· ∈ ((upperClosure A : UpperSet P) : Set P)) p} = A :=
      congrArg Subtype.val ((upperAntichainEquiv (P := P)).right_inv ⟨A, hA⟩)
    rw [rj_upperClosure_eq_setOf]
    exact h

/-! ### P2 -/

theorem sec2_pyramid_faces_full_proved {ι : Type*} [Fintype ι] (Q : Set (ι → ℝ)) (hQ : IsPolytope Q)
    (o : ι → ℝ) (ho : o ∉ affineSpan ℝ Q) :
    (∀ F, IsFace (convexHull ℝ (insert o Q)) F ↔
      IsFace Q F ∨ F = {o} ∨ ∃ G, IsFace Q G ∧ F = convexHull ℝ (insert o G)) ∧
    (∀ G, IsFace Q G → adim (convexHull ℝ (insert o G)) = adim G + 1) ∧
    (∀ G, IsFace Q G → o ∉ G) ∧
    (∀ G, IsFace Q G → convexHull ℝ (insert o G) ∩ Q = G) ∧
    Set.InjOn (fun G => convexHull ℝ (insert o G)) {G | IsFace Q G} ∧
    (∀ G G', IsFace Q G → IsFace Q G' → convexHull ℝ (insert o G) ≠ G') ∧
    (∀ G, IsFace Q G → G ≠ {o}) ∧
    (∀ G, IsFace Q G → convexHull ℝ (insert o G) ≠ {o}) := by
  have notin : ∀ G, IsFace Q G → o ∉ G := fun G hG hoG =>
    ho (subset_affineSpan ℝ Q (hG.2.subset hoG))
  have apex_mem : ∀ G : Set (ι → ℝ), o ∈ convexHull ℝ (insert o G) := fun G =>
    subset_convexHull ℝ _ (Set.mem_insert o G)
  refine ⟨fun F => sec2_pyramid_faces_proved Q hQ o ho F, fun G hG => hG.pyramid_adim o ho, notin,
    fun G hG => pyramid_join_inter_base hQ hG o ho, pyramid_join_injective hQ o ho, ?_, ?_, ?_⟩
  · intro G G' _ hG' same
    exact notin G' hG' (same ▸ apex_mem G)
  · intro G hG same
    exact notin G hG (same ▸ Set.mem_singleton o)
  · intro G hG same
    obtain ⟨g, hg⟩ := hG.1
    have hgo : g ∈ ({o} : Set (ι → ℝ)) := same ▸ subset_convexHull ℝ _ (Set.mem_insert_of_mem o hg)
    rw [Set.mem_singleton_iff] at hgo
    exact notin G hG (hgo ▸ hg)

/-! ### Points of the domains -/

section Domains

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

theorem rj_zero_mem_B' : (0 : s.P' → ℝ) ∈ s.B :=
  ⟨fun _ _ => le_rfl, fun _ _ => ⟨le_rfl, zero_le_one⟩, fun _ _ _ _ _ => le_rfl,
    fun _ _ _ _ _ _ => by simp, fun _ _ _ => by simp⟩

theorem rj_zero_mem_domL (K : Finset s.P') : (0 : s.P' → ℝ) ∈ s.domL K := by
  have h0 : ∀ K' : Finset s.P', s.chainSum K' 0 = 0 := fun K' => by simp [Switch.chainSum]
  refine ⟨rj_zero_mem_B' s, ?_⟩
  rw [h0]
  obtain ⟨K0, hK0⟩ := s.lowBranches_nonempty
  exact le_antisymm (Finset.sup'_le _ _ fun K' _ => (h0 K').le)
    ((h0 K0).symm.le.trans (Finset.le_sup' (fun K => s.chainSum K 0) hK0))

/-- The point with `x_p = 0` on `I` and `y_r = 1` on `J`. -/
noncomputable def rj_jPoint : s.P' → ℝ := fun p => by classical exact if p.1 ∈ s.I then 0 else 1

theorem rj_jPoint_mem_B : rj_jPoint s ∈ s.B := by
  classical
  have zero_on : ∀ K : Finset s.P', (↑K ⊆ s.I') → ∑ p ∈ K, rj_jPoint s p = 0 := fun K hK =>
    Finset.sum_eq_zero fun p hp => by simp [rj_jPoint, show p.1 ∈ s.I from hK hp]
  refine ⟨fun p hp => ?_, fun r hr => ?_, fun r r' hr hr' _ => ?_, fun r hr K hK _ _ => ?_, fun K hK _ => ?_⟩
  · simp [rj_jPoint, show p.1 ∈ s.I from hp]
  · simp [rj_jPoint, show r.1 ∉ s.I from hr]
  · simp [rj_jPoint, show r.1 ∉ s.I from hr, show r'.1 ∉ s.I from hr']
  · rw [zero_on K hK]
    simp [rj_jPoint, show r.1 ∉ s.I from hr]
  · rw [zero_on K hK]
    norm_num

theorem rj_jPoint_mem_domU (j : Option s.P') (hj : j ∈ s.upBranches) : rj_jPoint s ∈ s.domU j := by
  classical
  have hval : ∀ j ∈ s.upBranches, s.upVal j (rj_jPoint s) = 1 := by
    intro j hj
    rcases mem_upBranches s hj with rfl | ⟨r, hr, rfl⟩
    · rfl
    · have hrI : r.1 ∉ s.I := fun hrI => s.q_notMem (s.isLowerSet hr.le hrI)
      simp [Switch.upVal, rj_jPoint, hrI]
  refine ⟨rj_jPoint_mem_B s, ?_⟩
  rw [hval j hj]
  exact le_antisymm ((Finset.inf'_le (fun j => s.upVal j (rj_jPoint s)) hj).trans (hval j hj).le)
    (Finset.le_inf' _ _ fun j hj => (hval j hj).ge)

theorem rj_affineSpan_eq_top_of_adim {X : Set (s.P' → ℝ)} (hne : X.Nonempty) (h : adim X = Fintype.card s.P') :
    affineSpan ℝ X = ⊤ := by
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty (k := ℝ) (V := s.P' → ℝ)
    (P := s.P' → ℝ) hne]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fintype_fun_eq_card]
  exact h

theorem rj_cellS_props {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS) : Convex ℝ C ∧ C.Nonempty ∧ C ⊆ s.B := by
  obtain ⟨K, hK, _, hf⟩ := hC
  exact ⟨hf.2.convex (s.domL_isPolytope K hK).convex, hf.1, fun u hu => (hf.2.subset hu).1⟩

theorem rj_cellT_props {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsT) : Convex ℝ C ∧ C.Nonempty ∧ C ⊆ s.B := by
  obtain ⟨j, hj, _, hf⟩ := hC
  exact ⟨hf.2.convex (s.domU_isPolytope j hj).convex, hf.1, fun u hu => (hf.2.subset hu).1⟩

theorem rj_cell_props {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) :
    Convex ℝ C ∧ C.Nonempty ∧ C ⊆ s.B := by
  rcases hC with hC | hC | ⟨hne, A, hA, D, hD, rfl⟩
  · exact rj_cellS_props s hC
  · exact rj_cellT_props s hC
  · exact ⟨(rj_cellS_props s hA).1.inter (rj_cellT_props s hD).1, hne, fun u hu => (rj_cellS_props s hA).2.2 hu.1⟩

end Domains

/-! ### P3 -/

theorem sec3_maximal_cells_full_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (C : Set (s.P' → ℝ)) :
    ((C ∈ s.cellsS ∧ ∀ C' ∈ s.cellsS, C ⊆ C' → C' = C) ↔
      ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ C = s.domL K) ∧
    ((C ∈ s.cellsS ∧ ∀ C' ∈ s.cellsS, C ⊆ C' → C' = C) ↔ C ∈ s.cellsS ∧ adim C = Fintype.card s.P') ∧
    ((C ∈ s.cellsT ∧ ∀ C' ∈ s.cellsT, C ⊆ C' → C' = C) ↔
      ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ C = s.domU j) ∧
    ((C ∈ s.cellsT ∧ ∀ C' ∈ s.cellsT, C ⊆ C' → C' = C) ↔ C ∈ s.cellsT ∧ adim C = Fintype.card s.P') := by
  have maxS : (C ∈ s.cellsS ∧ ∀ C' ∈ s.cellsS, C ⊆ C' → C' = C) ↔
      ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ C = s.domL K := by
    constructor
    · rintro ⟨⟨K, hK, hdim, hface⟩, hmax⟩
      have hA : s.domL K ∈ s.cellsS := ⟨K, hK, hdim, IsFace.refl (hface.1.mono hface.2.subset)⟩
      exact ⟨K, hK, hdim, (hmax _ hA hface.2.subset).symm⟩
    · rintro ⟨K, hK, hdim, rfl⟩
      have hA : s.domL K ∈ s.cellsS := ⟨K, hK, hdim, IsFace.refl ⟨0, rj_zero_mem_domL s K⟩⟩
      refine ⟨hA, fun C' hC' hsub => ?_⟩
      obtain ⟨-, -, -, -, hmaxD⟩ := (sec3_S_paper_def_proved s (s.domL K)).1.mp ⟨hA, hdim⟩
      obtain ⟨hconv, -, hCB⟩ := rj_cellS_props s hC'
      obtain ⟨K', -, -, hface'⟩ := hC'
      exact hmaxD C' hsub hCB hconv
        ⟨chainSumAff s K', fun u hu => by rw [chainSumAff_apply]; exact (hface'.2.subset hu).2⟩
  have maxT : (C ∈ s.cellsT ∧ ∀ C' ∈ s.cellsT, C ⊆ C' → C' = C) ↔
      ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ C = s.domU j := by
    constructor
    · rintro ⟨⟨j, hj, hdim, hface⟩, hmax⟩
      have hA : s.domU j ∈ s.cellsT := ⟨j, hj, hdim, IsFace.refl (hface.1.mono hface.2.subset)⟩
      exact ⟨j, hj, hdim, (hmax _ hA hface.2.subset).symm⟩
    · rintro ⟨j, hj, hdim, rfl⟩
      have hA : s.domU j ∈ s.cellsT := ⟨j, hj, hdim, IsFace.refl ⟨rj_jPoint s, rj_jPoint_mem_domU s j hj⟩⟩
      refine ⟨hA, fun C' hC' hsub => ?_⟩
      obtain ⟨-, -, -, -, hmaxD⟩ := (sec3_S_paper_def_proved s (s.domU j)).2.mp ⟨hA, hdim⟩
      obtain ⟨hconv, -, hCB⟩ := rj_cellT_props s hC'
      obtain ⟨j', -, -, hface'⟩ := hC'
      exact hmaxD C' hsub hCB hconv
        ⟨upAff s j', fun u hu => by rw [upAff_apply]; exact (hface'.2.subset hu).2⟩
  have fullS : (∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ C = s.domL K) ↔
      C ∈ s.cellsS ∧ adim C = Fintype.card s.P' := by
    constructor
    · rintro ⟨K, hK, hdim, rfl⟩
      exact ⟨⟨K, hK, hdim, IsFace.refl ⟨0, rj_zero_mem_domL s K⟩⟩, hdim⟩
    · rintro ⟨⟨K, hK, hdim, hface⟩, hCdim⟩
      exact ⟨K, hK, hdim, hface.eq_of_adim_eq (hCdim.trans hdim.symm)⟩
  have fullT : (∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ C = s.domU j) ↔
      C ∈ s.cellsT ∧ adim C = Fintype.card s.P' := by
    constructor
    · rintro ⟨j, hj, hdim, rfl⟩
      exact ⟨⟨j, hj, hdim, IsFace.refl ⟨rj_jPoint s, rj_jPoint_mem_domU s j hj⟩⟩, hdim⟩
    · rintro ⟨⟨j, hj, hdim, hface⟩, hCdim⟩
      exact ⟨j, hj, hdim, hface.eq_of_adim_eq (hCdim.trans hdim.symm)⟩
  exact ⟨maxS, maxS.trans fullS, maxT, maxT.trans fullT⟩

/-! ### P4 -/

theorem sec3_domains_polytope_affine_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ K ∈ s.lowBranches,
      s.domL K = {u | u ∈ s.B ∧ ∀ K' ∈ s.lowBranches, s.chainSum K' u ≤ s.chainSum K u} ∧
      IsPolytope (s.domL K) ∧
      ∃ g : (s.P' → ℝ) →ᵃ[ℝ] ℝ, (∀ u, g u = s.chainSum K u) ∧ ∀ u ∈ s.domL K, s.L u = g u) ∧
    (∀ j ∈ s.upBranches,
      s.domU j = {u | u ∈ s.B ∧ ∀ j' ∈ s.upBranches, s.upVal j u ≤ s.upVal j' u} ∧
      IsPolytope (s.domU j) ∧
      ∃ g : (s.P' → ℝ) →ᵃ[ℝ] ℝ, (∀ u, g u = s.upVal j u) ∧ ∀ u ∈ s.domU j, s.U u = g u) := by
  refine ⟨fun K hK => ⟨?_, s.domL_isPolytope K hK, chainSumAff s K, chainSumAff_apply s K,
    fun u hu => hu.2.trans (chainSumAff_apply s K u).symm⟩,
    fun j hj => ⟨?_, s.domU_isPolytope j hj, upAff s j, upAff_apply s j,
    fun u hu => hu.2.trans (upAff_apply s j u).symm⟩⟩
  · ext u
    constructor
    · rintro ⟨hu, hL⟩
      exact ⟨hu, fun K' hK' => (Finset.le_sup' (fun K => s.chainSum K u) hK').trans hL.le⟩
    · rintro ⟨hu, hle⟩
      exact ⟨hu, le_antisymm (Finset.sup'_le _ _ hle) (Finset.le_sup' (fun K => s.chainSum K u) hK)⟩
  · ext u
    constructor
    · rintro ⟨hu, hU⟩
      exact ⟨hu, fun j' hj' => hU.symm.le.trans (Finset.inf'_le (fun j => s.upVal j u) hj')⟩
    · rintro ⟨hu, hle⟩
      exact ⟨hu, le_antisymm (Finset.inf'_le (fun j => s.upVal j u) hj) (Finset.le_inf' _ _ hle)⟩

/-! ### P5 -/

theorem sec3_full_domains_eq_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ K ∈ s.lowBranches, ∀ K' ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' →
      s.domL K ⊆ s.domL K' → s.chainSum K = s.chainSum K' ∧ s.domL K = s.domL K') ∧
    (∀ j ∈ s.upBranches, ∀ j' ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' →
      s.domU j ⊆ s.domU j' → s.upVal j = s.upVal j' ∧ s.domU j = s.domU j') := by
  constructor
  · intro K _ K' _ hdim hsub
    have heq : Set.EqOn (chainSumAff s K) (chainSumAff s K') (s.domL K) := fun u hu => by
      rw [chainSumAff_apply, chainSumAff_apply, ← hu.2, (hsub hu).2]
    have hall := AffineMap.eqOn_affineSpan heq
    rw [rj_affineSpan_eq_top_of_adim s ⟨0, rj_zero_mem_domL s K⟩ hdim, AffineSubspace.top_coe] at hall
    have hfun : s.chainSum K = s.chainSum K' := funext fun u => by
      rw [← chainSumAff_apply, ← chainSumAff_apply]
      exact hall (Set.mem_univ u)
    refine ⟨hfun, ?_⟩
    unfold Switch.domL
    rw [hfun]
  · intro j hj j' _ hdim hsub
    have heq : Set.EqOn (upAff s j) (upAff s j') (s.domU j) := fun u hu => by
      rw [upAff_apply, upAff_apply, ← hu.2, (hsub hu).2]
    have hall := AffineMap.eqOn_affineSpan heq
    rw [rj_affineSpan_eq_top_of_adim s ⟨rj_jPoint s, rj_jPoint_mem_domU s j hj⟩ hdim, AffineSubspace.top_coe] at hall
    have hfun : s.upVal j = s.upVal j' := funext fun u => by
      rw [← upAff_apply, ← upAff_apply]
      exact hall (Set.mem_univ u)
    refine ⟨hfun, ?_⟩
    unfold Switch.domU
    rw [hfun]

/-! ### P6 -/

theorem sec3_full_domains_cover_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ u ∈ s.B, ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ u ∈ s.domL K) ∧
    (∀ u ∈ s.B, ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ u ∈ s.domU j) := by
  obtain ⟨cS, cT, cR, hS, hT, -, subS, subT, -⟩ := sec3_subdivisions_proved s
  constructor
  · intro u hu
    rw [← subS.2.1] at hu
    obtain ⟨C, hC, huC⟩ := hu
    rw [hS] at hC
    obtain ⟨K, hK, hdim, hface⟩ := hC
    exact ⟨K, hK, hdim, hface.2.subset huC⟩
  · intro u hu
    rw [← subT.2.1] at hu
    obtain ⟨C, hC, huC⟩ := hu
    rw [hT] at hC
    obtain ⟨j, hj, hdim, hface⟩ := hC
    exact ⟨j, hj, hdim, hface.2.subset huC⟩

/-! ### P7 -/

/-- A face of `body` that contains a relative-interior point of `C ⊆ body` contains `C`. -/
theorem rj_face_contains_of_relint {ι : Type*} [Fintype ι] {body F C : Set (ι → ℝ)} (hF : IsFace body F)
    (hCB : C ⊆ body) {x : ι → ℝ} (hxF : x ∈ F) (hxC : x ∈ intrinsicInterior ℝ C) : C ⊆ F := by
  obtain ⟨l, hl⟩ := hF.2 hF.1
  rw [hl] at hxF ⊢
  have hconst := linear_eq_of_intrinsicInterior_max hxC l (fun y hy => hxF.2 y (hCB hy))
  intro y hy
  exact ⟨hCB hy, fun z hz => (hxF.2 z hz).trans (hconst y hy).ge⟩

theorem sec3_carrier_unique_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (C : Set (s.P' → ℝ)) (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) (E : Set (s.P' → ℝ))
    (hE : IsCarrier s.B E C) :
    ∀ E', IsFace s.B E' → ((intrinsicInterior ℝ E' ∩ intrinsicInterior ℝ C).Nonempty ↔ E' = E) := by
  obtain ⟨hconv, hne, hsub⟩ := rj_cell_props s hC
  obtain ⟨huniq, hrel⟩ := sec3_carrier_proved s C hC
  intro E' hE'
  constructor
  · rintro ⟨x, hxE', hxC⟩
    have hCE' : C ⊆ E' := rj_face_contains_of_relint hE' hsub (intrinsicInterior_subset hxE') hxC
    exact huniq.unique (isCarrier_of_subset_of_intrinsicInterior hE' hCE'
      ⟨x, intrinsicInterior_subset hxC, hxE'⟩) hE
  · rintro rfl
    obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior hconv hne
    exact ⟨x, hrel _ hE hx, hx⟩

/-! ### P8 -/

section P8

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

theorem rj_a_mem_I : x.a ∈ x.toSwitch.I := fun h => lt_irrefl _ (x.a_lt_q.trans_le h)
theorem rj_b_mem_I : x.b ∈ x.toSwitch.I := fun h => lt_irrefl _ (x.b_lt_q.trans_le h)
theorem rj_g_notMem_I : x.g' ∉ x.toSwitch.I := fun h => h x.q_covby_g'.lt.le
theorem rj_h_notMem_I : x.h' ∉ x.toSwitch.I := fun h => h x.q_covby_h'.lt.le

theorem rj_notSpecial_iff (p : x.toSwitch.P') :
    p ∉ x.special ↔ p.1 ≠ x.a ∧ p.1 ≠ x.b ∧ p.1 ≠ x.g' ∧ p.1 ≠ x.h' := by
  rw [Lemma45.not_special x]
  simp only [ne_eq, Subtype.ext_iff, XSwitch.pa, XSwitch.pb, XSwitch.pg, XSwitch.ph]

open Classical in
theorem sec4_E0_inequality_proved :
    ∀ u ∈ x.toSwitch.B,
      0 ≤ (∑ p ∈ univ.filter (fun p : x.toSwitch.P' => p.1 ∈ x.toSwitch.I ∧ p.1 ≠ x.a ∧ p.1 ≠ x.b), u p) +
        ∑ r ∈ univ.filter (fun r : x.toSwitch.P' => r.1 ∉ x.toSwitch.I ∧ r.1 ≠ x.g' ∧ r.1 ≠ x.h'), (1 - u r) ∧
      ((∑ p ∈ univ.filter (fun p : x.toSwitch.P' => p.1 ∈ x.toSwitch.I ∧ p.1 ≠ x.a ∧ p.1 ≠ x.b), u p) +
        ∑ r ∈ univ.filter (fun r : x.toSwitch.P' => r.1 ∉ x.toSwitch.I ∧ r.1 ≠ x.g' ∧ r.1 ≠ x.h'), (1 - u r) = 0 ↔
        x.zeta u = x.zeta x.u0) := by
  intro u hu
  have n1 : ∀ p ∈ univ.filter (fun p : x.toSwitch.P' => p.1 ∈ x.toSwitch.I ∧ p.1 ≠ x.a ∧ p.1 ≠ x.b),
      0 ≤ u p := fun p hp => hu.1 p (mem_filter.mp hp).2.1
  have n2 : ∀ r ∈ univ.filter (fun r : x.toSwitch.P' => r.1 ∉ x.toSwitch.I ∧ r.1 ≠ x.g' ∧ r.1 ≠ x.h'),
      0 ≤ 1 - u r := fun r hr => sub_nonneg.mpr (hu.2.1 r (mem_filter.mp hr).2.1).2
  refine ⟨add_nonneg (sum_nonneg n1) (sum_nonneg n2), ?_⟩
  rw [add_eq_zero_iff_of_nonneg (sum_nonneg n1) (sum_nonneg n2), sum_eq_zero_iff_of_nonneg n1,
    sum_eq_zero_iff_of_nonneg n2, funext_iff]
  constructor
  · rintro ⟨h1, h2⟩ ⟨p, hs⟩
    obtain ⟨ha, hb, hg, hh⟩ := (rj_notSpecial_iff x p).mp hs
    show u p = x.u0 p
    by_cases hp : p.1 ∈ x.toSwitch.I
    · rw [Lemma45.u0_I x hs hp]
      exact h1 p (mem_filter.mpr ⟨mem_univ _, hp, ha, hb⟩)
    · rw [Lemma45.u0_J x hs hp]
      have := h2 p (mem_filter.mpr ⟨mem_univ _, hp, hg, hh⟩)
      linarith
  · intro h
    have hval : ∀ p, p ∉ x.special → u p = x.u0 p := fun p hs => h ⟨p, hs⟩
    constructor
    · intro p hp
      obtain ⟨-, hpI, ha, hb⟩ := mem_filter.mp hp
      have hs : p ∉ x.special := (rj_notSpecial_iff x p).mpr ⟨ha, hb,
        fun e => rj_g_notMem_I x (e ▸ hpI), fun e => rj_h_notMem_I x (e ▸ hpI)⟩
      rw [hval p hs, Lemma45.u0_I x hs hpI]
    · intro r hr
      obtain ⟨-, hrI, hg, hh⟩ := mem_filter.mp hr
      have hs : r ∉ x.special := (rj_notSpecial_iff x r).mpr
        ⟨fun e => hrI (e ▸ rj_a_mem_I x), fun e => hrI (e ▸ rj_b_mem_I x), hg, hh⟩
      rw [hval r hs, Lemma45.u0_J x hs hrI, sub_self]

end P8

/-! ### P9 -/

theorem sec5_contains_X_five_le_proved (P : Type*) [Fintype P] [PartialOrder P] (hX : ContainsX P) :
    5 ≤ Fintype.card P := by
  obtain ⟨a, b, c, g, h, hX⟩ := hX
  obtain ⟨f, -⟩ := sec1_X_copy_induced_proved (a := a) (b := b) (c := c) (g := g) (h := h) hX
  have hle := Fintype.card_le_of_embedding f.toEmbedding
  have h5 : Fintype.card XElem = 5 := by decide
  omega

/-! ### P10 -/

theorem sec5_minimal_switch_faces_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    ((∀ p ∈ s.I, ¬ p < s.q) →
      (∀ u, s.L u = 0) ∧ AffineOn s.L s.B ∧ s.cellsS = {C | IsFace s.B C} ∧ cellPoly s.cellsS = facePoly s.B ∧
      s.cellsR = s.cellsT ∧ facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0) ∧
    ((∀ p : P, ¬ s.q < p) →
      (∀ u, s.U u = 1) ∧ AffineOn s.U s.B ∧ s.cellsT = {C | IsFace s.B C} ∧ cellPoly s.cellsT = facePoly s.B ∧
      s.cellsR = s.cellsS ∧ facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0) ∧
    (∀ s' : Switch Chain2, s'.I = ∅ → s'.q = 0 →
      (∀ u, s'.L u = 0) ∧ chainOrderPolytope Chain2 (insert s'.q s'.I) = orderPolytope Chain2) := by
  refine ⟨fun hI => ?_, fun hmax => ?_, fun s' hI hq => ?_⟩
  · have hmin : ∀ p : P, ¬ p < s.q := fun p hp => hI p (s.q_minimal p hp) hp
    have hS := s.cellsS_eq_faces_of_minimal hmin
    have hR := s.cellsR_eq_T_of_S_faces hS
    refine ⟨s.L_eq_zero_of_minimal hmin, ⟨AffineMap.const ℝ (s.P' → ℝ) (0 : ℝ), fun u _ => by
      rw [AffineMap.const_apply]; exact s.L_eq_zero_of_minimal hmin u⟩, hS, by rw [hS]; rfl, hR, ?_⟩
    rw [hR, hS, show cellPoly {C | IsFace s.B C} = facePoly s.B from rfl]
    ring
  · have hT := s.cellsT_eq_faces_of_maximal hmax
    have hR := s.cellsR_eq_S_of_T_faces hT
    refine ⟨s.U_eq_one_of_maximal hmax, ⟨AffineMap.const ℝ (s.P' → ℝ) (1 : ℝ), fun u _ => by
      rw [AffineMap.const_apply]; exact s.U_eq_one_of_maximal hmax u⟩, hT, by rw [hT]; rfl, hR, ?_⟩
    rw [hR, hT, show cellPoly {C | IsFace s.B C} = facePoly s.B from rfl]
    ring
  · have hmin : ∀ p : Chain2, ¬ p < s'.q := by rw [hq]; decide
    refine ⟨s'.L_eq_zero_of_minimal hmin, ?_⟩
    rw [hI, hq, show (insert (0 : Chain2) (∅ : Set Chain2)) = {0} from by ext; simp]
    exact chainOrderPolytope_chain2_zero

/-! ### P11 -/

section P11

open Example21 CenterGeometry CenterSwitch

theorem sec5_center_A0_A1_proved :
    (∀ u, center.L u = max 0 (max (u canonical.pa) (u canonical.pb))) ∧
    center.domL ∅ = {u | u ∈ center.B ∧ u canonical.pa = 0 ∧ u canonical.pb = 0} ∧
    adim (center.domL ∅) ≠ Fintype.card center.P' ∧
    (∀ u, center.U u = min (min (u canonical.pg) (u canonical.ph)) 1) ∧
    center.domU none = {u | u ∈ center.B ∧ u canonical.pg = 1 ∧ u canonical.ph = 1} ∧
    adim (center.domU none) ≠ Fintype.card center.P' := by
  have h0 : (∅ : Finset Coord) ∈ center.lowBranches := by
    classical
    simp [Switch.lowBranches, IsChainSet]
  have hL : ∀ u, center.L u = max 0 (max (u canonical.pa) (u canonical.pb)) := by
    intro u
    unfold Switch.L
    apply le_antisymm
    · apply Finset.sup'_le
      intro K hK
      rcases lowBranches_cases hK with rfl | rfl | rfl
      · simp [Switch.chainSum]
      · simp [Switch.chainSum]
      · simp [Switch.chainSum]
    · refine max_le ?_ (max_le ?_ ?_)
      · simpa only [Switch.chainSum, Finset.sum_empty] using Finset.le_sup' (center.chainSum · u) h0
      · simpa only [Switch.chainSum, Finset.sum_singleton] using
          Finset.le_sup' (center.chainSum · u) canonical.singleton_pa_mem
      · simpa only [Switch.chainSum, Finset.sum_singleton] using
          Finset.le_sup' (center.chainSum · u) canonical.singleton_pb_mem
  have hU : ∀ u, center.U u = min (min (u canonical.pg) (u canonical.ph)) 1 := by
    intro u
    apply le_antisymm
    · refine le_min (le_min ?_ ?_) ?_
      · exact Finset.inf'_le (center.upVal · u) (upper_valid false)
      · exact Finset.inf'_le (center.upVal · u) (upper_valid true)
      · exact Finset.inf'_le (center.upVal · u) (none_mem_upBranches center)
    · apply Finset.le_inf'
      intro j hj
      rcases upBranches_cases hj with rfl | rfl | rfl
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (min_le_left _ _)
      · exact (min_le_left _ _).trans (min_le_right _ _)
  have hA0 : center.domL ∅ = {u | u ∈ center.B ∧ u canonical.pa = 0 ∧ u canonical.pb = 0} := by
    ext u
    simp only [Switch.domL, Set.mem_ofPred_eq, hL, Switch.chainSum, Finset.sum_empty]
    constructor
    · rintro ⟨hu, h⟩
      obtain ⟨ha, hb, -⟩ := (mem_B_iff u).mp hu
      have h1 : max (u canonical.pa) (u canonical.pb) ≤ 0 := (le_max_right _ _).trans h.le
      exact ⟨hu, le_antisymm ((le_max_left _ _).trans h1) ha, le_antisymm ((le_max_right _ _).trans h1) hb⟩
    · rintro ⟨hu, ha, hb⟩
      exact ⟨hu, by rw [ha, hb]; simp⟩
  have hA1 : center.domU none = {u | u ∈ center.B ∧ u canonical.pg = 1 ∧ u canonical.ph = 1} := by
    ext u
    simp only [Switch.domU, Set.mem_ofPred_eq, hU, Switch.upVal]
    constructor
    · rintro ⟨hu, h⟩
      obtain ⟨-, -, -, hg, hh⟩ := (mem_B_iff u).mp hu
      have h1 : 1 ≤ min (u canonical.pg) (u canonical.ph) := h.ge.trans (min_le_left _ _)
      exact ⟨hu, le_antisymm hg (h1.trans (min_le_left _ _)), le_antisymm hh (h1.trans (min_le_right _ _))⟩
    · rintro ⟨hu, hg, hh⟩
      exact ⟨hu, by rw [hg, hh]; simp⟩
  exact ⟨hL, hA0, domL_empty_not_full, hU, hA1, domU_none_not_full⟩

end P11

/-! ### W2 helpers: `L` (or `U`) affine on all of `B` -/

section W2

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

theorem rj_cellsS_eq_faces_of_affineOn_B (hL : AffineOn s.L s.B) : s.cellsS = {C | IsFace s.B C} := by
  have hBface : IsFace s.B s.B := IsFace.refl ⟨0, rj_zero_mem_B' s⟩
  obtain ⟨C, hC, hBC⟩ :=
    (lemma_3_6_cover_proved s s.B hBface s.B subset_rfl s.B_isPolytope.convex rfl).1 hL
  obtain ⟨⟨-, A, hA, rfl⟩, -⟩ := hC
  obtain ⟨K, hK, hdim, hface⟩ := hA
  have hKB : s.domL K = s.B :=
    Set.Subset.antisymm (fun u hu => hu.1) (hBC.trans (Set.inter_subset_left.trans hface.2.subset))
  ext C'
  constructor
  · rintro ⟨K', hK', hdim', hface'⟩
    have hsame := ((sec3_full_domains_eq_proved s).1 K' hK' K hK hdim' (fun u hu => hKB ▸ hu.1)).2
    rw [hsame, hKB] at hface'
    exact hface'
  · intro hC'
    exact ⟨K, hK, hdim, hKB ▸ hC'⟩

theorem rj_cellsT_eq_faces_of_affineOn_B (hU : AffineOn s.U s.B) : s.cellsT = {C | IsFace s.B C} := by
  have hBface : IsFace s.B s.B := IsFace.refl ⟨0, rj_zero_mem_B' s⟩
  obtain ⟨C, hC, hBC⟩ :=
    (lemma_3_6_cover_proved s s.B hBface s.B subset_rfl s.B_isPolytope.convex rfl).2 hU
  obtain ⟨⟨-, A, hA, rfl⟩, -⟩ := hC
  obtain ⟨j, hj, hdim, hface⟩ := hA
  have hjB : s.domU j = s.B :=
    Set.Subset.antisymm (fun u hu => hu.1) (hBC.trans (Set.inter_subset_left.trans hface.2.subset))
  ext C'
  constructor
  · rintro ⟨j', hj', hdim', hface'⟩
    have hsame := ((sec3_full_domains_eq_proved s).2 j' hj' j hj hdim' (fun u hu => hjB ▸ hu.1)).2
    rw [hsame, hjB] at hface'
    exact hface'
  · intro hC'
    exact ⟨j, hj, hdim, hjB ▸ hC'⟩

end W2

/-! ### W2 -/

theorem sec3_chain2_cells_faces_proved :
    ∀ s : Switch Chain2, (s.I = ∅ ∧ s.q = 0) ∨ (s.I = {0} ∧ s.q = 1) →
      AffineOn s.L s.B ∧ AffineOn s.U s.B ∧
      s.cellsS = {C | IsFace s.B C} ∧ s.cellsT = {C | IsFace s.B C} ∧ s.cellsR = {C | IsFace s.B C} ∧
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0 := by
  have finish : ∀ s : Switch Chain2, AffineOn s.L s.B → AffineOn s.U s.B →
      AffineOn s.L s.B ∧ AffineOn s.U s.B ∧
      s.cellsS = {C | IsFace s.B C} ∧ s.cellsT = {C | IsFace s.B C} ∧ s.cellsR = {C | IsFace s.B C} ∧
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT = 0 := by
    intro s hL hU
    have hS := rj_cellsS_eq_faces_of_affineOn_B s hL
    have hT := rj_cellsT_eq_faces_of_affineOn_B s hU
    have hR : s.cellsR = {C | IsFace s.B C} := (s.cellsR_eq_S_of_T_faces hT).trans hS
    refine ⟨hL, hU, hS, hT, hR, ?_⟩
    rw [hR, hS, hT, show cellPoly {C | IsFace s.B C} = facePoly s.B from rfl]
    ring
  intro s hs
  rcases hs with ⟨hI, hq⟩ | ⟨hI, hq⟩
  · have hmin : ∀ p : Chain2, ¬ p < s.q := by rw [hq]; decide
    refine finish s ⟨AffineMap.const ℝ (s.P' → ℝ) (0 : ℝ), fun u _ => by
      rw [AffineMap.const_apply]; exact s.L_eq_zero_of_minimal hmin u⟩ ?_
    let r : s.P' := ⟨1, by rw [hq]; decide⟩
    have hrmem : some r ∈ s.upBranches := some_mem_upBranches s (show s.q < (1 : Chain2) by rw [hq]; decide)
    have key : ∀ t : Chain2, t ≠ 0 → t = 1 := by decide
    refine ⟨(LinearMap.proj (R := ℝ) (φ := fun _ : s.P' => ℝ) r).toAffineMap, fun u hu => ?_⟩
    have hle1 : u r ≤ 1 := (hu.2.1 r (fun h => by
      have h' : r.1 ∈ s.I := h
      rw [hI] at h'
      simp at h')).2
    show s.U u = u r
    apply le_antisymm (Finset.inf'_le (fun j => s.upVal j u) hrmem)
    refine Finset.le_inf' _ _ fun j hj => ?_
    rcases mem_upBranches s hj with rfl | ⟨r', hr', rfl⟩
    · exact hle1
    · have hr'r : r' = r := Subtype.ext (key r'.1 (hq ▸ r'.2))
      rw [hr'r]
  · have hs : s = chain2Switch := by
      cases s
      simp only at hI hq
      subst hI hq
      rfl
    subst hs
    let p0 : chain2Switch.P' := ⟨0, by decide⟩
    exact finish chain2Switch
      ⟨(LinearMap.proj (R := ℝ) (φ := fun _ : chain2Switch.P' => ℝ) p0).toAffineMap,
        fun u hu => chain2Switch_L u hu p0⟩
      ⟨AffineMap.const ℝ (chain2Switch.P' → ℝ) (1 : ℝ), fun u _ => by
        rw [AffineMap.const_apply]; exact chain2Switch_U u⟩

/-! ### W1 -/

theorem sec3_strict_point_v200_proved (P : Type*) [Fintype P] [PartialOrder P] (I : Set P) [DecidablePred (· ∈ I)] (m : ℕ)
    (e : Fin m ≃ {r : P // r ∉ I}) (hext : ∀ i j : Fin m, (e i : P) < e j → i < j) :
    let pt : P → ℝ := fun p =>
      if hp : p ∈ I then 1 / (4 * Fintype.card P) else 1 / 2 + (((e.symm ⟨p, hp⟩ : ℕ) : ℝ) + 1) / (4 * m)
    (∀ p ∈ I, 0 < pt p) ∧ (∀ r ∉ I, 0 < pt r ∧ pt r < 1) ∧
    (∀ r r', r ∉ I → r' ∉ I → r < r' → pt r < pt r') ∧
    (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, pt p ≤ 1 / 4) ∧
    (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, pt p ≤ (I.ncard : ℝ) / (4 * Fintype.card P)) ∧
    (I.ncard : ℝ) / (4 * Fintype.card P) ≤ 1 / 4 ∧
    (∀ r ∉ I, ∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → (∀ p ∈ K, p < r) → ∑ p ∈ K, pt p < pt r) ∧
    (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, pt p < 1) := by
  intro pt
  have hvalI : ∀ p (hp : p ∈ I), pt p = 1 / (4 * Fintype.card P) := fun p hp => by
    simp only [pt, dite_eq_left hp]
  have hvalJ : ∀ r (hr : r ∉ I), pt r = 1 / 2 + (((e.symm ⟨r, hr⟩ : ℕ) : ℝ) + 1) / (4 * m) := fun r hr => by
    simp only [pt, dite_eq_right hr]
  have hidx : ∀ r (hr : r ∉ I), (((e.symm ⟨r, hr⟩ : ℕ) : ℝ) + 1) ≤ m ∧ (0 : ℝ) < m := fun r hr => by
    have h := (e.symm ⟨r, hr⟩).isLt
    exact ⟨by exact_mod_cast Nat.succ_le_of_lt h, by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) h⟩
  have hJ : ∀ r (hr : r ∉ I), 1 / 2 < pt r ∧ pt r ≤ 3 / 4 := fun r hr => by
    obtain ⟨hle, hm⟩ := hidx r hr
    rw [hvalJ r hr]
    have hpos : 0 < (((e.symm ⟨r, hr⟩ : ℕ) : ℝ) + 1) / (4 * m) := div_pos (by positivity) (by linarith)
    have hquarter : (((e.symm ⟨r, hr⟩ : ℕ) : ℝ) + 1) / (4 * m) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    constructor <;> linarith
  have hsum : ∀ K : Finset P, (↑K ⊆ I) → ∑ p ∈ K, pt p ≤ 1 / 4 := by
    intro K hK
    rw [Finset.sum_congr rfl fun p hp => hvalI p (hK (Finset.mem_coe.2 hp)), Finset.sum_const, nsmul_eq_mul]
    have hcard : (K.card : ℝ) ≤ Fintype.card P := by exact_mod_cast Finset.card_le_univ K
    rcases Nat.eq_zero_or_pos (Fintype.card P) with h0 | hpos
    · simp [h0]
    · have hP : (0 : ℝ) < Fintype.card P := by exact_mod_cast hpos
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      linarith
  have hcardI : (I.ncard : ℝ) ≤ Fintype.card P := by
    have h := Set.ncard_le_ncard (Set.subset_univ I)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  have hbound : ∀ K : Finset P, (↑K ⊆ I) → ∑ p ∈ K, pt p ≤ (I.ncard : ℝ) / (4 * Fintype.card P) := by
    intro K hK
    rw [Finset.sum_congr rfl fun p hp => hvalI p (hK (Finset.mem_coe.2 hp)), Finset.sum_const, nsmul_eq_mul,
      mul_one_div]
    have hKI : (K.card : ℝ) ≤ I.ncard := by
      have h := Set.ncard_le_ncard hK (Set.toFinite I)
      rw [Set.ncard_coe_finset] at h
      exact_mod_cast h
    gcongr
  have hquarter : (I.ncard : ℝ) / (4 * Fintype.card P) ≤ 1 / 4 := by
    rcases Nat.eq_zero_or_pos (Fintype.card P) with h0 | hpos
    · simp [h0]
    · have hP : (0 : ℝ) < Fintype.card P := by exact_mod_cast hpos
      rw [div_le_iff₀ (by linarith)]
      linarith
  refine ⟨fun p hp => ?_, fun r hr => ?_, fun r r' hr hr' hlt => ?_, fun K hK _ => hsum K hK,
    fun K hK _ => hbound K hK, hquarter,
    fun r hr K hK _ _ => ?_, fun K hK _ => ?_⟩
  · rw [hvalI p hp]
    have : (0 : ℝ) < Fintype.card P := by
      exact_mod_cast Fintype.card_pos_iff.2 ⟨p⟩
    positivity
  · have := hJ r hr
    constructor <;> linarith
  · rw [hvalJ r hr, hvalJ r' hr']
    have hm := (hidx r hr).2
    have hij : e.symm ⟨r, hr⟩ < e.symm ⟨r', hr'⟩ :=
      hext _ _ (by simp only [Equiv.apply_symm_apply]; exact hlt)
    have hij' : ((e.symm ⟨r, hr⟩ : ℕ) : ℝ) < ((e.symm ⟨r', hr'⟩ : ℕ) : ℝ) := by exact_mod_cast hij
    have hdiv := (div_lt_div_iff_of_pos_right (by linarith : (0 : ℝ) < 4 * m)).2
      (by linarith : ((e.symm ⟨r, hr⟩ : ℕ) : ℝ) + 1 < ((e.symm ⟨r', hr'⟩ : ℕ) : ℝ) + 1)
    linarith
  · have := hJ r hr
    have := hsum K hK
    linarith
  · have := hsum K hK
    linarith

/-! ### M1 -/

section M1

open Filter Topology Lemma45 Lemma45Full

theorem rj_exists_pos_of_eventually {p : ℝ → Prop} (h : ∀ᶠ t in 𝓝 (0 : ℝ), p t) : ∃ t, 0 < t ∧ p t := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ε / 2, half_pos hε, hball (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; exact half_lt_self hε)⟩

/-- A convex set and its intersection with a neighborhood of one of its points span the same affine subspace. -/
theorem rj_affineSpan_inter_nhds {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] {Q V : Set W}
    (hQ : Convex ℝ Q) {z : W} (hz : z ∈ Q) (hV : V ∈ 𝓝 z) : affineSpan ℝ (Q ∩ V) = affineSpan ℝ Q := by
  apply le_antisymm (affineSpan_mono ℝ Set.inter_subset_left)
  rw [affineSpan_le]
  intro q hq
  have hc : Tendsto (fun t : ℝ => AffineMap.lineMap z q t) (𝓝 0) (𝓝 z) :=
    (AffineMap.lineMap_continuous (p := z) (q := q)).tendsto' 0 z (AffineMap.lineMap_apply_zero z q)
  obtain ⟨t, ht0, htV, ht1⟩ := rj_exists_pos_of_eventually ((hc.eventually_mem hV).and (eventually_lt_nhds zero_lt_one))
  have hzS : z ∈ affineSpan ℝ (Q ∩ V) := subset_affineSpan ℝ _ ⟨hz, mem_of_mem_nhds hV⟩
  have hpS : AffineMap.lineMap z q t ∈ affineSpan ℝ (Q ∩ V) :=
    subset_affineSpan ℝ _ ⟨hQ.lineMap_mem hz hq ⟨ht0.le, ht1.le⟩, htV⟩
  have hdir := AffineSubspace.vsub_mem_direction hpS hzS
  rw [AffineMap.lineMap_vsub_left] at hdir
  have hdir' := Submodule.smul_mem _ t⁻¹ hdir
  rw [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul] at hdir'
  have hmem := AffineSubspace.vadd_mem_of_mem_direction hdir' hzS
  rwa [vsub_vadd] at hmem

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

theorem rj_zeta_mem_QEpaper {E : Set (x.toSwitch.P' → ℝ)} (hEB : E ⊆ x.toSwitch.B) {u : x.toSwitch.P' → ℝ}
    (hu : u ∈ E) : x.zeta u ∈ x.QEpaper E := by
  simp only [XSwitch.QEpaper, Set.mem_ofPred_eq]
  intro g hg h0
  rw [QEPaper.tight_ineq_zeta x hg h0 (QEPaper.zeta_withZeta x (x.zeta u))]
  exact ⟨(QEPaper.mem_B_iff_ineqs x.toSwitch).mp (hEB hu) g hg, fun hz => hz u hu⟩

/-- Extension by zero from the `ζ`-coordinates to all coordinates. -/
noncomputable def rj_ext0 : ({p // p ∉ x.special} → ℝ) →ₗ[ℝ] (x.toSwitch.P' → ℝ) where
  toFun w p := by classical exact if h : p ∈ x.special then 0 else w ⟨p, h⟩
  map_add' w w' := by
    classical
    funext p
    by_cases h : p ∈ x.special <;> simp [h]
  map_smul' c w := by
    classical
    funext p
    by_cases h : p ∈ x.special <;> simp [h]

theorem rj_ext0_off (w : {p // p ∉ x.special} → ℝ) (p : x.toSwitch.P') (h : p ∉ x.special) :
    rj_ext0 x w p = w ⟨p, h⟩ := by
  classical
  simp [rj_ext0, h]

theorem rj_ext0_withZeta (q : {p // p ∉ x.special} → ℝ) :
    rj_ext0 x (q - x.zeta x.u0) = x.withZeta q - x.u0 := by
  classical
  funext p
  by_cases h : p ∈ x.special <;> simp [rj_ext0, XSwitch.withZeta, XSwitch.zeta, h]

/-- `ζ` as an affine map. -/
noncomputable def rj_zetaAff : (x.toSwitch.P' → ℝ) →ᵃ[ℝ] ({p // p ∉ x.special} → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : {p // p ∉ x.special} → x.toSwitch.P')).toAffineMap

theorem rj_zetaAff_apply (u : x.toSwitch.P' → ℝ) : rj_zetaAff x u = x.zeta u := rfl

theorem rj_M1_le {E : Set (x.toSwitch.P' → ℝ)} (hEB : E ⊆ x.toSwitch.B) {u : x.toSwitch.P' → ℝ}
    (hu : u ∈ affineSpan ℝ E) : x.zeta u ∈ affineSpan ℝ (x.QEpaper E) := by
  have hle : affineSpan ℝ E ≤ (affineSpan ℝ (x.QEpaper E)).comap (rj_zetaAff x) := by
    rw [affineSpan_le]
    intro v hv
    rw [SetLike.mem_coe, AffineSubspace.mem_comap, rj_zetaAff_apply]
    exact subset_affineSpan ℝ _ (rj_zeta_mem_QEpaper x hEB hv)
  have h := hle hu
  rwa [AffineSubspace.mem_comap, rj_zetaAff_apply] at h

theorem rj_M1_dz {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {u : x.toSwitch.P' → ℝ} (hu' : x.zeta u ∈ affineSpan ℝ (x.QEpaper E)) :
    rj_ext0 x (x.zeta u - x.zeta x.u0) ∈ (affineSpan ℝ E).direction := by
  have hu0A : x.u0 ∈ affineSpan ℝ E := subset_affineSpan ℝ E (QEPaper.u0_mem_face x hE0)
  have hz0 : x.zeta x.u0 ∈ x.QEpaper E ∩ box (x.zeta x.u0) (eps x) :=
    ⟨QEPaper.zeta_u0_mem_QEpaper x E, center_mem_box _ (eps_pos x)⟩
  have hbox : box (x.zeta x.u0) (eps x) ∈ 𝓝 (x.zeta x.u0) :=
    (isOpen_box _ _).mem_nhds (center_mem_box _ (eps_pos x))
  have hspan := rj_affineSpan_inter_nhds (QEPaper.QEpaper_convex x E) (QEPaper.zeta_u0_mem_QEpaper x E) hbox
  have hzdir : x.zeta u -ᵥ x.zeta x.u0 ∈ vectorSpan ℝ (x.QEpaper E ∩ box (x.zeta x.u0) (eps x)) := by
    rw [← direction_affineSpan, hspan]
    exact AffineSubspace.vsub_mem_direction hu' (subset_affineSpan ℝ _ (QEPaper.zeta_u0_mem_QEpaper x E))
  have hmap : vectorSpan ℝ (x.QEpaper E ∩ box (x.zeta x.u0) (eps x)) ≤
      (affineSpan ℝ E).direction.comap (rj_ext0 x) := by
    rw [vectorSpan_eq_span_vsub_set_right (k := ℝ) hz0, Submodule.span_le]
    rintro _ ⟨q, ⟨hqQ, hqbox⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    show rj_ext0 x (q -ᵥ x.zeta x.u0) ∈ (affineSpan ℝ E).direction
    rw [vsub_eq_sub, rj_ext0_withZeta, ← vsub_eq_sub]
    have hqE : x.withZeta q ∈ E := by
      rw [mem_iff_QE x hE hE0 (QEPaper.close_withZeta x hqbox), QEPaper.zeta_withZeta]
      exact (QEPaper.QE_iff_QEpaper x hE hE0 hqbox).mpr hqQ
    exact AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ E hqE) hu0A
  have h := hmap hzdir
  rwa [Submodule.mem_comap, vsub_eq_sub] at h

theorem rj_M1_da {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {da : x.toSwitch.P' → ℝ} (hda_off : ∀ p, p ∉ x.special → da p = 0) : da ∈ (affineSpan ℝ E).direction := by
  have hu0E : x.u0 ∈ E := QEPaper.u0_mem_face x hE0
  have hu0A : x.u0 ∈ affineSpan ℝ E := subset_affineSpan ℝ E hu0E
  have hz0QE : x.zeta x.u0 ∈ x.QE E := (mem_iff_QE x hE hE0 (QEPaper.close_u0 x)).mp hu0E
  obtain ⟨t, ht0, htc⟩ :=
    rj_exists_pos_of_eventually (eventually_lineMap_mem_open (isOpen_close x) (QEPaper.close_u0 x) (x.u0 + da))
  have hwz : x.zeta (AffineMap.lineMap x.u0 (x.u0 + da) t) = x.zeta x.u0 := by
    funext ⟨p, hp⟩
    simp only [XSwitch.zeta, AffineMap.lineMap_apply_module', add_sub_cancel_left, Pi.add_apply, Pi.smul_apply,
      hda_off p hp, smul_zero, zero_add]
  have hwE : AffineMap.lineMap x.u0 (x.u0 + da) t ∈ E := by
    rw [mem_iff_QE x hE hE0 htc, hwz]
    exact hz0QE
  have h1 := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ E hwE) hu0A
  rw [AffineMap.lineMap_vsub_left, vsub_eq_sub, add_sub_cancel_left] at h1
  have h2 := Submodule.smul_mem _ t⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ ht0.ne', one_smul] at h2

theorem rj_M1_ge {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {u : x.toSwitch.P' → ℝ} (hu' : x.zeta u ∈ affineSpan ℝ (x.QEpaper E)) : u ∈ affineSpan ℝ E := by
  have hu0A : x.u0 ∈ affineSpan ℝ E := subset_affineSpan ℝ E (QEPaper.u0_mem_face x hE0)
  have hdz := rj_M1_dz x hE hE0 hu'
  have hda_off : ∀ p, p ∉ x.special → ((u - x.u0) - rj_ext0 x (x.zeta u - x.zeta x.u0)) p = 0 := by
    intro p hp
    rw [Pi.sub_apply, Pi.sub_apply, rj_ext0_off x _ p hp, Pi.sub_apply]
    simp only [XSwitch.zeta]
    ring
  have hda := rj_M1_da x hE hE0 hda_off
  have hmem := AffineSubspace.vadd_mem_of_mem_direction (Submodule.add_mem _ hda hdz) hu0A
  rwa [sub_add_cancel, vadd_eq_add, sub_add_cancel] at hmem

theorem sec4_E_subset_QE_proved (E : Set (x.toSwitch.P' → ℝ)) (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    (∀ u ∈ E, x.zeta u ∈ x.QEpaper E) ∧
    (∀ V ∈ 𝓝 (x.zeta x.u0), affineSpan ℝ (x.QEpaper E ∩ V) = affineSpan ℝ (x.QEpaper E)) ∧
    (affineSpan ℝ E : Set (x.toSwitch.P' → ℝ)) = {u | x.zeta u ∈ affineSpan ℝ (x.QEpaper E)} :=
  ⟨fun _ hu => rj_zeta_mem_QEpaper x hE.2.subset hu,
    fun _ hV => rj_affineSpan_inter_nhds (QEPaper.QEpaper_convex x E) (QEPaper.zeta_u0_mem_QEpaper x E) hV,
    Set.ext fun _ => ⟨fun hu => rj_M1_le x hE.2.subset hu, fun hu => rj_M1_ge x hE hE0 hu⟩⟩

end M1

end HibiLi.Proofs
