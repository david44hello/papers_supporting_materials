/-
HibiLi/Proofs/Lemma36.lean — paper Lemma 3.6 (the e-cells of S|_E, T|_E are the maximal affinity sets) and the bridge
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs
import HibiLi.Polytope.CarrierInterior
import HibiLi.Polytope.Dimension
import HibiLi.Proofs.LU
import HibiLi.Proofs.LUPiecewise

namespace HibiLi.Proofs

open HibiLi Set

/-! ### Generic geometry: `F = max_{i ∈ S} f i` on a closed convex full-dimensional set `B` -/

section Generic

variable {ι β : Type*} [Fintype ι] (B : Set (ι → ℝ)) (S : Finset β) (f : β → (ι → ℝ) →ᵃ[ℝ] ℝ)
  (F : (ι → ℝ) → ℝ)

/-- The affinity domain `{u ∈ B : F u = f i u}` of the branch `i`. -/
def pwDom (i : β) : Set (ι → ℝ) := {u | u ∈ B ∧ F u = f i u}

/-- Nonempty faces of the full-dimensional affinity domains (the cells of `S`, resp. `T`). -/
def pwCells : Set (Set (ι → ℝ)) :=
  {C | ∃ i ∈ S, adim (pwDom B f F i) = Fintype.card ι ∧ IsFace (pwDom B f F i) C}

/-- The `e`-cells (`e = dim E`) of the restriction of `pwCells` to `E`. -/
def pwTop (E : Set (ι → ℝ)) : Set (Set (ι → ℝ)) :=
  {A | (A.Nonempty ∧ ∃ A₀ ∈ pwCells B S f F, A = A₀ ∩ E) ∧ adim A = adim E}

variable {B S f F}

/-- Spanning the whole space means full dimension. -/
lemma adim_eq_card_of_affineSpan_eq_top {X : Set (ι → ℝ)} (htop : affineSpan ℝ X = ⊤) :
    adim X = Fintype.card ι := by
  unfold adim
  rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
  simp

/-- A nonempty subset of `X` of the same dimension has the same affine span. -/
lemma affineSpan_eq_of_adim_eq {A X : Set (ι → ℝ)} (hAX : A ⊆ X) (hA : A.Nonempty)
    (hdim : adim A = adim X) : affineSpan ℝ A = affineSpan ℝ X := by
  refine AffineSubspace.eq_of_direction_eq_of_nonempty_of_le ?_ ((affineSpan_nonempty ℝ).mpr hA)
    (affineSpan_mono ℝ hAX)
  rw [direction_affineSpan, direction_affineSpan]
  exact Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hAX) hdim

/-- An affine function minimized at a relative interior point of `A` is constant on `A`. -/
lemma affine_eq_of_intrinsicInterior_min {A : Set (ι → ℝ)} {x : ι → ℝ} (hx : x ∈ intrinsicInterior ℝ A)
    (h : (ι → ℝ) →ᵃ[ℝ] ℝ) (hmin : ∀ y ∈ A, h x ≤ h y) : ∀ y ∈ A, h y = h x := by
  have hlin : ∀ z, h.linear z = h z - h 0 := fun z => congrFun h.decomp' z
  have key := linear_eq_of_intrinsicInterior_max hx (-LinearMap.toContinuousLinearMap h.linear)
    (fun y hy => by
      simp only [neg_apply, LinearMap.coe_toContinuousLinearMap', hlin]
      linarith [hmin y hy])
  intro y hy
  have := key y hy
  simp only [neg_apply, LinearMap.coe_toContinuousLinearMap', hlin] at this
  linarith

omit [Fintype ι] in
/-- If `E` is a face of `B` and `D ⊆ B` meets `E`, then `D ∩ E` is a face of `D` (same exposing functional). -/
lemma isFace_inter_of_isFace {E D : Set (ι → ℝ)} (hE : IsFace B E) (hDB : D ⊆ B)
    (hne : (D ∩ E).Nonempty) : IsFace D (D ∩ E) := by
  refine ⟨hne, fun _ => ?_⟩
  obtain ⟨l, hl⟩ := hE.2 hE.1
  obtain ⟨a, haD, haE⟩ := hne
  refine ⟨l, ?_⟩
  ext x
  constructor
  · rintro ⟨hxD, hxE⟩
    rw [hl] at hxE
    exact ⟨hxD, fun y hy => hxE.2 y (hDB hy)⟩
  · rintro ⟨hxD, hxmax⟩
    refine ⟨hxD, ?_⟩
    rw [hl] at haE ⊢
    exact ⟨hDB hxD, fun y hy => (haE.2 y hy).trans (hxmax a haD)⟩

/-- A finite union of closed sets with empty interiors has empty interior. -/
lemma interior_biUnion_finset_eq_empty {α X : Type*} [TopologicalSpace X] (T : Finset α) (C : α → Set X)
    (hc : ∀ a ∈ T, IsClosed (C a)) (hi : ∀ a ∈ T, interior (C a) = ∅) : interior (⋃ a ∈ T, C a) = ∅ := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T _ ih =>
    rw [Finset.set_biUnion_insert, interior_union_isClosed_of_interior_empty (hc a (Finset.mem_insert_self _ _))
      (ih (fun b hb => hc b (Finset.mem_insert_of_mem hb)) (fun b hb => hi b (Finset.mem_insert_of_mem hb)))]
    exact hi a (Finset.mem_insert_self _ _)

variable (hle : ∀ i ∈ S, ∀ u, f i u ≤ F u) (hex : ∀ u, ∃ i ∈ S, F u = f i u)
include hle hex

omit [Fintype ι] in
lemma pwDom_eq {i : β} (hi : i ∈ S) : pwDom B f F i = B ∩ ⋂ j ∈ S, {u | f j u ≤ f i u} := by
  ext u
  simp only [pwDom, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  refine and_congr_right fun _ => ⟨fun h j hj => (hle j hj u).trans_eq h, fun h => ?_⟩
  obtain ⟨j, hj, hFj⟩ := hex u
  exact le_antisymm (hFj.trans_le (h j hj)) (hle i hi u)

omit [Fintype ι] in
lemma pwDom_convex (hBc : Convex ℝ B) {i : β} (hi : i ∈ S) : Convex ℝ (pwDom B f F i) := by
  rw [pwDom_eq hle hex hi]
  refine hBc.inter (convex_iInter₂ fun j _ => ?_)
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, Convex.combo_affine_apply hab, smul_eq_mul] at hx hy ⊢
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

lemma pwDom_closed (hBcl : IsClosed B) {i : β} (hi : i ∈ S) : IsClosed (pwDom B f F i) := by
  rw [pwDom_eq hle hex hi]
  exact hBcl.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le (f j).continuous_of_finiteDimensional (f i).continuous_of_finiteDimensional)

/-- The full-dimensional affinity domains cover `B` (the thin ones are nowhere dense). -/
lemma pw_cover (hBc : Convex ℝ B) (hBcl : IsClosed B) (hBdim : adim B = Fintype.card ι) {u : ι → ℝ}
    (hu : u ∈ B) : ∃ i ∈ S, adim (pwDom B f F i) = Fintype.card ι ∧ u ∈ pwDom B f F i := by
  classical
  let full := S.filter (fun i => adim (pwDom B f F i) = Fintype.card ι)
  let thin := S.filter (fun i => adim (pwDom B f F i) ≠ Fintype.card ι)
  let G := ⋃ i ∈ full, pwDom B f F i
  have hG : IsClosed G :=
    isClosed_biUnion_finset fun i hi => pwDom_closed hle hex hBcl (Finset.mem_filter.mp hi).1
  have hthin : interior (⋃ i ∈ thin, pwDom B f F i) = ∅ := by
    refine interior_biUnion_finset_eq_empty thin _
      (fun i hi => pwDom_closed hle hex hBcl (Finset.mem_filter.mp hi).1) (fun i hi => ?_)
    by_contra hne
    have htop := isOpen_interior.affineSpan_eq_top (Set.nonempty_iff_ne_empty.mpr hne)
    exact (Finset.mem_filter.mp hi).2 (adim_eq_card_of_affineSpan_eq_top
      (top_unique (htop ▸ affineSpan_mono ℝ interior_subset)))
  have hint : interior B ⊆ G := by
    intro x hx
    by_contra hxG
    have hsub : interior B ∩ Gᶜ ⊆ ⋃ i ∈ thin, pwDom B f F i := by
      rintro w ⟨hwB, hwG⟩
      obtain ⟨i, hi, hFi⟩ := hex w
      have hw : w ∈ pwDom B f F i := ⟨interior_subset hwB, hFi⟩
      by_cases hfull : adim (pwDom B f F i) = Fintype.card ι
      · exact absurd (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hfull⟩, hw⟩) hwG
      · exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hfull⟩, hw⟩
    have hopen := interior_maximal hsub (isOpen_interior.inter hG.isOpen_compl)
    rw [hthin] at hopen
    exact hopen ⟨hx, hxG⟩
  have hspan : affineSpan ℝ B = ⊤ := by
    refine (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty (k := ℝ) (V := ι → ℝ) (P := ι → ℝ) ⟨u, hu⟩).mpr ?_
    exact Submodule.eq_top_of_finrank_eq (hBdim.trans (Module.finrank_fintype_fun_eq_card ℝ).symm)
  have hBint : (interior B).Nonempty := hBc.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  have huG : u ∈ G := by
    refine closure_minimal hint hG ?_
    rw [hBc.closure_interior_eq_closure_of_nonempty_interior hBint]
    exact subset_closure hu
  obtain ⟨i, hi, hui⟩ := mem_iUnion₂.mp huG
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2, hui⟩

/-- (→) of Lemma 3.6: an `e`-cell `A₀ ∩ E` is a maximal `e`-dimensional convex set where `F` is affine. -/
lemma pwTop_forward (hBc : Convex ℝ B) {E : Set (ι → ℝ)} (hE : IsFace B E) {A : Set (ι → ℝ)}
    (hA : A ∈ pwTop B S f F E) :
    A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn F A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn F D → D = A := by
  obtain ⟨⟨hAne, A₀, ⟨i, hi, -, hface⟩, rfl⟩, hdim⟩ := hA
  have hdom : ∀ u ∈ A₀ ∩ E, u ∈ pwDom B f F i := fun u hu => hface.subset hu.1
  refine ⟨inter_subset_right, (hface.2.convex (pwDom_convex hle hex hBc hi)).inter (hE.2.convex hBc), hdim,
    ⟨f i, fun u hu => (hdom u hu).2⟩, fun D hAD hDE _ hD => ?_⟩
  obtain ⟨g, hg⟩ := hD
  -- `A₀ ∩ E` spans `aff E`, so `g = f i` and the exposing functional of `A₀` is constant on `D`
  have hspan : ∀ u ∈ D, u ∈ affineSpan ℝ (A₀ ∩ E) := fun u hu => by
    rw [affineSpan_eq_of_adim_eq inter_subset_right hAne hdim]
    exact subset_affineSpan ℝ E (hDE hu)
  have hgf : ∀ u ∈ D, F u = f i u := fun u hu => by
    rw [hg u hu]
    exact AffineMap.eqOn_affineSpan (fun v hv => (hg v (hAD hv)).symm.trans (hdom v hv).2) (hspan u hu)
  obtain ⟨a, haA₀, haE⟩ := hAne
  obtain ⟨l, hl⟩ := hface.2 ⟨a, haA₀⟩
  have hmaxA₀ : ∀ v ∈ A₀, ∀ y ∈ pwDom B f F i, l y ≤ l v := fun v hv => by
    rw [hl] at hv
    exact hv.2
  have hflat : ∀ v ∈ A₀ ∩ E, l v = l a := fun v hv =>
    le_antisymm (hmaxA₀ a haA₀ v (hface.subset hv.1)) (hmaxA₀ v hv.1 a (hface.subset haA₀))
  refine Subset.antisymm (fun u hu => ⟨?_, hDE hu⟩) hAD
  have hlu := linear_eq_on_affineSpan l (l a) hflat u (hspan u hu)
  rw [hl]
  exact ⟨⟨hE.subset (hDE hu), hgf u hu⟩, fun y hy => (hmaxA₀ a haA₀ y hy).trans hlu.ge⟩

/-- (←) of Lemma 3.6: a maximal `e`-dimensional convex subset of `E` where `F` is affine is an `e`-cell. -/
lemma pwTop_backward (hBc : Convex ℝ B) (hBcl : IsClosed B) (hBdim : adim B = Fintype.card ι)
    {E : Set (ι → ℝ)} (hE : IsFace B E) {A : Set (ι → ℝ)}
    (hA : A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn F A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn F D → D = A) : A ∈ pwTop B S f F E := by
  obtain ⟨hAE, hAc, hdim, ⟨g, hg⟩, hmax⟩ := hA
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hE.1
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have hx' := hmax {x} (by simp [hne]) (singleton_subset_iff.mpr hx) (convex_singleton x)
      ⟨AffineMap.const ℝ _ (F x), fun u hu => by rw [mem_singleton_iff.mp hu]; rfl⟩
    rw [hne] at hx'
    exact singleton_ne_empty x hx'
  -- a relative interior point of `A` lies in a full-dimensional domain; `g - f i ≥ 0` vanishes there
  obtain ⟨x, hx⟩ := hAne.intrinsicInterior hAc
  have hxA : x ∈ A := intrinsicInterior_subset hx
  obtain ⟨i, hi, hfull, hxi⟩ := pw_cover hle hex hBc hBcl hBdim (hE.subset (hAE hxA))
  have hzero := affine_eq_of_intrinsicInterior_min hx (g - f i) (fun y hy => by
    simp only [AffineMap.coe_sub, Pi.sub_apply]
    linarith [hg x hxA, hg y hy, hxi.2, hle i hi y])
  have hAdom : A ⊆ pwDom B f F i := fun y hy => by
    refine ⟨hE.subset (hAE hy), ?_⟩
    have hy0 := hzero y hy
    simp only [AffineMap.coe_sub, Pi.sub_apply] at hy0
    linarith [hg x hxA, hg y hy, hxi.2]
  have hA₀ := hmax (pwDom B f F i ∩ E) (subset_inter hAdom hAE) inter_subset_right
    ((pwDom_convex hle hex hBc hi).inter (hE.2.convex hBc)) ⟨f i, fun u hu => hu.1.2⟩
  have hface : IsFace (pwDom B f F i) (pwDom B f F i ∩ E) :=
    isFace_inter_of_isFace hE (fun u hu => hu.1) (by rw [hA₀]; exact hAne)
  refine ⟨⟨hAne, _, ⟨i, hi, hfull, hface⟩, ?_⟩, hdim⟩
  rw [inter_assoc, inter_self, hA₀]

theorem pwTop_iff (hBc : Convex ℝ B) (hBcl : IsClosed B) (hBdim : adim B = Fintype.card ι)
    {E : Set (ι → ℝ)} (hE : IsFace B E) (A : Set (ι → ℝ)) :
    A ∈ pwTop B S f F E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn F A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn F D → D = A :=
  ⟨pwTop_forward hle hex hBc hE, pwTop_backward hle hex hBc hBcl hBdim hE⟩

end Generic

lemma affineOn_neg_iff {ι : Type*} {F : (ι → ℝ) → ℝ} {D : Set (ι → ℝ)} :
    AffineOn (fun u => -F u) D ↔ AffineOn F D :=
  ⟨fun ⟨g, hg⟩ => ⟨-g, fun u hu => by
      have hgu := hg u hu
      simp only [AffineMap.coe_neg, Pi.neg_apply] at hgu ⊢
      linarith⟩,
    fun ⟨g, hg⟩ => ⟨-g, fun u hu => by simp only [AffineMap.coe_neg, Pi.neg_apply, hg u hu]⟩⟩

/-! ### The switch instances: `L` (max of chain sums) and `U` (min, via `-U = max(-·)`) -/

section Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

lemma B_convex_closed : Convex ℝ s.B ∧ IsClosed s.B := by
  obtain ⟨V, hV⟩ := s.B_isPolytope
  rw [hV]
  exact ⟨convex_convexHull ℝ _, (Set.Finite.isCompact_convexHull ℝ V.finite_toSet).isClosed⟩

lemma B_nonempty : s.B.Nonempty :=
  ⟨0, by simp [Switch.B, chainOrderPolytope]⟩

lemma pwTop_L (E : Set (s.P' → ℝ)) :
    pwTop s.B s.lowBranches (chainSumAff s) s.L E = s.topCells s.cellsS E := by
  have hdom : pwDom s.B (chainSumAff s) s.L = s.domL := by
    funext K; ext u; simp [pwDom, Switch.domL, chainSumAff_apply]
  simp only [pwTop, pwCells, hdom]
  rfl

lemma pwTop_U (E : Set (s.P' → ℝ)) :
    pwTop s.B s.upBranches (fun j => -upAff s j) (fun u => -s.U u) E = s.topCells s.cellsT E := by
  have hdom : pwDom s.B (fun j => -upAff s j) (fun u => -s.U u) = s.domU := by
    funext j; ext u; simp [pwDom, Switch.domU, upAff_apply]
  simp only [pwTop, pwCells, hdom]
  rfl

end Switch

/-- **Lemma 3.6.** The `e`-cells of `S|_E` (resp. `T|_E`) are exactly the maximal `e`-dimensional convex subsets of
`E` on which `L` (resp. `U`) is affine. -/
theorem lemma_3_6_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (A : Set (s.P' → ℝ)) :
    (A ∈ s.topCells s.cellsS E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn s.L A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn s.L D → D = A) ∧
    (A ∈ s.topCells s.cellsT E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn s.U A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn s.U D → D = A) := by
  obtain ⟨hBc, hBcl⟩ := B_convex_closed s
  have hBdim : adim s.B = Fintype.card s.P' := chainOrderPolytope_adim _ _
  constructor
  · rw [← pwTop_L]
    refine pwTop_iff (fun K hK u => (chainSumAff_apply s K u).trans_le (chainSum_le_L s hK u))
      (fun u => ?_) hBc hBcl hBdim hE A
    obtain ⟨K, hK, hmax⟩ := Finset.exists_mem_eq_sup' s.lowBranches_nonempty (fun K => s.chainSum K u)
    exact ⟨K, hK, hmax.trans (chainSumAff_apply s K u).symm⟩
  · rw [← pwTop_U]
    have key := pwTop_iff (S := s.upBranches) (f := fun j => -upAff s j) (F := fun u => -s.U u)
      (fun j hj u => by simpa [upAff_apply] using U_le_upVal s hj u) (fun u => ?_) hBc hBcl hBdim hE A
    · simpa only [affineOn_neg_iff] using key
    obtain ⟨j, hj, hmin⟩ := Finset.exists_mem_eq_inf' s.upBranches_nonempty (fun j => s.upVal j u)
    exact ⟨j, hj, by simp only [AffineMap.coe_neg, Pi.neg_apply, upAff_apply, neg_inj]; exact hmin⟩

/-- Cells of `S` that lie in `B` are unchanged by restriction to `B`. -/
lemma topCells_B_iff {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) {K : Set (Set (s.P' → ℝ))}
    (hK : ∀ C ∈ K, C.Nonempty ∧ C ⊆ s.B) (A : Set (s.P' → ℝ)) :
    A ∈ K ∧ adim A = adim s.B ↔ A ∈ s.topCells K s.B := by
  constructor
  · rintro ⟨hA, hdim⟩
    exact ⟨⟨(hK A hA).1, A, hA, (inter_eq_left.mpr (hK A hA).2).symm⟩, hdim⟩
  · rintro ⟨⟨-, A₀, hA₀, rfl⟩, hdim⟩
    rw [inter_eq_left.mpr (hK A₀ hA₀).2] at hdim ⊢
    exact ⟨hA₀, hdim⟩

/-- Lines 357–360: the full-dimensional cells of `S` (resp. `T`) are the maximal full-dimensional convex subsets of
`B` on which `L` (resp. `U`) is affine (Lemma 3.6 with `E = B`). -/
theorem sec3_S_paper_def_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (A : Set (s.P' → ℝ)) :
    (A ∈ s.cellsS ∧ adim A = Fintype.card s.P' ↔ A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧
      AffineOn s.L A ∧ ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.L D → D = A) ∧
    (A ∈ s.cellsT ∧ adim A = Fintype.card s.P' ↔ A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧
      AffineOn s.U A ∧ ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.U D → D = A) := by
  have hBdim : adim s.B = Fintype.card s.P' := chainOrderPolytope_adim _ _
  have hSB : ∀ C ∈ s.cellsS, C.Nonempty ∧ C ⊆ s.B := fun _ ⟨_, _, _, hface⟩ =>
    ⟨hface.1, fun _ hu => (hface.subset hu).1⟩
  have hTB : ∀ C ∈ s.cellsT, C.Nonempty ∧ C ⊆ s.B := fun _ ⟨_, _, _, hface⟩ =>
    ⟨hface.1, fun _ hu => (hface.subset hu).1⟩
  obtain ⟨hS, hT⟩ := lemma_3_6_proved s s.B (IsFace.refl (B_nonempty s)) A
  rw [← topCells_B_iff s hSB, hBdim] at hS
  rw [← topCells_B_iff s hTB, hBdim] at hT
  exact ⟨hS, hT⟩

end HibiLi.Proofs
