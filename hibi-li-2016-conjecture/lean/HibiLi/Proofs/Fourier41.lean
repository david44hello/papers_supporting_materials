/-
HibiLi/Proofs/Fourier41.lean — Fourier's Lemma 4.1 (first equality of Lemma 3.2) from the informal reading: non-vertical faces are counted by the cells (paper v4.60 l. 373-376, 380-384).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Both polytopes are prisms over `B` (Proposition 3.1). Before the switch, the non-vertical faces are the graphs of `L`
over the cells of `S` and of `U` over the cells of `T`; after it, the parts of `{z = 0}` over the faces of `B` and the
graphs of `U − L` over the cells of `R`. Each such graph is a face: the graph over a full-dimensional affinity domain is
cut out by an affine bound (`z ≥ ℓ_K`, `z ≤ upVal j`, `z ≥ 0`, `z ≤ upVal j − ℓ_K`), and a face of a face of a polytope
is a face. Graph maps are injective and keep dimensions, the faces of both kinds are counted by the faces of `B` with
`L = U` on them, and inclusion-exclusion gives the coefficient of `F_B + F_R − F_S − F_T`.
-/
import HibiLi.Proofs.V450Rows
import HibiLi.Proofs.DeltaCoefficient

noncomputable section

namespace HibiLi.Proofs.Fourier41

open HibiLi HibiLi.Proofs HibiLi.Proofs.Vertical HibiLi.Proofs.V450 HibiLi.Proofs.V450.Rows Polynomial

section Image

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- The image of a face under an affine map with an affine left inverse is a face of the image (used for the graphs
of v4.60 l. 380-383). -/
theorem face_image_of_leftInverse (emb : E →ᵃ[ℝ] G) (retr : G →ᵃ[ℝ] E)
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

end Image

section Coefficients

variable {ι : Type*} [Fintype ι]

/-- No cell has dimension above the ambient dimension, so the polynomial `F_𝒴` of v4.60 l. 363-364 has no terms
there. -/
theorem cellNum_eq_zero_of_card_lt (K : Set (Set (ι → ℝ))) {k : ℕ} (hk : Fintype.card ι < k) :
    cellNum K k = 0 := by
  have hempty : {A ∈ K | adim A = k} = ∅ := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hA
    exact absurd (hA ▸ adim_le_card A) (not_le.mpr hk)
  simp [cellNum, hempty]

/-- The coefficient of `t^k` in `F_𝒴` is the number of `k`-cells of `𝒴` (v4.60 l. 363-364). -/
theorem cellPoly_coeff (K : Set (Set (ι → ℝ))) (k : ℕ) : (cellPoly K).coeff k = (cellNum K k : ℤ) := by
  unfold cellPoly cellPolyUpTo
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hk : k ≤ Fintype.card ι
  · rw [Finset.sum_ite_eq]
    simp [Finset.mem_range, Nat.lt_succ_of_le hk]
  · rw [Finset.sum_ite_eq]
    simp only [Finset.mem_range, Nat.lt_succ_iff, hk, ite_false]
    rw [cellNum_eq_zero_of_card_lt K (not_le.mp hk)]
    simp

end Coefficients

section Graphs

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The projection `x ↦ x|_{P'}` as an affine map (base coordinates of v4.60 l. 380-383). -/
def projAff : (P → ℝ) →ᵃ[ℝ] (s.P' → ℝ) := (proj s).toLinearMap.toAffineMap

/-- The affine projection is the projection `x ↦ x|_{P'}` onto the base coordinates (v4.60 l. 380-383). -/
theorem projAff_apply (x : P → ℝ) : projAff s x = proj s x := rfl

/-- The projection recovers the base point from a point of a graph (v4.60 l. 380-383). -/
theorem leftInverse_graphMap (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ) : Function.LeftInverse (projAff s) (graphMap s g) :=
  fun u => proj_mk s u (g u)

/-- If `f` agrees with an affine map on `X`, the graph of `f` over a face of `X` is a face of the graph over `X`
(v4.60 l. 380-383). -/
theorem graph_face_of_face {f : (s.P' → ℝ) → ℝ} {X C : Set (s.P' → ℝ)} (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ)
    (hfg : ∀ u ∈ X, f u = g u) (hC : IsFace X C) : IsFace (graph s f X) (graph s f C) := by
  rw [graph_eq_image s g hfg, graph_eq_image s g (fun u hu => hfg u (hC.subset hu))]
  exact face_image_of_leftInverse (graphMap s g) (projAff s) (leftInverse_graphMap s g) hC

/-- If `g ≤ lo` on the base with `g` affine, the graph of `lo` over `{lo = g}` is a face of the prism: it is cut out
by `z ≥ g` (v4.60 l. 340-341 for `L` and its chain sums; l. 380-383). -/
theorem graph_lower_isFace {lo hi : (s.P' → ℝ) → ℝ} {base : Set (s.P' → ℝ)} (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ)
    (hlohi : ∀ u ∈ base, lo u ≤ hi u) (hg : ∀ u ∈ base, g u ≤ lo u) (hne : ∃ u ∈ base, lo u = g u) :
    IsFace (prism s lo hi base) (graph s lo {u ∈ base | lo u = g u}) := by
  let φ : (P → ℝ) →ᵃ[ℝ] ℝ := g.comp (projAff s) - (LinearMap.proj s.q : (P → ℝ) →ₗ[ℝ] ℝ).toAffineMap
  have hφ : ∀ x, φ x = g (proj s x) - x s.q := fun x => rfl
  have key : graph s lo {u ∈ base | lo u = g u} = {x ∈ prism s lo hi base | φ x = 0} := by
    ext x
    simp only [mem_graph, prism, Set.mem_ofPred_eq, hφ]
    constructor
    · rintro ⟨⟨hb, hE⟩, hq⟩
      exact ⟨⟨hb, hq.ge, hq.le.trans (hlohi _ hb)⟩, by linarith⟩
    · rintro ⟨⟨hb, hlo, -⟩, h0⟩
      have h1 := hg _ hb
      exact ⟨⟨hb, by linarith⟩, by linarith⟩
  rw [key]
  refine isFace_affine_level _ φ 0 (fun x hx => ?_) ?_
  · rw [hφ]
    have h1 := hg _ hx.1
    linarith [hx.2.1]
  · obtain ⟨u, hu, hE⟩ := hne
    refine ⟨mk s u (lo u), mk_mem_prism s hu le_rfl (hlohi u hu), ?_⟩
    rw [hφ, proj_mk, mk_q, hE, sub_self]

/-- If `hi ≤ g` on the base with `g` affine, the graph of `hi` over `{hi = g}` is a face of the prism: it is cut out
by `z ≤ g` (v4.60 l. 343 for `U` and its terms; l. 380-383). -/
theorem graph_upper_isFace {lo hi : (s.P' → ℝ) → ℝ} {base : Set (s.P' → ℝ)} (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ)
    (hlohi : ∀ u ∈ base, lo u ≤ hi u) (hg : ∀ u ∈ base, hi u ≤ g u) (hne : ∃ u ∈ base, hi u = g u) :
    IsFace (prism s lo hi base) (graph s hi {u ∈ base | hi u = g u}) := by
  let φ : (P → ℝ) →ᵃ[ℝ] ℝ := (LinearMap.proj s.q : (P → ℝ) →ₗ[ℝ] ℝ).toAffineMap - g.comp (projAff s)
  have hφ : ∀ x, φ x = x s.q - g (proj s x) := fun x => rfl
  have key : graph s hi {u ∈ base | hi u = g u} = {x ∈ prism s lo hi base | φ x = 0} := by
    ext x
    simp only [mem_graph, prism, Set.mem_ofPred_eq, hφ]
    constructor
    · rintro ⟨⟨hb, hE⟩, hq⟩
      exact ⟨⟨hb, (hlohi _ hb).trans hq.ge, hq.le⟩, by linarith⟩
    · rintro ⟨⟨hb, -, hhi⟩, h0⟩
      have h1 := hg _ hb
      exact ⟨⟨hb, by linarith⟩, by linarith⟩
  rw [key]
  refine isFace_affine_level _ φ 0 (fun x hx => ?_) ?_
  · rw [hφ]
    have h1 := hg _ hx.1
    linarith [hx.2.2]
  · obtain ⟨u, hu, hE⟩ := hne
    refine ⟨mk s u (hi u), mk_mem_prism s hu (hlohi u hu) le_rfl, ?_⟩
    rw [hφ, proj_mk, mk_q, hE, sub_self]

/-- A graph contains no segment parallel to the `z`-axis (v4.60 l. 380-383). -/
theorem not_hasVertical_graph (f : (s.P' → ℝ) → ℝ) (C : Set (s.P' → ℝ)) : ¬ HasVertical s (graph s f C) := by
  intro hv
  obtain ⟨x, hx, t, ht, hxt⟩ := (hasVertical_iff s _).1 hv
  have hp : proj s (x + t • ez s) = proj s x := by
    rw [map_add, map_smul, proj_ez, smul_zero, add_zero]
  have h1 : (x + t • ez s) s.q = f (proj s (x + t • ez s)) := hxt.2
  have h2 : x s.q = f (proj s x) := hx.2
  have h3 : (x + t • ez s) s.q = x s.q + t := by
    rw [Pi.add_apply, Pi.smul_apply, ez_q, smul_eq_mul, mul_one]
  rw [h3, hp, ← h2] at h1
  exact ht (by linarith)

/-- Distinct cells have distinct graphs: a graph projects onto its cell (v4.60 l. 383). -/
theorem graph_injOn (f : (s.P' → ℝ) → ℝ) (X : Set (Set (s.P' → ℝ))) : Set.InjOn (graph s f) X :=
  fun _ _ _ _ h => eq_of_graph_eq s h

end Graphs

section Cells

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The affinity domain `A_ℓ = {u ∈ B : L(u) = ℓ(u)}` of a chain sum (v4.60 l. 340). -/
theorem domL_eq (K : Finset s.P') : s.domL K = {u ∈ s.B | s.L u = (chainLin s K).toAffineMap u} := by
  ext u
  simp only [Switch.domL, Set.mem_ofPred_eq, LinearMap.coe_toAffineMap, chainLin_apply]

/-- The affinity domain of a term of `U` (v4.60 l. 343). -/
theorem domU_eq (j : Option s.P') : s.domU j = {u ∈ s.B | s.U u = upAff s j u} := by
  ext u
  simp only [Switch.domU, Set.mem_ofPred_eq, upAff_apply]

/-- Before the switch, the graph of `L` over a cell of `S` is a face (v4.60 l. 380-381). -/
theorem graph_L_isFace {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS) :
    IsFace (chainOrderPolytope P s.I) (graph s s.L C) := by
  obtain ⟨K, hK, -, hCK⟩ := hC
  have hX : IsFace (chainOrderPolytope P s.I) (graph s s.L (s.domL K)) := by
    rw [before_eq_prism s, domL_eq s K]
    obtain ⟨u, hu⟩ := hCK.1
    refine graph_lower_isFace s _ (fun v hv => (L_U_bounds s hv).2.1) (fun v _ => ?_)
      ⟨u, (hCK.subset hu).1, L_eq_on_domL s hCK.subset u hu⟩
    rw [LinearMap.coe_toAffineMap, chainLin_apply]
    exact chainSum_le_L s hK v
  exact IsFace.trans (chainOrderPolytope_isPolytope P s.I) hX
    (graph_face_of_face s _ (L_eq_on_domL s Set.Subset.rfl) hCK)

/-- Before the switch, the graph of `U` over a cell of `T` is a face (v4.60 l. 380-381). -/
theorem graph_U_isFace {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsT) :
    IsFace (chainOrderPolytope P s.I) (graph s s.U C) := by
  obtain ⟨j, hj, -, hCj⟩ := hC
  have hX : IsFace (chainOrderPolytope P s.I) (graph s s.U (s.domU j)) := by
    rw [before_eq_prism s, domU_eq s j]
    obtain ⟨u, hu⟩ := hCj.1
    refine graph_upper_isFace s _ (fun v hv => (L_U_bounds s hv).2.1) (fun v _ => ?_)
      ⟨u, (hCj.subset hu).1, U_eq_on_domU s hCj.subset u hu⟩
    rw [upAff_apply]
    exact U_le_upVal s hj v
  exact IsFace.trans (chainOrderPolytope_isPolytope P s.I) hX
    (graph_face_of_face s _ (U_eq_on_domU s Set.Subset.rfl) hCj)

/-- After the switch, the part of the facet `{z = 0}` over a face of `B` is a face (v4.60 l. 382). -/
theorem graph_zero_isFace_of_face {G : Set (s.P' → ℝ)} (hG : IsFace s.B G) :
    IsFace (chainOrderPolytope P (insert s.q s.I)) (graph s (fun _ => 0) G) := by
  have hB : {u ∈ s.B | (fun _ => (0 : ℝ)) u = AffineMap.const ℝ (s.P' → ℝ) (0 : ℝ) u} = s.B :=
    Set.ext fun _ => ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  obtain ⟨u, hu⟩ := hG.1
  have hX := graph_lower_isFace s (lo := fun _ => (0 : ℝ)) (hi := fun u => s.U u - s.L u) (base := s.B)
    (AffineMap.const ℝ (s.P' → ℝ) (0 : ℝ)) (fun v hv => sub_nonneg.2 (L_U_bounds s hv).2.1)
    (fun _ _ => le_rfl) ⟨u, hG.subset hu, rfl⟩
  rw [hB, ← after_eq_prism s] at hX
  exact IsFace.trans (chainOrderPolytope_isPolytope P _) hX
    (graph_face_of_face s (AffineMap.const ℝ (s.P' → ℝ) (0 : ℝ)) (fun _ _ => rfl) hG)

/-- The common affinity domain of the branch `K` of `L` and the branch `j` of `U`, written as the set where
`U − L` meets its affine bound `upVal j − ℓ_K` (v4.60 l. 346-348). -/
def domR (K : Finset s.P') (j : Option s.P') : Set (s.P' → ℝ) :=
  {u ∈ s.B | s.U u - s.L u = (upAff s j - (chainLin s K).toAffineMap) u}

/-- The affine bound `upVal j − ℓ_K` of `U − L` (v4.60 l. 346-348, 382-383). -/
theorem upAffSub_apply (K : Finset s.P') (j : Option s.P') (u : s.P' → ℝ) :
    (upAff s j - (chainLin s K).toAffineMap) u = s.upVal j u - s.chainSum K u := by
  rw [AffineMap.coe_sub, Pi.sub_apply, upAff_apply, LinearMap.coe_toAffineMap, chainLin_apply]

/-- Where `U − L` meets `upVal j − ℓ_K`, `L = ℓ_K` (v4.60 l. 346-348). -/
theorem domR_subset_domL {K : Finset s.P'} {j : Option s.P'} (hK : K ∈ s.lowBranches) (hj : j ∈ s.upBranches) :
    domR s K j ⊆ s.domL K := fun u hu => by
  have h1 := U_le_upVal s hj u
  have h2 := chainSum_le_L s hK u
  have h3 : s.U u - s.L u = s.upVal j u - s.chainSum K u := hu.2.trans (upAffSub_apply s K j u)
  exact ⟨hu.1, by linarith⟩

/-- Where `U − L` meets `upVal j − ℓ_K`, `U = upVal j` (v4.60 l. 346-348). -/
theorem domR_subset_domU {K : Finset s.P'} {j : Option s.P'} (hK : K ∈ s.lowBranches) (hj : j ∈ s.upBranches) :
    domR s K j ⊆ s.domU j := fun u hu => by
  have h1 := U_le_upVal s hj u
  have h2 := chainSum_le_L s hK u
  have h3 : s.U u - s.L u = s.upVal j u - s.chainSum K u := hu.2.trans (upAffSub_apply s K j u)
  exact ⟨hu.1, by linarith⟩

/-- A cell `A ∩ D` of `R` (v4.60 l. 346-348) lies where `U − L` meets `upVal j − ℓ_K`. -/
theorem inter_subset_domR {K : Finset s.P'} {j : Option s.P'} {A D : Set (s.P' → ℝ)} (hA : A ⊆ s.domL K)
    (hD : D ⊆ s.domU j) : A ∩ D ⊆ domR s K j := fun u hu => by
  have hL := (hA hu.1).2
  have hU := (hD hu.2).2
  refine ⟨(hA hu.1).1, ?_⟩
  rw [upAffSub_apply]
  linarith

/-- After the switch, the graph of `U − L` over a cell of `R` is a face (v4.60 l. 382-383): the cell `A ∩ D` is a face
of `domR K j` (exposed by the sum of the two exposing functionals), and the graph over `domR K j` is cut out by
`z ≤ upVal j − ℓ_K`. -/
theorem graph_UL_isFace {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsR) :
    IsFace (chainOrderPolytope P (insert s.q s.I)) (graph s (fun u => s.U u - s.L u) C) := by
  obtain ⟨⟨u0, hu0⟩, A, ⟨K, hK, -, hAK⟩, D, ⟨j, hj, -, hDj⟩, rfl⟩ := hC
  have hCX := inter_subset_domR s hAK.subset hDj.subset
  have hface : IsFace (domR s K j) (A ∩ D) := by
    have h1 := hAK.inter_subset (domR_subset_domL s hK hj) ⟨u0, hCX hu0, hu0.1⟩
    have h2 := hDj.inter_subset (domR_subset_domU s hK hj) ⟨u0, hCX hu0, hu0.2⟩
    have h3 := h1.inter h2 ⟨u0, ⟨hCX hu0, hu0.1⟩, ⟨hCX hu0, hu0.2⟩⟩
    have e : (domR s K j ∩ A) ∩ (domR s K j ∩ D) = A ∩ D := by
      ext u
      constructor
      · rintro ⟨⟨-, ha⟩, ⟨-, hd⟩⟩
        exact ⟨ha, hd⟩
      · intro hu
        exact ⟨⟨hCX hu, hu.1⟩, ⟨hCX hu, hu.2⟩⟩
    rwa [e] at h3
  have hX : IsFace (chainOrderPolytope P (insert s.q s.I)) (graph s (fun u => s.U u - s.L u) (domR s K j)) := by
    rw [after_eq_prism s]
    refine graph_upper_isFace s (lo := fun _ => (0 : ℝ)) (hi := fun u => s.U u - s.L u) _
      (fun v hv => sub_nonneg.2 (L_U_bounds s hv).2.1) (fun v _ => ?_) ⟨u0, (hCX hu0).1, (hCX hu0).2⟩
    rw [upAffSub_apply]
    linarith [U_le_upVal s hj v, chainSum_le_L s hK v]
  exact IsFace.trans (chainOrderPolytope_isPolytope P _) hX
    (graph_face_of_face s (upAff s j - (chainLin s K).toAffineMap) (fun u hu => hu.2) hface)

/-- The graph of `L` over a cell of `S` has the dimension of the cell (v4.60 l. 383). -/
theorem adim_graph_S {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsS) : adim (graph s s.L C) = adim C := by
  obtain ⟨K, -, -, hCK⟩ := hC
  exact adim_graph s _ (L_eq_on_domL s hCK.subset)

/-- The graph of `U` over a cell of `T` has the dimension of the cell (v4.60 l. 383). -/
theorem adim_graph_T {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsT) : adim (graph s s.U C) = adim C := by
  obtain ⟨j, -, -, hCj⟩ := hC
  exact adim_graph s _ (U_eq_on_domU s hCj.subset)

/-- The graph of `U − L` over a cell of `R` has the dimension of the cell (v4.60 l. 383). -/
theorem adim_graph_R {C : Set (s.P' → ℝ)} (hC : C ∈ s.cellsR) :
    adim (graph s (fun u => s.U u - s.L u) C) = adim C := by
  obtain ⟨-, A, ⟨K, -, -, hAK⟩, D, ⟨j, -, -, hDj⟩, rfl⟩ := hC
  exact adim_graph s (upAff s j - (chainLin s K).toAffineMap)
    (fun u hu => (inter_subset_domR s hAK.subset hDj.subset hu).2)

end Cells

section Counting

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The non-vertical `k`-faces before the switch: graphs of `L` over `k`-cells of `S` and of `U` over `k`-cells of
`T` (v4.60 l. 380-381). -/
theorem nonvertical_before_eq (k : ℕ) :
    {F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ ¬ HasVertical s F} =
      graph s s.L '' {A ∈ s.cellsS | adim A = k} ∪ graph s s.U '' {A ∈ s.cellsT | adim A = k} := by
  ext F
  constructor
  · rintro ⟨hF, hk, hv⟩
    rcases informal_before_graph_proved s F hF hv with ⟨C, hC, e⟩ | ⟨C, hC, e⟩
    · have e' : F = graph s s.L C := e
      subst e'
      exact Or.inl ⟨C, ⟨hC, (adim_graph_S s hC).symm.trans hk⟩, rfl⟩
    · have e' : F = graph s s.U C := e
      subst e'
      exact Or.inr ⟨C, ⟨hC, (adim_graph_T s hC).symm.trans hk⟩, rfl⟩
  · rintro (⟨C, ⟨hC, hk⟩, rfl⟩ | ⟨C, ⟨hC, hk⟩, rfl⟩)
    · exact ⟨graph_L_isFace s hC, (adim_graph_S s hC).trans hk, not_hasVertical_graph s _ _⟩
    · exact ⟨graph_U_isFace s hC, (adim_graph_T s hC).trans hk, not_hasVertical_graph s _ _⟩

/-- The faces of both kinds before the switch: graphs of `L` over the `k`-faces of `B` with `L = U` (v4.60 l. 383). -/
theorem inter_before_eq (k : ℕ) :
    graph s s.L '' {A ∈ s.cellsS | adim A = k} ∩ graph s s.U '' {A ∈ s.cellsT | adim A = k} =
      graph s s.L '' eqFaces s k := by
  ext F
  constructor
  · rintro ⟨⟨C, ⟨hC, hk⟩, rfl⟩, ⟨D, ⟨hD, -⟩, e⟩⟩
    obtain ⟨G, hG, hLU, e2⟩ := (both_before s (graph s s.L C)).1
      ⟨graph_L_isFace s hC, ⟨C, hC, rfl⟩, ⟨D, hD, e.symm⟩⟩
    have hCG : C = G := eq_of_graph_eq s (f := s.L) (f' := s.L) e2
    subst hCG
    exact ⟨_, ⟨hG, hLU, hk⟩, rfl⟩
  · rintro ⟨G, ⟨hG, hLU, hk⟩, rfl⟩
    obtain ⟨-, hS, hT⟩ := face_mem_cells s hG hLU
    exact ⟨⟨G, ⟨hS, hk⟩, rfl⟩, ⟨G, ⟨hT, hk⟩, (graph_congr s hLU).symm⟩⟩

/-- Inclusion-exclusion before the switch: non-vertical `k`-faces plus both-kind ones = `k`-cells of `S` and of `T`
(v4.60 l. 380-383). -/
theorem count_before (k : ℕ) :
    {F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard + (eqFaces s k).ncard =
      cellNum s.cellsS k + cellNum s.cellsT k := by
  have hfin1 : (graph s s.L '' {A ∈ s.cellsS | adim A = k}).Finite :=
    (chainOrderPolytope_isPolytope P s.I).finite_faces.subset (by
      rintro _ ⟨C, ⟨hC, -⟩, rfl⟩
      exact graph_L_isFace s hC)
  have hfin2 : (graph s s.U '' {A ∈ s.cellsT | adim A = k}).Finite :=
    (chainOrderPolytope_isPolytope P s.I).finite_faces.subset (by
      rintro _ ⟨C, ⟨hC, -⟩, rfl⟩
      exact graph_U_isFace s hC)
  have h := Set.ncard_union_add_ncard_inter _ _ hfin1 hfin2
  rw [← nonvertical_before_eq, inter_before_eq, (graph_injOn s s.L (eqFaces s k)).ncard_image,
    (graph_injOn s s.L _).ncard_image, (graph_injOn s s.U _).ncard_image] at h
  exact h

/-- The non-vertical `k`-faces after the switch: parts of `{z = 0}` over `k`-faces of `B` and graphs of `U − L`
over `k`-cells of `R` (v4.60 l. 382-383). -/
theorem nonvertical_after_eq (k : ℕ) :
    {F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ ¬ HasVertical s F} =
      graph s (fun _ => 0) '' {G | IsFace s.B G ∧ adim G = k} ∪
        graph s (fun u => s.U u - s.L u) '' {A ∈ s.cellsR | adim A = k} := by
  ext F
  constructor
  · rintro ⟨hF, hk, hv⟩
    rcases informal_after_graph_proved s F hF hv with ⟨G, hG, e⟩ | ⟨C, hC, e⟩
    · have e' : F = graph s (fun _ => 0) G := e
      subst e'
      exact Or.inl ⟨G, ⟨hG, (adim_graph_zero s G).symm.trans hk⟩, rfl⟩
    · have e' : F = graph s (fun u => s.U u - s.L u) C := e
      subst e'
      exact Or.inr ⟨C, ⟨hC, (adim_graph_R s hC).symm.trans hk⟩, rfl⟩
  · rintro (⟨G, ⟨hG, hk⟩, rfl⟩ | ⟨C, ⟨hC, hk⟩, rfl⟩)
    · exact ⟨graph_zero_isFace_of_face s hG, (adim_graph_zero s G).trans hk, not_hasVertical_graph s _ _⟩
    · exact ⟨graph_UL_isFace s hC, (adim_graph_R s hC).trans hk, not_hasVertical_graph s _ _⟩

/-- The faces of both kinds after the switch: parts of `{z = 0}` over the `k`-faces of `B` with `L = U`
(v4.60 l. 383). -/
theorem inter_after_eq (k : ℕ) :
    graph s (fun _ => 0) '' {G | IsFace s.B G ∧ adim G = k} ∩
        graph s (fun u => s.U u - s.L u) '' {A ∈ s.cellsR | adim A = k} =
      graph s (fun _ => 0) '' eqFaces s k := by
  ext F
  constructor
  · rintro ⟨⟨G, ⟨hG, hk⟩, rfl⟩, ⟨C, ⟨hC, -⟩, e⟩⟩
    obtain ⟨G', hG', hLU, e2⟩ := (both_after s (graph s (fun _ => 0) G)).1
      ⟨graph_zero_isFace_of_face s hG, ⟨G, hG, rfl⟩, ⟨C, hC, e.symm⟩⟩
    have hGG : G = G' := eq_of_graph_eq s (f := fun _ => (0 : ℝ)) (f' := fun _ => (0 : ℝ)) e2
    subst hGG
    exact ⟨_, ⟨hG', hLU, hk⟩, rfl⟩
  · rintro ⟨G, ⟨hG, hLU, hk⟩, rfl⟩
    refine ⟨⟨G, ⟨hG, hk⟩, rfl⟩, ⟨G, ⟨face_mem_cellsR s hG hLU, hk⟩, ?_⟩⟩
    exact graph_congr s (f := fun u => s.U u - s.L u) (f' := fun _ => (0 : ℝ))
      (fun u hu => by simp [hLU u hu])

/-- Inclusion-exclusion after the switch: non-vertical `k`-faces plus both-kind ones = `k`-faces of `B` and `k`-cells
of `R` (v4.60 l. 382-383). -/
theorem count_after (k : ℕ) :
    {F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard +
        (eqFaces s k).ncard = fNum s.B k + cellNum s.cellsR k := by
  have hfin1 : (graph s (fun _ => 0) '' {G | IsFace s.B G ∧ adim G = k}).Finite :=
    (chainOrderPolytope_isPolytope P (insert s.q s.I)).finite_faces.subset (by
      rintro _ ⟨G, ⟨hG, -⟩, rfl⟩
      exact graph_zero_isFace_of_face s hG)
  have hfin2 : (graph s (fun u => s.U u - s.L u) '' {A ∈ s.cellsR | adim A = k}).Finite :=
    (chainOrderPolytope_isPolytope P (insert s.q s.I)).finite_faces.subset (by
      rintro _ ⟨C, ⟨hC, -⟩, rfl⟩
      exact graph_UL_isFace s hC)
  have h := Set.ncard_union_add_ncard_inter _ _ hfin1 hfin2
  rw [← nonvertical_after_eq, inter_after_eq, (graph_injOn s (fun _ => 0) (eqFaces s k)).ncard_image,
    (graph_injOn s (fun _ => 0) _).ncard_image, (graph_injOn s (fun u => s.U u - s.L u) _).ncard_image] at h
  exact h

end Counting

/-- **Paper v4.60 l. 380-384** (informal reading of the first equality of Lemma 3.2, l. 373-376): in each dimension
`k`, the number of faces with no segment parallel to the `z`-axis grows across the switch by the `k`-th coefficient of
`F_B + F_R − F_S − F_T`. Before the switch these faces are the graphs of `L` over the cells of `S` and of `U` over the
cells of `T`; after it, the parts of the facet `{z = 0}` over the faces of `B` and the graphs of `U − L` over the cells
of `R`; in both, the faces of both kinds are those over the faces of `B` on which `L = U`. -/
theorem nonvertical_coefficient_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (k : ℕ) :
    ({F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard : ℤ) -
      ({F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard : ℤ) =
        (facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT).coeff k := by
  have hb := count_before s k
  have ha := count_after s k
  simp only [coeff_sub, coeff_add, facePoly_coeff, cellPoly_coeff]
  omega

/-- **Paper v4.60 l. 383** (informal reading of Lemma 3.2): "the first equality of Lemma 3.2 is equivalent to the
statement that the two polytopes have, in each dimension, the same number of faces that contain such a segment"
(a segment parallel to the `z`-axis; the first equality is l. 373-376). -/
theorem informal_equivalence_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT) ↔
    ∀ k : ℕ, {F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ HasVertical s F}.ncard =
      {F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ HasVertical s F}.ncard := by
  constructor
  · intro h k
    have h1 := nonvertical_coefficient_proved s k
    have before := fNum_vertical_partition s (chainOrderPolytope P s.I) (chainOrderPolytope_isPolytope P s.I) k
    have after := fNum_vertical_partition s (chainOrderPolytope P (insert s.q s.I))
      (chainOrderPolytope_isPolytope P (insert s.q s.I)) k
    have total : (facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I)).coeff k =
        (facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT).coeff k := by
      rw [h]
    rw [coeff_sub (facePoly (chainOrderPolytope P (insert s.q s.I))) (facePoly (chainOrderPolytope P s.I)),
      facePoly_coeff, facePoly_coeff] at total
    omega
  · intro hv
    ext k
    have h1 := nonvertical_coefficient_proved s k
    have before := fNum_vertical_partition s (chainOrderPolytope P s.I) (chainOrderPolytope_isPolytope P s.I) k
    have after := fNum_vertical_partition s (chainOrderPolytope P (insert s.q s.I))
      (chainOrderPolytope_isPolytope P (insert s.q s.I)) k
    have vertical := hv k
    rw [coeff_sub (facePoly (chainOrderPolytope P (insert s.q s.I))) (facePoly (chainOrderPolytope P s.I)),
      facePoly_coeff, facePoly_coeff]
    omega

/-- **Paper v4.60 l. 373-376** (Lemma 3.2, first equality; Fourier's Lemma 4.1):
`F_{O_{I∪{q}}(P)} − F_{O_I(P)} = F_B + F_R − F_S − F_T`. Proved as the paper's informal reading (l. 380-384) says: the
faces containing a segment parallel to the `z`-axis are equally many before and after, in each dimension, and the other
faces are counted by the cells (`nonvertical_coefficient_proved`). -/
theorem fourier_lemma_4_1_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT :=
  (informal_equivalence_proved s).2 (sec3_informal_vertical_count s)

end HibiLi.Proofs.Fourier41

end
