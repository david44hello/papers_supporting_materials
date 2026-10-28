/-
HibiLi/Proofs/Informal.lean — the informal reading of paper v2.10 l. 435-441 (review REVIEW_006_cov, item B5(a),
sentences 1-2): a face of `O_I(P)` (resp. `O_{I∪{q}}(P)`) that contains no segment parallel to the `z`-axis lies in the
graph of `L` over a cell of `S` or of `U` over a cell of `T` (resp. in `{z = 0}` over a face of `B` or in the graph of
`U − L` over a cell of `R`). `HasVertical` and sentence 3 (the vertical-face count) are in `Proofs/VerticalCount.lean`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.VerticalCount
import HibiLi.Proofs.Lemma42
import HibiLi.Polytope.DomainCover
import HibiLi.Polytope.CellGeometry
import HibiLi.Polytope.ChainOrder
import HibiLi.Polytope.Faces

noncomputable section

namespace HibiLi.Proofs.Informal

open HibiLi

/-! ### A function that is affine along a convex set and vanishes at a relative interior point -/

section Vanish

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `h` is affine along the segments of `G`. -/
def AffAlong (G : Set V) (h : V → ℝ) : Prop :=
  ∀ w ∈ G, ∀ v ∈ G, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → h (a • w + b • v) = a * h w + b * h v

/-- A function that is nonnegative on `G`, affine along `G`, and zero at a relative interior point of `G`, is zero on
`G` (v2.10 l. 405-406: "an affine function that is nonnegative on a convex set and vanishes at one of its relative
interior points vanishes on the whole set"). -/
theorem eq_zero_of_relint {G : Set V} {u0 : V} (hu0 : u0 ∈ intrinsicInterior ℝ G) {h : V → ℝ}
    (hnn : ∀ v ∈ G, 0 ≤ h v) (h0 : h u0 = 0) (haff : AffAlong G h) : ∀ v ∈ G, h v = 0 := by
  intro v hv
  obtain ⟨ε, hε, hball⟩ := L42.exists_ball hu0 self_mem_nhdsWithin
  have hd : u0 - v ∈ vectorSpan ℝ G := vsub_mem_vectorSpan ℝ (intrinsicInterior_subset hu0) hv
  obtain ⟨r, hr, -, hrd⟩ := L42.exists_small hε (norm_nonneg (u0 - v))
  have hw : u0 + r • (u0 - v) ∈ G :=
    hball _ (Submodule.smul_mem _ r hd) (by rw [L42.norm_smul_of_pos hr]; exact hrd)
  have h1r : (1 + r) ≠ 0 := by positivity
  have hcomb : (1 / (1 + r)) • (u0 + r • (u0 - v)) + (r / (1 + r)) • v = u0 := by
    match_scalars <;> field_simp
    ring
  have hb : 0 < r / (1 + r) := by positivity
  have key := haff _ hw v hv (1 / (1 + r)) (r / (1 + r)) (by positivity) hb.le (by field_simp)
  rw [hcomb, h0] at key
  have hw0 := hnn _ hw
  have hv0 := hnn v hv
  have hmul : r / (1 + r) * h v = 0 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / (1 + r) by positivity) hw0, mul_nonneg hb.le hv0]
  exact (mul_eq_zero.1 hmul).resolve_left hb.ne'

end Vanish

/-! ### Affine along a convex set: inside one full-dimensional affinity domain -/

section Domains

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- If `U` is affine along a nonempty convex `G ⊆ B`, then `G` lies in one full-dimensional affinity domain of `U`. -/
theorem domU_of_affAlong {G : Set (s.P' → ℝ)} (hconv : Convex ℝ G) (hne : G.Nonempty) (hGB : G ⊆ s.B)
    (haff : AffAlong G s.U) : ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ G ⊆ s.domU j := by
  obtain ⟨u0, hu0⟩ := hne.intrinsicInterior hconv
  obtain ⟨⟨C, j, hj, hfull, hface⟩, hu0C⟩ := Set.mem_iUnion.mp (s.cellsT_cover (hGB (intrinsicInterior_subset hu0)))
  have hu0j : u0 ∈ s.domU j := hface.2.subset hu0C
  refine ⟨j, hj, hfull, fun v hv => ⟨hGB hv, ?_⟩⟩
  have hzero := eq_zero_of_relint hu0 (h := fun u => s.upVal j u - s.U u)
    (fun u _ => sub_nonneg.2 (U_le_upVal s hj u)) (by rw [hu0j.2, sub_self])
    (fun w _ v _ a b _ _ hab => by
      beta_reduce
      rw [upVal_add_smul s j w v a b hab, haff w ‹_› v ‹_› a b ‹_› ‹_› hab]
      ring) v hv
  beta_reduce at hzero
  linarith

/-- If `L` is affine along a nonempty convex `G ⊆ B`, then `G` lies in one full-dimensional affinity domain of `L`. -/
theorem domL_of_affAlong {G : Set (s.P' → ℝ)} (hconv : Convex ℝ G) (hne : G.Nonempty) (hGB : G ⊆ s.B)
    (haff : AffAlong G s.L) : ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ G ⊆ s.domL K := by
  obtain ⟨u0, hu0⟩ := hne.intrinsicInterior hconv
  obtain ⟨⟨C, K, hK, hfull, hface⟩, hu0C⟩ := Set.mem_iUnion.mp (s.cellsS_cover (hGB (intrinsicInterior_subset hu0)))
  have hu0K : u0 ∈ s.domL K := hface.2.subset hu0C
  refine ⟨K, hK, hfull, fun v hv => ⟨hGB hv, ?_⟩⟩
  have hzero := eq_zero_of_relint hu0 (h := fun u => s.L u - s.chainSum K u)
    (fun u _ => sub_nonneg.2 (chainSum_le_L s hK u)) (by rw [hu0K.2, sub_self])
    (fun w _ v _ a b _ _ hab => by
      beta_reduce
      rw [chainSum_add_smul s K w v a b, haff w ‹_› v ‹_› a b ‹_› ‹_› hab]
      ring) v hv
  beta_reduce at hzero
  linarith

/-- If `U − L` is affine along `G`, so are `U` (concave) and `L` (convex). -/
theorem affAlong_split {G : Set (s.P' → ℝ)} (h : AffAlong G (fun u => s.U u - s.L u)) :
    AffAlong G s.U ∧ AffAlong G s.L := by
  have key : ∀ w ∈ G, ∀ v ∈ G, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      s.U (a • w + b • v) = a * s.U w + b * s.U v ∧ s.L (a • w + b • v) = a * s.L w + b * s.L v := by
    intro w hw v hv a b ha hb hab
    have h1 := h w hw v hv a b ha hb hab
    have h2 := (U_concave s).2 (Set.mem_univ w) (Set.mem_univ v) ha hb hab
    have h3 := (L_convex s).2 (Set.mem_univ w) (Set.mem_univ v) ha hb hab
    simp only [smul_eq_mul] at h2 h3
    beta_reduce at h1
    constructor <;> linarith
  exact ⟨fun w hw v hv a b ha hb hab => (key w hw v hv a b ha hb hab).1,
    fun w hw v hv a b ha hb hab => (key w hw v hv a b ha hb hab).2⟩

end Domains

/-! ### Faces of the two polytopes and vertical moves -/

section Faces

open Classical

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The projection `x ↦ (x_p)_{p ≠ q}`. -/
def projL : (P → ℝ) →ₗ[ℝ] (s.P' → ℝ) where
  toFun x p := x p.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The lift `u ↦ (u, 0)` (the `q`-coordinate set to `0`). -/
def liftL : (s.P' → ℝ) →ₗ[ℝ] (P → ℝ) where
  toFun u p := if h : p = s.q then 0 else u ⟨p, h⟩
  map_add' u v := by
    funext p
    by_cases h : p = s.q <;> simp [h]
  map_smul' a u := by
    funext p
    by_cases h : p = s.q <;> simp [h]

theorem proj_lift (u : s.P' → ℝ) : (fun p : s.P' => liftL s u p.1) = u := by
  funext p
  simp [liftL, p.2]

theorem lift_q (u : s.P' → ℝ) : liftL s u s.q = 0 := by
  simp [liftL]

theorem decomp (y : P → ℝ) : y = liftL s (fun p : s.P' => y p.1) + y s.q • Pi.single s.q 1 := by
  funext p
  by_cases h : p = s.q
  · subst h
    simp [liftL]
  · simp [liftL, h]

theorem proj_add_single (x : P → ℝ) (t : ℝ) :
    (fun p : s.P' => (x + t • (Pi.single s.q (1 : ℝ) : P → ℝ)) p.1) = fun p => x p.1 := by
  funext p
  simp [p.2]

theorem q_add_single (x : P → ℝ) (t : ℝ) : (x + t • (Pi.single s.q (1 : ℝ) : P → ℝ)) s.q = x s.q + t := by
  simp

/-- On a face `F` exposed by `l`, a vertical move that stays in the polytope does not increase `l`. -/
theorem move_le {Q F : Set (P → ℝ)} {l : StrongDual ℝ (P → ℝ)} (hl : F = {x ∈ Q | ∀ y ∈ Q, l y ≤ l x})
    {x : P → ℝ} (hx : x ∈ F) {t : ℝ} (ht : x + t • Pi.single s.q 1 ∈ Q) : t * l (Pi.single s.q 1) ≤ 0 := by
  rw [hl] at hx
  have h := hx.2 _ ht
  rw [map_add, map_smul, smul_eq_mul] at h
  linarith

/-- If `l` vanishes on the vertical direction, a vertical move that stays in the polytope stays in `F`. -/
theorem move_mem {Q F : Set (P → ℝ)} {l : StrongDual ℝ (P → ℝ)} (hl : F = {x ∈ Q | ∀ y ∈ Q, l y ≤ l x})
    {x : P → ℝ} (hx : x ∈ F) {t : ℝ} (ht : x + t • Pi.single s.q 1 ∈ Q) (hc : l (Pi.single s.q 1) = 0) :
    x + t • Pi.single s.q 1 ∈ F := by
  rw [hl] at hx ⊢
  refine ⟨ht, fun y hy => ?_⟩
  rw [map_add, map_smul, smul_eq_mul, hc, mul_zero, add_zero]
  exact hx.2 y hy

/-- A function whose graph contains the convex set `F` is affine along the projection of `F`. -/
theorem affAlong_of_graph {F : Set (P → ℝ)} (hFconv : Convex ℝ F) {f : (s.P' → ℝ) → ℝ}
    (hgraph : ∀ x ∈ F, x s.q = f (fun p : s.P' => x p.1)) : AffAlong (projL s '' F) f := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  have hx' : x s.q = f (projL s x) := hgraph x hx
  have hy' : y s.q = f (projL s y) := hgraph y hy
  have hxy : (a • x + b • y) s.q = f (projL s (a • x + b • y)) := hgraph _ (hFconv hx hy ha hb hab)
  rw [map_add, map_smul, map_smul] at hxy
  rw [← hxy, ← hx', ← hy']
  simp

/-- The projection of a face `F` of `O_{I∪{q}}(P)` that lies in `{z = 0}` is a face of `B` (exposed by `l ∘ lift`, where
`l` exposes `F`). -/
theorem after_face {F : Set (P → ℝ)} {l : StrongDual ℝ (P → ℝ)} (hne : F.Nonempty)
    (hl : F = {x ∈ chainOrderPolytope P (insert s.q s.I) | ∀ y ∈ chainOrderPolytope P (insert s.q s.I), l y ≤ l x})
    (hzero : ∀ x ∈ F, x s.q = 0) : IsFace s.B (projL s '' F) := by
  let a : StrongDual ℝ (s.P' → ℝ) := l.comp (LinearMap.toContinuousLinearMap (liftL s))
  have ha : ∀ u, a u = l (liftL s u) := fun u => rfl
  have hlift : ∀ u ∈ s.B, liftL s u ∈ chainOrderPolytope P (insert s.q s.I) := by
    intro u hu
    refine (prop_3_1_proved s _).2.2 ⟨?_, ?_, ?_⟩
    · rw [proj_lift]
      exact hu
    · rw [lift_q]
    · rw [lift_q, proj_lift]
      linarith [(L_U_bounds s hu).2.1]
  have hly : ∀ y : P → ℝ, l y = a (fun p : s.P' => y p.1) + y s.q * l (Pi.single s.q 1) := by
    intro y
    conv_lhs => rw [decomp s y]
    rw [map_add, map_smul, smul_eq_mul, ha]
  refine ⟨hne.image _, fun _ => ⟨a, ?_⟩⟩
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxF := hx
    rw [hl] at hx
    refine ⟨((prop_3_1_proved s x).2.1 hx.1).1, fun v hv => ?_⟩
    have h1 := hx.2 _ (hlift v hv)
    rw [hly x, hzero x hxF, zero_mul, add_zero, ← ha] at h1
    exact h1
  · rintro ⟨hu, hmax⟩
    refine ⟨liftL s u, ?_, proj_lift s u⟩
    obtain ⟨x0, hx0⟩ := hne
    have hx0F := hx0
    rw [hl] at hx0 ⊢
    refine ⟨hlift u hu, fun y hy => ?_⟩
    have h1 := hx0.2 y hy
    have h2 := hmax _ ((prop_3_1_proved s x0).2.1 hx0.1).1
    rw [hly x0, hzero x0 hx0F, zero_mul, add_zero] at h1
    rw [← ha]
    linarith

/-- v2.10 l. 435-437: a face of `O_I(P)` with no vertical segment lies in the graph of `L` or in the graph of `U`. -/
theorem before_graph {F : Set (P → ℝ)} (hF : IsFace (chainOrderPolytope P s.I) F) (hv : ¬ HasVertical s F) :
    (∀ x ∈ F, x s.q = s.L (fun p : s.P' => x p.1)) ∨ (∀ x ∈ F, x s.q = s.U (fun p : s.P' => x p.1)) := by
  obtain ⟨l, hl⟩ := hF.2 hF.1
  have hFQ : F ⊆ chainOrderPolytope P s.I := hF.2.subset
  have hfib : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B ∧ s.L (fun p : s.P' => x p.1) ≤ x s.q ∧
      x s.q ≤ s.U (fun p : s.P' => x p.1) := fun x hx => (prop_3_1_proved s x).1.1 (hFQ hx)
  have hmove : ∀ x ∈ F, ∀ z, s.L (fun p : s.P' => x p.1) ≤ z → z ≤ s.U (fun p : s.P' => x p.1) →
      x + (z - x s.q) • Pi.single s.q 1 ∈ chainOrderPolytope P s.I := by
    intro x hx z hz1 hz2
    refine (prop_3_1_proved s _).1.2 ⟨?_, ?_, ?_⟩
    · rw [proj_add_single s]
      exact (hfib x hx).1
    · rw [proj_add_single s, q_add_single s]
      linarith
    · rw [proj_add_single s, q_add_single s]
      linarith
  rcases lt_trichotomy (l (Pi.single s.q 1)) 0 with hc | hc | hc
  · left
    intro x hx
    by_contra hne
    have hlt : s.L (fun p : s.P' => x p.1) < x s.q := lt_of_le_of_ne (hfib x hx).2.1 (Ne.symm hne)
    have h1 := move_le s hl hx (hmove x hx _ le_rfl ((hfib x hx).2.1.trans (hfib x hx).2.2))
    nlinarith
  · left
    intro x hx
    by_contra hne
    exact hv ⟨x, hx, _, sub_ne_zero.2 (Ne.symm hne),
      move_mem s hl hx (hmove x hx _ le_rfl ((hfib x hx).2.1.trans (hfib x hx).2.2)) hc⟩
  · right
    intro x hx
    by_contra hne
    have hlt : x s.q < s.U (fun p : s.P' => x p.1) := lt_of_le_of_ne (hfib x hx).2.2 hne
    have h1 := move_le s hl hx (hmove x hx _ ((hfib x hx).2.1.trans (hfib x hx).2.2) le_rfl)
    nlinarith

/-- A convex `F` (over `B`) in the graph of `L` lies over one cell of `S`: a full-dimensional affinity domain of `L`
(v2.10 l. 371-373, with `dim F` in place of `n − 1`; relative interior argument). -/
theorem cellS_of_graph {F : Set (P → ℝ)} (hFconv : Convex ℝ F) (hne : F.Nonempty)
    (hFB : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B) (hL : ∀ x ∈ F, x s.q = s.L (fun p : s.P' => x p.1)) :
    ∃ C ∈ s.cellsS, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)} := by
  have hGB : projL s '' F ⊆ s.B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hFB x hx
  obtain ⟨K, hK, hfull, hsub⟩ := domL_of_affAlong s (hFconv.linear_image (projL s)) (hne.image _) hGB
    (affAlong_of_graph s hFconv hL)
  obtain ⟨x0, hx0⟩ := hne
  exact ⟨s.domL K, ⟨K, hK, hfull, IsFace.refl ⟨_, hsub ⟨x0, hx0, rfl⟩⟩⟩, fun x hx => ⟨hsub ⟨x, hx, rfl⟩, hL x hx⟩⟩

/-- A convex `F` (over `B`) in the graph of `U` lies over one cell of `T`. -/
theorem cellT_of_graph {F : Set (P → ℝ)} (hFconv : Convex ℝ F) (hne : F.Nonempty)
    (hFB : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B) (hU : ∀ x ∈ F, x s.q = s.U (fun p : s.P' => x p.1)) :
    ∃ C ∈ s.cellsT, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)} := by
  have hGB : projL s '' F ⊆ s.B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hFB x hx
  obtain ⟨j, hj, hfull, hsub⟩ := domU_of_affAlong s (hFconv.linear_image (projL s)) (hne.image _) hGB
    (affAlong_of_graph s hFconv hU)
  obtain ⟨x0, hx0⟩ := hne
  exact ⟨s.domU j, ⟨j, hj, hfull, IsFace.refl ⟨_, hsub ⟨x0, hx0, rfl⟩⟩⟩, fun x hx => ⟨hsub ⟨x, hx, rfl⟩, hU x hx⟩⟩

/-- A convex `F` (over `B`) in the graph of `U − L` lies over one cell `A_ℓ ∩ A'_j` of `R`. -/
theorem cellR_of_graph {F : Set (P → ℝ)} (hFconv : Convex ℝ F) (hne : F.Nonempty)
    (hFB : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B)
    (hg : ∀ x ∈ F, x s.q = s.U (fun p : s.P' => x p.1) - s.L (fun p : s.P' => x p.1)) :
    ∃ C ∈ s.cellsR, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧
      x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)} := by
  have hGconv : Convex ℝ (projL s '' F) := hFconv.linear_image (projL s)
  have hGne : (projL s '' F).Nonempty := hne.image _
  have hGB : projL s '' F ⊆ s.B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hFB x hx
  obtain ⟨hU, hL⟩ := affAlong_split s (affAlong_of_graph s hFconv (f := fun u => s.U u - s.L u) hg)
  obtain ⟨K, hK, hKfull, hKsub⟩ := domL_of_affAlong s hGconv hGne hGB hL
  obtain ⟨j, hj, hjfull, hjsub⟩ := domU_of_affAlong s hGconv hGne hGB hU
  obtain ⟨x0, hx0⟩ := hne
  exact ⟨s.domL K ∩ s.domU j,
    ⟨⟨_, hKsub ⟨x0, hx0, rfl⟩, hjsub ⟨x0, hx0, rfl⟩⟩, s.domL K,
      ⟨K, hK, hKfull, IsFace.refl ⟨_, hKsub ⟨x0, hx0, rfl⟩⟩⟩, s.domU j,
      ⟨j, hj, hjfull, IsFace.refl ⟨_, hjsub ⟨x0, hx0, rfl⟩⟩⟩, rfl⟩,
    fun x hx => ⟨⟨hKsub ⟨x, hx, rfl⟩, hjsub ⟨x, hx, rfl⟩⟩, hg x hx⟩⟩

/-- **v2.10 l. 435-437, sentence 1** ("An informal reading (not used below)"): a face of `O_I(P)` that contains no
segment parallel to the `z`-axis lies in the graph of `L` over a cell of `S`, or in the graph of `U` over a cell of `T`,
or in both; the last case occurs exactly over the set where `L = U`. -/
theorem informal_before (F : Set (P → ℝ)) (hF : IsFace (chainOrderPolytope P s.I) F) (hv : ¬ HasVertical s F) :
    ((∃ C ∈ s.cellsS, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∨
     (∃ C ∈ s.cellsT, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})) ∧
    (((∃ C ∈ s.cellsS, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
      (∃ C ∈ s.cellsT, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})) ↔
      ∀ x ∈ F, s.L (fun p => x p.1) = s.U (fun p => x p.1)) := by
  have hFQ : F ⊆ chainOrderPolytope P s.I := hF.2.subset
  have hFconv : Convex ℝ F := hF.2.convex (chainOrderPolytope_isPolytope P s.I).convex
  have hfib : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B ∧ s.L (fun p : s.P' => x p.1) ≤ x s.q ∧
      x s.q ≤ s.U (fun p : s.P' => x p.1) := fun x hx => (prop_3_1_proved s x).1.1 (hFQ hx)
  have hFB : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B := fun x hx => (hfib x hx).1
  refine ⟨?_, ?_⟩
  · rcases before_graph s hF hv with hL | hU
    · exact Or.inl (cellS_of_graph s hFconv hF.1 hFB hL)
    · exact Or.inr (cellT_of_graph s hFconv hF.1 hFB hU)
  · constructor
    · rintro ⟨⟨C, -, hC⟩, ⟨D, -, hD⟩⟩ x hx
      exact (hC hx).2.symm.trans (hD hx).2
    · intro h
      have hL : ∀ x ∈ F, x s.q = s.L (fun p : s.P' => x p.1) := fun x hx => by
        linarith [(hfib x hx).2.1, (hfib x hx).2.2, h x hx]
      have hU : ∀ x ∈ F, x s.q = s.U (fun p : s.P' => x p.1) := fun x hx => by
        linarith [(hfib x hx).2.1, (hfib x hx).2.2, h x hx]
      exact ⟨cellS_of_graph s hFconv hF.1 hFB hL, cellT_of_graph s hFconv hF.1 hFB hU⟩

/-- **v2.10 l. 437-439, sentence 2**: after the switch, a face of `O_{I∪{q}}(P)` that contains no segment parallel to
the `z`-axis lies in the facet `{z = 0}` over a face of `B`, or in the graph of `U − L` over a cell of `R`, or in both;
again the last case occurs exactly over the set where `L = U`. -/
theorem informal_after (F : Set (P → ℝ)) (hF : IsFace (chainOrderPolytope P (insert s.q s.I)) F)
    (hv : ¬ HasVertical s F) :
    ((∃ G, IsFace s.B G ∧ F ⊆ {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∨
     (∃ C ∈ s.cellsR, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧
        x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})) ∧
    (((∃ G, IsFace s.B G ∧ F ⊆ {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
      (∃ C ∈ s.cellsR, F ⊆ {x | (fun p : s.P' => x p.1) ∈ C ∧
        x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})) ↔
      ∀ x ∈ F, s.L (fun p => x p.1) = s.U (fun p => x p.1)) := by
  have hFQ : F ⊆ chainOrderPolytope P (insert s.q s.I) := hF.2.subset
  have hFconv : Convex ℝ F := hF.2.convex (chainOrderPolytope_isPolytope P (insert s.q s.I)).convex
  have hfib : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B ∧ 0 ≤ x s.q ∧
      x s.q ≤ s.U (fun p : s.P' => x p.1) - s.L (fun p : s.P' => x p.1) :=
    fun x hx => (prop_3_1_proved s x).2.1 (hFQ hx)
  have hFB : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B := fun x hx => (hfib x hx).1
  have hmove : ∀ x ∈ F, ∀ z, 0 ≤ z → z ≤ s.U (fun p : s.P' => x p.1) - s.L (fun p : s.P' => x p.1) →
      x + (z - x s.q) • Pi.single s.q 1 ∈ chainOrderPolytope P (insert s.q s.I) := by
    intro x hx z hz1 hz2
    refine (prop_3_1_proved s _).2.2 ⟨?_, ?_, ?_⟩
    · rw [proj_add_single s]
      exact (hfib x hx).1
    · rw [q_add_single s]
      linarith
    · rw [proj_add_single s, q_add_single s]
      linarith
  obtain ⟨l, hl⟩ := hF.2 hF.1
  refine ⟨?_, ?_⟩
  · rcases le_or_gt (l (Pi.single s.q 1)) 0 with hc | hc
    · have hzero : ∀ x ∈ F, x s.q = 0 := by
        intro x hx
        by_contra hne
        have hpos : 0 < x s.q := lt_of_le_of_ne (hfib x hx).2.1 (Ne.symm hne)
        have hm := hmove x hx 0 le_rfl ((hfib x hx).2.1.trans (hfib x hx).2.2)
        rcases hc.lt_or_eq with hneg | heq
        · have h1 := move_le s hl hx hm
          nlinarith
        · exact hv ⟨x, hx, _, by linarith, move_mem s hl hx hm heq⟩
      exact Or.inl ⟨projL s '' F, after_face s hF.1 hl hzero, fun x hx => ⟨⟨x, hx, rfl⟩, hzero x hx⟩⟩
    · have hgraph : ∀ x ∈ F, x s.q = s.U (fun p : s.P' => x p.1) - s.L (fun p : s.P' => x p.1) := by
        intro x hx
        by_contra hne
        have hlt := lt_of_le_of_ne (hfib x hx).2.2 hne
        have h1 := move_le s hl hx (hmove x hx _ ((hfib x hx).2.1.trans (hfib x hx).2.2) le_rfl)
        nlinarith
      exact Or.inr (cellR_of_graph s hFconv hF.1 hFB hgraph)
  · constructor
    · rintro ⟨⟨G, -, hG⟩, ⟨C, -, hC⟩⟩ x hx
      have h1 : x s.q = 0 := (hG hx).2
      have h2 := (hC hx).2
      linarith
    · intro h
      have hzero : ∀ x ∈ F, x s.q = 0 := fun x hx => by
        linarith [(hfib x hx).2.1, (hfib x hx).2.2, h x hx]
      have hg : ∀ x ∈ F, x s.q = s.U (fun p : s.P' => x p.1) - s.L (fun p : s.P' => x p.1) := fun x hx => by
        linarith [(hfib x hx).2.1, (hfib x hx).2.2, h x hx]
      exact ⟨⟨projL s '' F, after_face s hF.1 hl hzero, fun x hx => ⟨⟨x, hx, rfl⟩, hzero x hx⟩⟩,
        cellR_of_graph s hFconv hF.1 hFB hg⟩

end Faces

end HibiLi.Proofs.Informal

end
