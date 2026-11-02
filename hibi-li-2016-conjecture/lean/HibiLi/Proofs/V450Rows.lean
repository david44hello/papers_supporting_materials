/-
HibiLi/Proofs/V450Rows.lean — faces with no vertical segment are graphs over cells, the faces of both kinds, L = U on a face of B, and L, U on E₀ with E₀ a copy of the base of the switch of c in X (paper v4.60 l. 380-384, 395, 622).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Informal
import HibiLi.Polytope.Transitivity
import HibiLi.Polytope.AffinityComplex
import HibiLi.Polytope.IntersectionFaces
import HibiLi.Polytope.CarrierInterior
import HibiLi.Polytope.TopCells
import HibiLi.Polytope.FiniteFaces
import HibiLi.Proofs.Lemma44
import HibiLi.Example21.CenterSwitch

noncomputable section

namespace HibiLi.Proofs.V450

open HibiLi HibiLi.Proofs.Vertical

namespace Rows

section Graph

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The graph `{x : x|_{P'} ∈ C, x_q = f(x|_{P'})}` of `f` over `C`. -/
def graph (f : (s.P' → ℝ) → ℝ) (C : Set (s.P' → ℝ)) : Set (P → ℝ) :=
  {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = f (fun p => x p.1)}

theorem mem_graph {f : (s.P' → ℝ) → ℝ} {C : Set (s.P' → ℝ)} {x : P → ℝ} :
    x ∈ graph s f C ↔ proj s x ∈ C ∧ x s.q = f (proj s x) := Iff.rfl

theorem mk_mem_graph {f : (s.P' → ℝ) → ℝ} {C : Set (s.P' → ℝ)} {u : s.P' → ℝ} (hu : u ∈ C) :
    mk s u (f u) ∈ graph s f C := by
  rw [mem_graph, proj_mk, mk_q]
  exact ⟨hu, rfl⟩

theorem proj_image_graph (f : (s.P' → ℝ) → ℝ) (C : Set (s.P' → ℝ)) : proj s '' graph s f C = C := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro hu
    exact ⟨_, mk_mem_graph s hu, proj_mk s u (f u)⟩

theorem eq_of_graph_eq {f f' : (s.P' → ℝ) → ℝ} {C C' : Set (s.P' → ℝ)} (h : graph s f C = graph s f' C') :
    C = C' := by
  rw [← proj_image_graph s f C, h, proj_image_graph]

theorem graph_mono {f : (s.P' → ℝ) → ℝ} {C D : Set (s.P' → ℝ)} (h : C ⊆ D) : graph s f C ⊆ graph s f D :=
  fun _ hx => ⟨h hx.1, hx.2⟩

theorem eq_of_proj_eq {x y : P → ℝ} (hp : proj s x = proj s y) (hq : x s.q = y s.q) : x = y := by
  rw [← mk_proj s x, ← mk_proj s y, hp, hq]

/-- A set inside the graph of `f` is the graph of `f` over its projection. -/
theorem eq_graph_proj {F : Set (P → ℝ)} {f : (s.P' → ℝ) → ℝ} {D : Set (s.P' → ℝ)} (hF : F ⊆ graph s f D) :
    F = graph s f (proj s '' F) := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, (hF hx).2⟩
  · rintro ⟨⟨y, hy, hxy⟩, hq⟩
    have hyx : y = x := by
      refine eq_of_proj_eq s hxy ?_
      rw [(hF hy).2, hq]
      exact congrArg f hxy
    exact hyx ▸ hy

/-- If `f` agrees on `D` with an affine function, a face `F` of a set `Q` with `F ⊆ graph f D ⊆ Q` projects onto a face
of `D`. -/
theorem isFace_proj {Q F : Set (P → ℝ)} (hF : IsFace Q F) {D : Set (s.P' → ℝ)} {f : (s.P' → ℝ) → ℝ}
    (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ) (hfg : ∀ u ∈ D, f u = g u) (hFG : F ⊆ graph s f D) (hGQ : graph s f D ⊆ Q) :
    IsFace D (proj s '' F) := by
  obtain ⟨l, hl⟩ := hF.2 hF.1
  let a : StrongDual ℝ (s.P' → ℝ) :=
    l.comp (lift s) + l (ez s) • LinearMap.toContinuousLinearMap g.linear
  have hg : ∀ u, g u = g.linear u + g 0 := fun u => congrFun (AffineMap.decomp g) u
  have hval : ∀ u ∈ D, l (mk s u (f u)) = a u + g 0 * l (ez s) := by
    intro u hu
    rw [hfg u hu, hg u]
    simp only [mk, map_add, map_smul, smul_eq_mul, a, add_apply,
      ContinuousLinearMap.comp_apply, smul_apply, LinearMap.coe_toContinuousLinearMap']
    ring
  have hpt : ∀ x ∈ F, mk s (proj s x) (f (proj s x)) = x := by
    intro x hx
    have h2 : x s.q = f (proj s x) := (hFG hx).2
    rw [← h2, mk_proj]
  have hlx : ∀ x ∈ F, l x = a (proj s x) + g 0 * l (ez s) := fun x hx => by
    rw [← hval (proj s x) (hFG hx).1, hpt x hx]
  have hmax : ∀ x ∈ F, ∀ y ∈ Q, l y ≤ l x := fun x hx => by
    rw [hl] at hx
    exact hx.2
  obtain ⟨x0, hx0⟩ := hF.1
  refine ⟨⟨_, x0, hx0, rfl⟩, fun _ => ⟨a, ?_⟩⟩
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(hFG hx).1, fun v hv => ?_⟩
    have h1 := hmax x hx _ (hGQ (mk_mem_graph s hv))
    rw [hval v hv, hlx x hx] at h1
    linarith
  · rintro ⟨hu, hmaxu⟩
    refine ⟨mk s u (f u), ?_, proj_mk s u (f u)⟩
    rw [hl]
    refine ⟨hGQ (mk_mem_graph s hu), fun y hy => ?_⟩
    have h1 := hmax x0 hx0 y hy
    rw [hlx x0 hx0] at h1
    rw [hval u hu]
    linarith [hmaxu (proj s x0) (hFG hx0).1]

/-- A graph over a subset of the base, between the two bounds, lies in the prism. -/
theorem graph_subset_prism {lo hi f : (s.P' → ℝ) → ℝ} {C base : Set (s.P' → ℝ)} (hC : C ⊆ base)
    (hlo : ∀ u ∈ base, lo u ≤ f u) (hhi : ∀ u ∈ base, f u ≤ hi u) : graph s f C ⊆ prism s lo hi base := by
  intro x hx
  have hq : x s.q = f (proj s x) := hx.2
  exact ⟨hC hx.1, (hlo _ (hC hx.1)).trans_eq hq.symm, hq.le.trans (hhi _ (hC hx.1))⟩

/-- Where the two bounds agree, the prism is the graph. -/
theorem graph_eq_prism {lo hi : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} (h : ∀ u ∈ G, lo u = hi u) :
    graph s lo G = prism s lo hi G := by
  ext x
  constructor
  · rintro ⟨hG, hq⟩
    exact ⟨hG, hq.ge, hq.le.trans_eq (h _ hG)⟩
  · rintro ⟨hG, h1, h2⟩
    exact ⟨hG, le_antisymm (h2.trans_eq (h _ hG).symm) h1⟩

theorem before_eq_prism : chainOrderPolytope P s.I = prism s s.L s.U s.B :=
  Set.ext fun x => (prop_3_1_proved s x).1

theorem after_eq_prism :
    chainOrderPolytope P (insert s.q s.I) = prism s (fun _ => 0) (fun u => s.U u - s.L u) s.B :=
  Set.ext fun x => (prop_3_1_proved s x).2

/-- The chain sum `ℓ_K` as a linear map. -/
def chainLin (K : Finset s.P') : (s.P' → ℝ) →ₗ[ℝ] ℝ := ∑ p ∈ K, LinearMap.proj p

theorem chainLin_apply (K : Finset s.P') (u : s.P' → ℝ) : chainLin s K u = s.chainSum K u := by
  simp [chainLin, Switch.chainSum, LinearMap.sum_apply]

/-- The branch `j` of `U` as an affine map. -/
def upAff : Option s.P' → (s.P' → ℝ) →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ (s.P' → ℝ) (1 : ℝ)
  | some r => (LinearMap.proj r : (s.P' → ℝ) →ₗ[ℝ] ℝ).toAffineMap

theorem upAff_apply (j : Option s.P') (u : s.P' → ℝ) : upAff s j u = s.upVal j u := by
  cases j <;> rfl

theorem L_eq_on_domL {C : Set (s.P' → ℝ)} {K : Finset s.P'} (hCK : C ⊆ s.domL K) :
    ∀ u ∈ C, s.L u = (chainLin s K).toAffineMap u := fun u hu => by
  rw [LinearMap.coe_toAffineMap, chainLin_apply]
  exact (hCK hu).2

theorem U_eq_on_domU {C : Set (s.P' → ℝ)} {j : Option s.P'} (hCj : C ⊆ s.domU j) :
    ∀ u ∈ C, s.U u = upAff s j u := fun u hu => by
  rw [upAff_apply]
  exact (hCj hu).2

end Graph

section Concave

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A function that is nonnegative and concave along a convex set `G`, and zero at a relative interior point of `G`, is
zero on `G`. -/
theorem eq_zero_of_relint_concave {G : Set V} {u0 : V} (hu0 : u0 ∈ intrinsicInterior ℝ G) {h : V → ℝ}
    (hnn : ∀ v ∈ G, 0 ≤ h v) (h0 : h u0 = 0)
    (hconc : ∀ w ∈ G, ∀ v ∈ G, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → a * h w + b * h v ≤ h (a • w + b • v)) :
    ∀ v ∈ G, h v = 0 := by
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
  have key := hconc _ hw v hv (1 / (1 + r)) (r / (1 + r)) (by positivity) hb.le (by field_simp)
  rw [hcomb, h0] at key
  have hw0 := hnn _ hw
  have hv0 := hnn v hv
  have hmul : r / (1 + r) * h v = 0 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / (1 + r) by positivity) hw0, mul_nonneg hb.le hv0]
  exact (mul_eq_zero.1 hmul).resolve_left hb.ne'

/-- An affine map does not raise the affine dimension. -/
theorem adim_image_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ V]
    (φ : V →ᵃ[ℝ] W) (S : Set V) : adim (φ '' S) ≤ adim S := by
  unfold adim
  rw [← AffineMap.map_vectorSpan]
  exact Submodule.finrank_map_le _ _

end Concave

section Both

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

theorem graph_congr {f f' : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} (h : ∀ u ∈ G, f u = f' u) :
    graph s f G = graph s f' G := by
  ext x
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans (h _ h1)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans (h _ h1).symm⟩

/-- `L = U` on a convex `G ⊆ B` once `L = U` at one relative interior point (`U − L` is concave and nonnegative). -/
theorem L_eq_U_of_relint {G : Set (s.P' → ℝ)} (hGB : G ⊆ s.B) {u : s.P' → ℝ} (hu : u ∈ intrinsicInterior ℝ G)
    (hLU : s.L u = s.U u) : ∀ v ∈ G, s.L v = s.U v := by
  have hz := eq_zero_of_relint_concave hu (h := fun v => s.U v - s.L v)
    (fun v hv => sub_nonneg.2 (L_U_bounds s (hGB hv)).2.1) (by simp [hLU])
    (fun w _ v _ a b ha hb hab => by
      have h2 := (U_concave s).2 (Set.mem_univ w) (Set.mem_univ v) ha hb hab
      have h3 := (L_convex s).2 (Set.mem_univ w) (Set.mem_univ v) ha hb hab
      simp only [smul_eq_mul] at h2 h3
      show a * (s.U w - s.L w) + b * (s.U v - s.L v) ≤ s.U (a • w + b • v) - s.L (a • w + b • v)
      linarith)
  intro v hv
  have h1 : s.U v - s.L v = 0 := hz v hv
  linarith

/-- Where `L = U` on a convex set, both are affine along it. -/
theorem affAlong_of_eq {G : Set (s.P' → ℝ)} (hconv : Convex ℝ G) (hLU : ∀ v ∈ G, s.L v = s.U v) :
    Informal.AffAlong G s.L ∧ Informal.AffAlong G s.U := by
  have key : ∀ w ∈ G, ∀ v ∈ G, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      s.L (a • w + b • v) = a * s.L w + b * s.L v ∧ s.U (a • w + b • v) = a * s.U w + b * s.U v := by
    intro w hw v hv a b ha hb hab
    have h2 := (U_concave s).2 (Set.mem_univ w) (Set.mem_univ v) ha hb hab
    have h3 := (L_convex s).2 (Set.mem_univ w) (Set.mem_univ v) ha hb hab
    simp only [smul_eq_mul] at h2 h3
    have hm := hLU _ (hconv hw hv ha hb hab)
    rw [hLU w hw, hLU v hv] at h3
    refine ⟨?_, by linarith⟩
    rw [hLU w hw, hLU v hv]
    linarith
  exact ⟨fun w hw v hv a b ha hb hab => (key w hw v hv a b ha hb hab).1,
    fun w hw v hv a b ha hb hab => (key w hw v hv a b ha hb hab).2⟩

/-- A face `G` of `B` with `L = U` on it lies in one full-dimensional affinity domain of `L`, and is a cell of `S` and
of `T`. -/
theorem face_mem_cells {G : Set (s.P' → ℝ)} (hG : IsFace s.B G) (hLU : ∀ v ∈ G, s.L v = s.U v) :
    (∃ K, G ⊆ s.domL K) ∧ G ∈ s.cellsS ∧ G ∈ s.cellsT := by
  have hconv : Convex ℝ G := hG.2.convex s.B_isPolytope.convex
  obtain ⟨hAL, hAU⟩ := affAlong_of_eq s hconv hLU
  obtain ⟨K, hK, hKfull, hKsub⟩ := Informal.domL_of_affAlong s hconv hG.1 hG.subset hAL
  obtain ⟨j, hj, hjfull, hjsub⟩ := Informal.domU_of_affAlong s hconv hG.1 hG.subset hAU
  obtain ⟨u, hu⟩ := hG.1
  refine ⟨⟨K, hKsub⟩, ⟨K, hK, hKfull, ?_⟩, ⟨j, hj, hjfull, ?_⟩⟩
  · have h := hG.inter_subset (fun _ hv => hv.1 : s.domL K ⊆ s.B) ⟨u, hKsub hu, hu⟩
    rwa [Set.inter_eq_right.mpr hKsub] at h
  · have h := hG.inter_subset (fun _ hv => hv.1 : s.domU j ⊆ s.B) ⟨u, hjsub hu, hu⟩
    rwa [Set.inter_eq_right.mpr hjsub] at h

/-- The graph map `u ↦ (u, g u)` of an affine function. -/
def graphMap (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ) : (s.P' → ℝ) →ᵃ[ℝ] (P → ℝ) where
  toFun u := mk s u (g u)
  linear := (lift s).toLinearMap + g.linear.smulRight (ez s)
  map_vadd' u v := by
    simp only [vadd_eq_add, mk, map_add, LinearMap.add_apply, LinearMap.smulRight_apply,
      ContinuousLinearMap.coe_coe]
    rw [show g (v + u) = g.linear v + g u from g.map_vadd u v, add_smul]
    abel

theorem graph_eq_image {f : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ)
    (hfg : ∀ u ∈ G, f u = g u) : graph s f G = graphMap s g '' G := by
  ext x
  constructor
  · intro hx
    refine ⟨proj s x, hx.1, ?_⟩
    have hq : x s.q = f (proj s x) := hx.2
    show mk s (proj s x) (g (proj s x)) = x
    rw [← hfg (proj s x) hx.1, ← hq, mk_proj]
  · rintro ⟨u, hu, rfl⟩
    show mk s u (g u) ∈ graph s f G
    rw [← hfg u hu]
    exact mk_mem_graph s hu

/-- The graph of a function that is affine on `G` has the dimension of `G`. -/
theorem adim_graph {f : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} (g : (s.P' → ℝ) →ᵃ[ℝ] ℝ)
    (hfg : ∀ u ∈ G, f u = g u) : adim (graph s f G) = adim G := by
  apply le_antisymm
  · rw [graph_eq_image s g hfg]
    exact adim_image_le _ _
  · have h := adim_image_le ((proj s).toLinearMap.toAffineMap) (graph s f G)
    have himg : ((proj s).toLinearMap.toAffineMap : (P → ℝ) → (s.P' → ℝ)) '' graph s f G = G :=
      proj_image_graph s f G
    rwa [himg] at h

theorem graph_L_isFace {G : Set (s.P' → ℝ)} (hG : IsFace s.B G) (hLU : ∀ v ∈ G, s.L v = s.U v) :
    IsFace (chainOrderPolytope P s.I) (graph s s.L G) := by
  rw [before_eq_prism, graph_eq_prism s hLU]
  exact face_prism s (fun u hu => (L_U_bounds s hu).2.1) hG

theorem graph_zero_isFace {G : Set (s.P' → ℝ)} (hG : IsFace s.B G) (hLU : ∀ v ∈ G, s.L v = s.U v) :
    IsFace (chainOrderPolytope P (insert s.q s.I)) (graph s (fun _ => 0) G) := by
  rw [after_eq_prism, graph_eq_prism s (hi := fun u => s.U u - s.L u) (fun u hu => by simp [hLU u hu])]
  exact face_prism s (fun u hu => sub_nonneg.2 (L_U_bounds s hu).2.1) hG

theorem face_mem_cellsR {G : Set (s.P' → ℝ)} (hG : IsFace s.B G) (hLU : ∀ v ∈ G, s.L v = s.U v) :
    G ∈ s.cellsR := by
  obtain ⟨-, hS, hT⟩ := face_mem_cells s hG hLU
  exact ⟨hG.1, G, hS, G, hT, (Set.inter_self G).symm⟩

/-- Before the switch: the faces that are graphs of both kinds are the graphs of `L` over the faces of `B` where
`L = U`. -/
theorem both_before (F : Set (P → ℝ)) :
    (IsFace (chainOrderPolytope P s.I) F ∧
        (∃ C ∈ s.cellsS, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
        (∃ C ∈ s.cellsT, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})) ↔
      ∃ G, IsFace s.B G ∧ (∀ u ∈ G, s.L u = s.U u) ∧
        F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = s.L (fun p => x p.1)} := by
  constructor
  · rintro ⟨hF, ⟨C, hC, e1⟩, ⟨C', -, e2⟩⟩
    have e1' : F = graph s s.L C := e1
    have e2' : F = graph s s.U C' := e2
    have hCC : C = C' := eq_of_graph_eq s (e1'.symm.trans e2')
    subst hCC
    have hLU : ∀ u ∈ C, s.L u = s.U u := by
      intro u hu
      have hm : mk s u (s.L u) ∈ graph s s.U C := by
        rw [← e2', e1']
        exact mk_mem_graph s hu
      rw [mem_graph, proj_mk, mk_q] at hm
      exact hm.2
    obtain ⟨K, hK, -, hCK⟩ := hC
    have hCB : C ⊆ s.B := hCK.subset.trans fun _ hv => hv.1
    have hCne : C.Nonempty := hCK.1
    have hCconv : Convex ℝ C := hCK.2.convex (s.domL_isPolytope K hK).convex
    obtain ⟨G, hGcar, -⟩ := s.B_isPolytope.existsUnique_carrier hCne hCB
    obtain ⟨u0, hu0⟩ := hCne.intrinsicInterior hCconv
    have hu0G := hGcar.intrinsicInterior_subset (chainOrderPolytope_halfspaces _ _) hu0
    have hLUG := L_eq_U_of_relint s hGcar.1.subset hu0G (hLU u0 (intrinsicInterior_subset hu0))
    obtain ⟨⟨K', hGK'⟩, -, -⟩ := face_mem_cells s hGcar.1 hLUG
    have hGQ : graph s s.L G ⊆ chainOrderPolytope P s.I := by
      rw [before_eq_prism]
      exact graph_subset_prism s hGcar.1.subset (fun _ _ => le_rfl) (fun u hu => (L_U_bounds s hu).2.1)
    have hFG : F ⊆ graph s s.L G := e1' ▸ graph_mono s hGcar.2.1
    have hface := isFace_proj s hF (f := s.L) _ (L_eq_on_domL s hGK') hFG hGQ
    rw [e1', proj_image_graph] at hface
    exact ⟨C, IsFace.trans s.B_isPolytope hGcar.1 hface, hLU, e1⟩
  · rintro ⟨G, hG, hLU, e⟩
    have e' : F = graph s s.L G := e
    obtain ⟨-, hS, hT⟩ := face_mem_cells s hG hLU
    refine ⟨e' ▸ graph_L_isFace s hG hLU, ⟨G, hS, e⟩, ⟨G, hT, ?_⟩⟩
    show F = graph s s.U G
    rw [e', graph_congr s hLU]

/-- After the switch: the faces that are of both kinds are the parts of `{z = 0}` over the faces of `B` where
`L = U`. -/
theorem both_after (F : Set (P → ℝ)) :
    (IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧
        (∃ G, IsFace s.B G ∧ F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
        (∃ C ∈ s.cellsR, F = {x | (fun p : s.P' => x p.1) ∈ C ∧
          x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})) ↔
      ∃ G, IsFace s.B G ∧ (∀ u ∈ G, s.L u = s.U u) ∧
        F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0} := by
  constructor
  · rintro ⟨-, ⟨G, hG, e1⟩, ⟨C, -, e2⟩⟩
    have e1' : F = graph s (fun _ => 0) G := e1
    have e2' : F = graph s (fun u => s.U u - s.L u) C := e2
    have hGC : G = C := eq_of_graph_eq s (e1'.symm.trans e2')
    subst hGC
    refine ⟨G, hG, fun u hu => ?_, e1⟩
    have hm : mk s u 0 ∈ graph s (fun u => s.U u - s.L u) G := by
      rw [← e2', e1']
      exact mk_mem_graph s (f := fun _ => 0) hu
    rw [mem_graph, proj_mk, mk_q] at hm
    linarith [hm.2]
  · rintro ⟨G, hG, hLU, e⟩
    have e' : F = graph s (fun _ => 0) G := e
    refine ⟨e' ▸ graph_zero_isFace s hG hLU, ⟨G, hG, e⟩, ⟨G, face_mem_cellsR s hG hLU, ?_⟩⟩
    show F = graph s (fun u => s.U u - s.L u) G
    rw [e', graph_congr s (fun u hu => by simp [hLU u hu] : ∀ u ∈ G, (fun _ => (0 : ℝ)) u = s.U u - s.L u)]

/-- The faces of `B` where `L = U`, of dimension `k`. -/
def eqFaces (k : ℕ) : Set (Set (s.P' → ℝ)) := {G | IsFace s.B G ∧ (∀ u ∈ G, s.L u = s.U u) ∧ adim G = k}

theorem adim_graph_L {G : Set (s.P' → ℝ)} (hG : IsFace s.B G) (hLU : ∀ v ∈ G, s.L v = s.U v) :
    adim (graph s s.L G) = adim G := by
  obtain ⟨⟨K, hGK⟩, -, -⟩ := face_mem_cells s hG hLU
  exact adim_graph s _ (L_eq_on_domL s hGK)

theorem adim_graph_zero (G : Set (s.P' → ℝ)) : adim (graph s (fun _ => 0) G) = adim G :=
  adim_graph s (AffineMap.const ℝ _ (0 : ℝ)) (fun _ _ => rfl)

theorem both_before_eq_image (k : ℕ) :
    {F : Set (P → ℝ) | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧
        (∃ C ∈ s.cellsS, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
        (∃ C ∈ s.cellsT, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})} =
      graph s s.L '' eqFaces s k := by
  ext F
  constructor
  · rintro ⟨hF, hk, hS, hT⟩
    obtain ⟨G, hG, hLU, e⟩ := (both_before s F).1 ⟨hF, hS, hT⟩
    have e' : F = graph s s.L G := e
    subst e'
    exact ⟨G, ⟨hG, hLU, (adim_graph_L s hG hLU).symm.trans hk⟩, rfl⟩
  · rintro ⟨G, ⟨hG, hLU, hk⟩, rfl⟩
    obtain ⟨hF, hS, hT⟩ := (both_before s (graph s s.L G)).2 ⟨G, hG, hLU, rfl⟩
    exact ⟨hF, (adim_graph_L s hG hLU).trans hk, hS, hT⟩

theorem both_after_eq_image (k : ℕ) :
    {F : Set (P → ℝ) | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧
        (∃ G, IsFace s.B G ∧ F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
        (∃ C ∈ s.cellsR, F = {x | (fun p : s.P' => x p.1) ∈ C ∧
          x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})} =
      graph s (fun _ => 0) '' eqFaces s k := by
  ext F
  constructor
  · rintro ⟨hF, hk, hZ, hR⟩
    obtain ⟨G, hG, hLU, e⟩ := (both_after s F).1 ⟨hF, hZ, hR⟩
    have e' : F = graph s (fun _ => 0) G := e
    subst e'
    exact ⟨G, ⟨hG, hLU, (adim_graph_zero s G).symm.trans hk⟩, rfl⟩
  · rintro ⟨G, ⟨hG, hLU, hk⟩, rfl⟩
    obtain ⟨hF, hZ, hR⟩ := (both_after s (graph s (fun _ => 0) G)).2 ⟨G, hG, hLU, rfl⟩
    exact ⟨hF, (adim_graph_zero s G).trans hk, hZ, hR⟩

end Both

section E0

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

theorem pa_mem_I : x.pa.1 ∈ x.toSwitch.I := by
  show ¬ x.q ≤ x.a
  exact fun h => lt_irrefl _ (lt_of_le_of_lt h x.a_lt_q)

theorem pb_mem_I : x.pb.1 ∈ x.toSwitch.I := by
  show ¬ x.q ≤ x.b
  exact fun h => lt_irrefl _ (lt_of_le_of_lt h x.b_lt_q)

theorem not_mem_I_of_lt {r : x.toSwitch.P'} (hr : x.q < r.1) : r.1 ∉ x.toSwitch.I := by
  show ¬ ¬ x.q ≤ r.1
  exact fun h => h hr.le

theorem pg_not_mem_I : x.pg.1 ∉ x.toSwitch.I := not_mem_I_of_lt x x.q_covby_g'.lt

theorem ph_not_mem_I : x.ph.1 ∉ x.toSwitch.I := not_mem_I_of_lt x x.q_covby_h'.lt

theorem chainSum_le_max {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) {K : Finset x.toSwitch.P'}
    (hK : K ∈ x.toSwitch.lowBranches) : x.toSwitch.chainSum K u ≤ max (u x.pa) (u x.pb) := by
  obtain ⟨hB, hchain, -⟩ := hu
  obtain ⟨hKI, hKc, -⟩ := (mem_lowBranches x.toSwitch).1 hK
  have ha0 : 0 ≤ u x.pa := hB.1 x.pa (pa_mem_I x)
  have hzero : ∀ p ∈ K, p ≠ x.pa → p ≠ x.pb → u p = 0 := fun p hp h1 h2 =>
    hchain p (hKI p hp) (fun e => h1 (Subtype.ext e)) (fun e => h2 (Subtype.ext e))
  unfold Switch.chainSum
  by_cases ha : x.pa ∈ K
  · have hb : x.pb ∉ K := by
      intro hb
      have hne : x.pa ≠ x.pb := fun e => x.isX.2.2.2.2.1 (le_of_eq (congrArg Subtype.val e))
      rcases hKc (Finset.mem_coe.2 ha) (Finset.mem_coe.2 hb) hne with h | h
      · exact x.isX.2.2.2.2.1 h
      · exact x.isX.2.2.2.2.2.1 h
    rw [Finset.sum_eq_single_of_mem x.pa ha (fun p hp hne => hzero p hp hne (fun e => hb (e ▸ hp)))]
    exact le_max_left _ _
  · by_cases hb : x.pb ∈ K
    · rw [Finset.sum_eq_single_of_mem x.pb hb (fun p hp hne => hzero p hp (fun e => ha (e ▸ hp)) hne)]
      exact le_max_right _ _
    · rw [Finset.sum_eq_zero (fun p hp => hzero p hp (fun e => ha (e ▸ hp)) (fun e => hb (e ▸ hp)))]
      exact le_max_of_le_left ha0

theorem L_on_E0 {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) : x.toSwitch.L u = max (u x.pa) (u x.pb) := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun K hK => chainSum_le_max x hu hK
  · apply max_le
    · calc u x.pa = x.toSwitch.chainSum {x.pa} u := by simp [Switch.chainSum]
        _ ≤ x.toSwitch.L u := Finset.le_sup' (fun K => x.toSwitch.chainSum K u) x.singleton_pa_mem
    · calc u x.pb = x.toSwitch.chainSum {x.pb} u := by simp [Switch.chainSum]
        _ ≤ x.toSwitch.L u := Finset.le_sup' (fun K => x.toSwitch.chainSum K u) x.singleton_pb_mem

theorem U_on_E0 {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) : x.toSwitch.U u = min (u x.pg) (u x.ph) := by
  obtain ⟨hB, -, horder⟩ := hu
  have hg1 : u x.pg ≤ 1 := (hB.2.1 x.pg (pg_not_mem_I x)).2
  apply le_antisymm
  · apply le_min
    · exact Finset.inf'_le (fun j => x.toSwitch.upVal j u)
        (some_mem_upBranches x.toSwitch (r := x.pg) x.q_covby_g'.lt)
    · exact Finset.inf'_le (fun j => x.toSwitch.upVal j u)
        (some_mem_upBranches x.toSwitch (r := x.ph) x.q_covby_h'.lt)
  · apply Finset.le_inf'
    intro j hj
    rcases mem_upBranches x.toSwitch hj with rfl | ⟨r, hr, rfl⟩
    · show min (u x.pg) (u x.ph) ≤ 1
      exact (min_le_left _ _).trans hg1
    · show min (u x.pg) (u x.ph) ≤ u r
      by_cases e1 : r = x.pg
      · subst e1
        exact min_le_left _ _
      by_cases e2 : r = x.ph
      · subst e2
        exact min_le_right _ _
      rw [horder r (not_mem_I_of_lt x hr) (fun e => e1 (Subtype.ext e)) (fun e => e2 (Subtype.ext e))]
      exact (min_le_left _ _).trans hg1

end E0

section Copy

open Classical

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

theorem pa_ne_pb : x.pa ≠ x.pb := fun e => x.isX.2.2.2.2.1 (le_of_eq (congrArg Subtype.val e))

theorem pg_ne_ph : x.pg ≠ x.ph := fun e => x.g'_ne_h' (congrArg Subtype.val e)

theorem ne_of_mem_I {p r : x.toSwitch.P'} (hp : p.1 ∈ x.toSwitch.I) (hr : r.1 ∉ x.toSwitch.I) : p ≠ r :=
  fun e => hr (by rw [← e]; exact hp)

/-- On `E₀`, a coordinate other than `α, β, γ, η` is `0` (chain) or `1` (order). -/
theorem E0_other {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) (p : x.toSwitch.P') (h1 : p ≠ x.pa) (h2 : p ≠ x.pb)
    (h3 : p ≠ x.pg) (h4 : p ≠ x.ph) : u p = if p.1 ∈ x.toSwitch.I then 0 else 1 := by
  obtain ⟨-, hchain, horder⟩ := hu
  split_ifs with hp
  · exact hchain p hp (fun e => h1 (Subtype.ext e)) (fun e => h2 (Subtype.ext e))
  · exact horder p hp (fun e => h3 (Subtype.ext e)) (fun e => h4 (Subtype.ext e))

theorem E0_injOn : Set.InjOn x.alphaPart x.E0 := by
  intro u hu v hv huv
  have h0 : u x.pa = v x.pa := by simpa [XSwitch.alphaPart] using congrFun huv 0
  have h1 : u x.pb = v x.pb := by simpa [XSwitch.alphaPart] using congrFun huv 1
  have h2 : u x.pg = v x.pg := by simpa [XSwitch.alphaPart] using congrFun huv 2
  have h3 : u x.ph = v x.ph := by simpa [XSwitch.alphaPart] using congrFun huv 3
  funext p
  by_cases e1 : p = x.pa
  · rw [e1]
    exact h0
  by_cases e2 : p = x.pb
  · rw [e2]
    exact h1
  by_cases e3 : p = x.pg
  · rw [e3]
    exact h2
  by_cases e4 : p = x.ph
  · rw [e4]
    exact h3
  rw [E0_other x hu p e1 e2 e3 e4, E0_other x hv p e1 e2 e3 e4]

/-- The common image: `0 ≤ α, β`, `max(α, β) ≤ min(γ, η)`, `γ, η ≤ 1`. -/
def S4 : Set (Fin 4 → ℝ) := {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ max (v 0) (v 1) ≤ min (v 2) (v 3) ∧ v 2 ≤ 1 ∧ v 3 ≤ 1}

theorem E0_image : x.alphaPart '' x.E0 = S4 := by
  obtain ⟨-, -, hE⟩ := lemma_4_4_proved x x.pa x.pb x.pg x.ph rfl rfl rfl rfl
  have hpg := pg_not_mem_I x
  have hph := ph_not_mem_I x
  have hpa := pa_mem_I x
  have hpb := pb_mem_I x
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hE, Set.mem_ofPred_eq] at hu
    obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := hu
    show 0 ≤ u x.pa ∧ 0 ≤ u x.pb ∧ max (u x.pa) (u x.pb) ≤ min (u x.pg) (u x.ph) ∧ u x.pg ≤ 1 ∧ u x.ph ≤ 1
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨hv0, hv1, hvm, hv2, hv3⟩
    let u : x.toSwitch.P' → ℝ := fun p => if p = x.pa then v 0 else if p = x.pb then v 1 else
      if p = x.pg then v 2 else if p = x.ph then v 3 else if p.1 ∈ x.toSwitch.I then 0 else 1
    have ua : u x.pa = v 0 := by simp [u]
    have ub : u x.pb = v 1 := by simp [u, (pa_ne_pb x).symm]
    have ug : u x.pg = v 2 := by
      simp [u, (ne_of_mem_I x hpa hpg).symm, (ne_of_mem_I x hpb hpg).symm]
    have uh : u x.ph = v 3 := by
      simp [u, (ne_of_mem_I x hpa hph).symm, (ne_of_mem_I x hpb hph).symm, (pg_ne_ph x).symm]
    have uo : ∀ p, p ≠ x.pa → p ≠ x.pb → p ≠ x.pg → p ≠ x.ph →
        u p = if p.1 ∈ x.toSwitch.I then 0 else 1 := by
      intro p h1 h2 h3 h4
      simp [u, h1, h2, h3, h4]
    refine ⟨u, ?_, ?_⟩
    · rw [hE, Set.mem_ofPred_eq]
      refine ⟨fun p hp ha hb => ?_, fun r hr hg hh => ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [uo p (fun e => ha (congrArg Subtype.val e)) (fun e => hb (congrArg Subtype.val e))
          (ne_of_mem_I x hp hpg) (ne_of_mem_I x hp hph), ite_eq_left hp]
      · rw [uo r (ne_of_mem_I x hpa hr).symm (ne_of_mem_I x hpb hr).symm
          (fun e => hg (congrArg Subtype.val e)) (fun e => hh (congrArg Subtype.val e)), ite_eq_right hr]
      · rw [ua]
        exact hv0
      · rw [ub]
        exact hv1
      · rw [ua, ub, ug, uh]
        exact hvm
      · rw [ug]
        exact hv2
      · rw [uh]
        exact hv3
    · funext i
      fin_cases i <;> simp [XSwitch.alphaPart, ua, ub, ug, uh]

end Copy

end Rows

open Rows

/-- **v4.60 l. 380-382** (informal reading, sentence 1): a face of `O_I(P)` that contains no segment parallel to the
`z`-axis IS the graph of `L` over a cell of `S`, or the graph of `U` over a cell of `T` (or both). -/
theorem informal_before_graph_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (F : Set (P → ℝ))
    (hF : IsFace (chainOrderPolytope P s.I) F) (hv : ¬ HasVertical s F) :
    (∃ C ∈ s.cellsS, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∨
    (∃ C ∈ s.cellsT, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)}) := by
  have hFQ : F ⊆ chainOrderPolytope P s.I := hF.subset
  have hFconv : Convex ℝ F := hF.2.convex (chainOrderPolytope_isPolytope P s.I).convex
  have hFB : ∀ x ∈ F, (fun p : s.P' => x p.1) ∈ s.B := fun x hx => ((prop_3_1_proved s x).1.1 (hFQ hx)).1
  rcases Informal.before_graph s hF hv with hL | hU
  · left
    obtain ⟨C, ⟨K, hK, hfull, hCK⟩, hsub⟩ := Informal.cellS_of_graph s hFconv hF.1 hFB hL
    have hCB : C ⊆ s.B := hCK.subset.trans fun _ hu => hu.1
    have hGQ : graph s s.L C ⊆ chainOrderPolytope P s.I := by
      rw [before_eq_prism]
      exact graph_subset_prism s hCB (fun _ _ => le_rfl) (fun u hu => (L_U_bounds s hu).2.1)
    have hface := isFace_proj s hF (f := s.L) _ (L_eq_on_domL s hCK.subset) hsub hGQ
    exact ⟨proj s '' F, s.cellsS_face_closed ⟨K, hK, hfull, hCK⟩ hface, eq_graph_proj s hsub⟩
  · right
    obtain ⟨C, ⟨j, hj, hfull, hCj⟩, hsub⟩ := Informal.cellT_of_graph s hFconv hF.1 hFB hU
    have hCB : C ⊆ s.B := hCj.subset.trans fun _ hu => hu.1
    have hGQ : graph s s.U C ⊆ chainOrderPolytope P s.I := by
      rw [before_eq_prism]
      exact graph_subset_prism s hCB (fun u hu => (L_U_bounds s hu).2.1) (fun _ _ => le_rfl)
    have hface := isFace_proj s hF (f := s.U) _ (U_eq_on_domU s hCj.subset) hsub hGQ
    exact ⟨proj s '' F, s.cellsT_face_closed ⟨j, hj, hfull, hCj⟩ hface, eq_graph_proj s hsub⟩

/-- **v4.60 l. 382-383** (informal reading, sentence 2): after the switch, a face of `O_{I∪{q}}(P)` that contains no
segment parallel to the `z`-axis IS the part of the facet `{z = 0}` over a face of `B`, or the graph of `U − L` over a
cell of `R` (or both). -/
theorem informal_after_graph_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (F : Set (P → ℝ))
    (hF : IsFace (chainOrderPolytope P (insert s.q s.I)) F) (hv : ¬ HasVertical s F) :
    (∃ G, IsFace s.B G ∧ F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∨
    (∃ C ∈ s.cellsR, F = {x | (fun p : s.P' => x p.1) ∈ C ∧
        x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)}) := by
  rcases (Informal.informal_after s F hF hv).1 with ⟨G, hG, hsub⟩ | ⟨C, hC, hsub⟩
  · left
    have hGQ : graph s (fun _ => 0) G ⊆ chainOrderPolytope P (insert s.q s.I) := by
      rw [after_eq_prism]
      exact graph_subset_prism s hG.subset (fun _ _ => le_rfl) (fun u hu => sub_nonneg.2 (L_U_bounds s hu).2.1)
    have hface := isFace_proj s hF (f := fun _ => 0) (AffineMap.const ℝ _ (0 : ℝ)) (fun _ _ => rfl) hsub hGQ
    exact ⟨proj s '' F, IsFace.trans s.B_isPolytope hG hface, eq_graph_proj s (f := fun _ => 0) hsub⟩
  · right
    obtain ⟨-, A, ⟨K, hK, hKfull, hAK⟩, D, ⟨j, hj, hjfull, hDj⟩, rfl⟩ := hC
    have hfg : ∀ u ∈ A ∩ D, s.U u - s.L u = (upAff s j - (chainLin s K).toAffineMap) u := fun u hu => by
      rw [AffineMap.coe_sub, Pi.sub_apply, ← U_eq_on_domU s hDj.subset u hu.2,
        ← L_eq_on_domL s hAK.subset u hu.1]
    have hCB : A ∩ D ⊆ s.B := fun u hu => (hAK.subset hu.1).1
    have hGQ : graph s (fun u => s.U u - s.L u) (A ∩ D) ⊆ chainOrderPolytope P (insert s.q s.I) := by
      rw [after_eq_prism]
      exact graph_subset_prism s hCB (fun u hu => sub_nonneg.2 (L_U_bounds s hu).2.1) (fun _ _ => le_rfl)
    have hface := isFace_proj s hF (f := fun u => s.U u - s.L u) _ hfg hsub hGQ
    have hAS : A ∈ s.cellsS := ⟨K, hK, hKfull, hAK⟩
    have hDT : D ∈ s.cellsT := ⟨j, hj, hjfull, hDj⟩
    obtain ⟨A', D', hA', hD', heq⟩ := IsFace.inter_decomposition ((s.domL_isPolytope K hK).face hAK)
      ((s.domU_isPolytope j hj).face hDj) (s.cellsS_halfspaces hAS) (s.cellsT_halfspaces hDT) hface
    exact ⟨proj s '' F, ⟨hF.1.image _, A', s.cellsS_face_closed hAS hA', D', s.cellsT_face_closed hDT hD', heq⟩,
      eq_graph_proj s (f := fun u => s.U u - s.L u) hsub⟩

/-- **v4.60 l. 383-384** (informal reading, sentence 3): in both polytopes the faces of both kinds are exactly those
over the faces `G` of `B` on which `L = U` (the graph of `L` over `G` before the switch, the part of `{z = 0}` over `G`
after it), so in each dimension the two polytopes have finitely many and equally many of them. -/
theorem informal_both_kinds_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ F : Set (P → ℝ), (IsFace (chainOrderPolytope P s.I) F ∧
        (∃ C ∈ s.cellsS, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
        (∃ C ∈ s.cellsT, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})) ↔
      ∃ G, IsFace s.B G ∧ (∀ u ∈ G, s.L u = s.U u) ∧
        F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = s.L (fun p => x p.1)}) ∧
    (∀ F : Set (P → ℝ), (IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧
        (∃ G, IsFace s.B G ∧ F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
        (∃ C ∈ s.cellsR, F = {x | (fun p : s.P' => x p.1) ∈ C ∧
          x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})) ↔
      ∃ G, IsFace s.B G ∧ (∀ u ∈ G, s.L u = s.U u) ∧
        F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
    ∀ k : ℕ,
      {F : Set (P → ℝ) | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧
        (∃ C ∈ s.cellsS, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
        (∃ C ∈ s.cellsT, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})}.Finite ∧
      {F : Set (P → ℝ) | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧
        (∃ G, IsFace s.B G ∧ F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
        (∃ C ∈ s.cellsR, F = {x | (fun p : s.P' => x p.1) ∈ C ∧
          x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})}.Finite ∧
      {F : Set (P → ℝ) | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧
        (∃ C ∈ s.cellsS, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.L (fun p => x p.1)}) ∧
        (∃ C ∈ s.cellsT, F = {x | (fun p : s.P' => x p.1) ∈ C ∧ x s.q = s.U (fun p => x p.1)})}.ncard =
      {F : Set (P → ℝ) | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧
        (∃ G, IsFace s.B G ∧ F = {x | (fun p : s.P' => x p.1) ∈ G ∧ x s.q = 0}) ∧
        (∃ C ∈ s.cellsR, F = {x | (fun p : s.P' => x p.1) ∈ C ∧
          x s.q = s.U (fun p => x p.1) - s.L (fun p => x p.1)})}.ncard := by
  refine ⟨both_before s, both_after s, fun k => ⟨?_, ?_, ?_⟩⟩
  · exact (chainOrderPolytope_isPolytope P s.I).finite_faces.subset fun _ hF => hF.1
  · exact (chainOrderPolytope_isPolytope P (insert s.q s.I)).finite_faces.subset fun _ hF => hF.1
  · rw [both_before_eq_image s k, both_after_eq_image s k,
      Set.InjOn.ncard_image (fun G1 _ G2 _ h => eq_of_graph_eq s h),
      Set.InjOn.ncard_image (fun G1 _ G2 _ h => eq_of_graph_eq s h)]

/-- **v4.60 l. 395**: if `L(u) = U(u)` at a point `u` of the relative interior of a face `E` of `B`, then `L = U` on
`E` (as `U − L` is concave and nonnegative), `L` and `U` are affine on `E`, and `S|_E` and `T|_E` consist of the
nonempty faces of `E`. -/
theorem transverse_equal_case_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (u : s.P' → ℝ) (hu : u ∈ intrinsicInterior ℝ E)
    (hLU : s.L u = s.U u) :
    (∀ v ∈ E, s.L v = s.U v) ∧ AffineOn s.L E ∧ AffineOn s.U E ∧
      s.restrict s.cellsS E = {C | IsFace E C} ∧ s.restrict s.cellsT E = {C | IsFace E C} := by
  have hEq := L_eq_U_of_relint s hE.subset hu hLU
  obtain ⟨⟨K, hK⟩, hES, hET⟩ := face_mem_cells s hE hEq
  refine ⟨hEq, ⟨_, L_eq_on_domL s hK⟩,
    ⟨(chainLin s K).toAffineMap, fun v hv => (hEq v hv).symm.trans (L_eq_on_domL s hK v hv)⟩, ?_, ?_⟩
  · ext C
    constructor
    · rintro ⟨hne, A, hA, rfl⟩
      exact (s.cellsS_inter_faces hA hES hne).2
    · intro hC
      exact ⟨hC.1, C, s.cellsS_face_closed hES hC, (Set.inter_eq_left.mpr hC.subset).symm⟩
  · ext C
    constructor
    · rintro ⟨hne, D, hD, rfl⟩
      exact (s.cellsT_inter_faces hD hET hne).2
    · intro hC
      exact ⟨hC.1, C, s.cellsT_face_closed hET hC, (Set.inter_eq_left.mpr hC.subset).symm⟩

/-- **v4.60 l. 622-623**: on `E₀` all other chain coordinates vanish and all other order coordinates equal `1`, so
`L = max(α, β)` and `U = min(γ, η)` there. -/
theorem E0_L_U_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∀ u ∈ x.E0, x.toSwitch.L u = max (u x.pa) (u x.pb) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph) :=
  fun _ hu => ⟨L_on_E0 x hu, U_on_E0 x hu⟩

/-- **v4.60 l. 623-624**: `E₀` is a copy of the base of the switch of `c` in `X`: the coordinates `(α, β, γ, η)` are
injective on `E₀` and on the base `B` of the switch of `c` in `X`, and the two images are equal (both are
`{0 ≤ α, β; max(α, β) ≤ min(γ, η); γ, η ≤ 1}`). -/
theorem E0_copy_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    Set.InjOn (fun u : x.toSwitch.P' → ℝ => (![u x.pa, u x.pb, u x.pg, u x.ph] : Fin 4 → ℝ)) x.E0 ∧
    Set.InjOn (fun u : Example21.CenterSwitch.canonical.toSwitch.P' → ℝ =>
        (![u Example21.CenterSwitch.canonical.pa, u Example21.CenterSwitch.canonical.pb,
           u Example21.CenterSwitch.canonical.pg, u Example21.CenterSwitch.canonical.ph] : Fin 4 → ℝ))
      Example21.CenterSwitch.canonical.toSwitch.B ∧
    (fun u : x.toSwitch.P' → ℝ => (![u x.pa, u x.pb, u x.pg, u x.ph] : Fin 4 → ℝ)) '' x.E0 =
      (fun u : Example21.CenterSwitch.canonical.toSwitch.P' → ℝ =>
        (![u Example21.CenterSwitch.canonical.pa, u Example21.CenterSwitch.canonical.pb,
           u Example21.CenterSwitch.canonical.pg, u Example21.CenterSwitch.canonical.ph] : Fin 4 → ℝ))
        '' Example21.CenterSwitch.canonical.toSwitch.B := by
  have hc : Example21.CenterSwitch.canonical.toSwitch.B = Example21.CenterSwitch.canonical.E0 :=
    (Example21.CenterSwitch.E0_eq_B _).symm
  refine ⟨E0_injOn x, ?_, ?_⟩
  · rw [hc]
    exact E0_injOn _
  · rw [hc]
    exact (E0_image x).trans (E0_image _).symm

end HibiLi.Proofs.V450
