/-
HibiLi/Proofs/VerticalCount.lean — Section 3, informal reading of Lemma 3.2 (l. 435-441), review 006 coverage item
B5(a) sentence 3: both polytopes have equally many `k`-faces that contain a segment parallel to the `z`-axis.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

By Proposition 3.1, in the coordinates `u = x|_{P'}`, `z = x_q`, both polytopes are prisms `{u ∈ B, lo u ≤ z ≤ hi u}`:
`(lo, hi) = (L, U)` before the switch and `(0, U − L)` after. A face with a vertical segment is exposed by a functional
that vanishes on the `z`-axis, so it is the prism over a face `G` of `B` with `lo < hi` somewhere on `G`; conversely every
such prism is a vertical face. The direction of the prism is the preimage of the direction of `G` under the projection,
the same for both polytopes. So the vertical `k`-faces of both polytopes are injective images of one set of faces of `B`.
-/
import HibiLi.Proofs.Prop31
import HibiLi.Proofs.LU

namespace HibiLi.Proofs

open Classical in
/-- `F` contains a segment parallel to the `z`-axis (`z = x_q`, paper l. 440-441). -/
def HasVertical {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (F : Set (P → ℝ)) : Prop :=
  ∃ x ∈ F, ∃ t : ℝ, t ≠ 0 ∧ x + t • Pi.single s.q 1 ∈ F

namespace Vertical

open Classical

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The unit vector of the `z`-axis. -/
noncomputable def ez : P → ℝ := Pi.single s.q 1

theorem hasVertical_iff (F : Set (P → ℝ)) :
    HasVertical s F ↔ ∃ x ∈ F, ∃ t : ℝ, t ≠ 0 ∧ x + t • ez s ∈ F := Iff.rfl

/-- The projection `x ↦ u = x|_{P'}`. -/
noncomputable def proj : (P → ℝ) →L[ℝ] (s.P' → ℝ) := ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj p.1

theorem proj_apply (x : P → ℝ) (p : s.P') : proj s x p = x p.1 := rfl

/-- The section `u ↦ (q ↦ 0, p ↦ u p)` of the projection, as a linear map. -/
noncomputable def liftL : (s.P' → ℝ) →ₗ[ℝ] (P → ℝ) where
  toFun u p := if h : p = s.q then 0 else u ⟨p, h⟩
  map_add' u v := by funext p; by_cases h : p = s.q <;> simp [h]
  map_smul' c u := by funext p; by_cases h : p = s.q <;> simp [h]

/-- The section `u ↦ (q ↦ 0, p ↦ u p)`. -/
noncomputable def lift : (s.P' → ℝ) →L[ℝ] (P → ℝ) := LinearMap.toContinuousLinearMap (liftL s)

theorem lift_apply (u : s.P' → ℝ) (p : P) : lift s u p = if h : p = s.q then 0 else u ⟨p, h⟩ := rfl

/-- The point with coordinates `(u, z)`. -/
noncomputable def mk (u : s.P' → ℝ) (z : ℝ) : P → ℝ := lift s u + z • ez s

theorem proj_ez : proj s (ez s) = 0 := by
  funext p
  simp [proj_apply, ez, p.2]

theorem ez_q : ez s s.q = 1 := by
  simp [ez]

theorem proj_mk (u : s.P' → ℝ) (z : ℝ) : proj s (mk s u z) = u := by
  funext p
  simp [mk, proj_apply, lift_apply, ez, p.2]

theorem mk_q (u : s.P' → ℝ) (z : ℝ) : mk s u z s.q = z := by
  simp [mk, lift_apply, ez]

theorem mk_proj (x : P → ℝ) : mk s (proj s x) (x s.q) = x := by
  funext p
  by_cases h : p = s.q
  · subst h; simp [mk, lift_apply, ez]
  · simp [mk, lift_apply, ez, h, proj_apply]

theorem mk_add_ez (u : s.P' → ℝ) (z t : ℝ) : mk s u z + t • ez s = mk s u (z + t) := by
  simp only [mk, add_smul, add_assoc]

/-- The prism `{x : proj x ∈ G, lo (proj x) ≤ x_q ≤ hi (proj x)}` over `G`. -/
def prism (lo hi : (s.P' → ℝ) → ℝ) (G : Set (s.P' → ℝ)) : Set (P → ℝ) :=
  {x | proj s x ∈ G ∧ lo (proj s x) ≤ x s.q ∧ x s.q ≤ hi (proj s x)}

theorem mk_mem_prism {lo hi : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} {u : s.P' → ℝ} {z : ℝ} (hu : u ∈ G)
    (hlo : lo u ≤ z) (hhi : z ≤ hi u) : mk s u z ∈ prism s lo hi G := by
  refine ⟨?_, ?_, ?_⟩ <;> simpa [proj_mk, mk_q]

theorem proj_image_prism {lo hi : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} (hG : ∀ u ∈ G, lo u ≤ hi u) :
    proj s '' prism s lo hi G = G := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.1
  · intro hu
    exact ⟨mk s u (lo u), mk_mem_prism s hu le_rfl (hG u hu), proj_mk s u (lo u)⟩

/-- A prism contains a vertical segment iff `lo < hi` somewhere on its base. -/
theorem hasVertical_prism_iff {lo hi : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} :
    HasVertical s (prism s lo hi G) ↔ ∃ u ∈ G, lo u < hi u := by
  rw [hasVertical_iff]
  constructor
  · rintro ⟨x, ⟨hxG, hlo, hhi⟩, t, ht, ⟨-, hlo', hhi'⟩⟩
    simp only [map_add, map_smul, proj_ez, smul_zero, add_zero, Pi.add_apply, Pi.smul_apply, ez_q,
      smul_eq_mul, mul_one] at hlo' hhi'
    rcases ht.lt_or_gt with h | h
    · exact ⟨_, hxG, by linarith⟩
    · exact ⟨_, hxG, by linarith⟩
  · rintro ⟨u, hu, hlt⟩
    refine ⟨mk s u (lo u), mk_mem_prism s hu le_rfl hlt.le, hi u - lo u, (sub_pos.2 hlt).ne', ?_⟩
    rw [mk_add_ez, add_sub_cancel]
    exact mk_mem_prism s hu hlt.le le_rfl

/-- A functional that vanishes on the `z`-axis factors through the projection. -/
theorem apply_eq_of_ez (l : (P → ℝ) →L[ℝ] ℝ) (hl : l (ez s) = 0) (x : P → ℝ) :
    l x = (l.comp (lift s)) (proj s x) := by
  conv_lhs => rw [← mk_proj s x]
  simp [mk, hl]

/-- The prism over a face of the base is a face of the prism over the base. -/
theorem face_prism {lo hi : (s.P' → ℝ) → ℝ} {base G : Set (s.P' → ℝ)} (hlohi : ∀ u ∈ base, lo u ≤ hi u)
    (hG : IsFace base G) : IsFace (prism s lo hi base) (prism s lo hi G) := by
  obtain ⟨⟨u, hu⟩, hexp⟩ := hG
  obtain ⟨a, ha⟩ := hexp ⟨u, hu⟩
  have hGB : G ⊆ base := hexp.subset
  refine ⟨⟨mk s u (lo u), mk_mem_prism s hu le_rfl (hlohi u (hGB hu))⟩, fun _ => ⟨a.comp (proj s), ?_⟩⟩
  ext x
  constructor
  · rintro ⟨hxG, hlo, hhi⟩
    rw [ha] at hxG
    exact ⟨⟨hxG.1, hlo, hhi⟩, fun y hy => hxG.2 _ hy.1⟩
  · rintro ⟨⟨hxB, hlo, hhi⟩, hmax⟩
    refine ⟨?_, hlo, hhi⟩
    rw [ha]
    refine ⟨hxB, fun v hv => ?_⟩
    have := hmax (mk s v (lo v)) (mk_mem_prism s hv le_rfl (hlohi v hv))
    rwa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, proj_mk] at this

/-- A face of the prism over the base that contains a vertical segment is the prism over a face of the base. -/
theorem vertical_face_is_prism {lo hi : (s.P' → ℝ) → ℝ} {base : Set (s.P' → ℝ)} (hlohi : ∀ u ∈ base, lo u ≤ hi u)
    {F : Set (P → ℝ)} (hF : IsFace (prism s lo hi base) F) (hv : HasVertical s F) :
    ∃ G, IsFace base G ∧ F = prism s lo hi G := by
  obtain ⟨hne, hexp⟩ := hF
  obtain ⟨l, hl⟩ := hexp hne
  obtain ⟨x, hxF, t, ht, hxt⟩ := (hasVertical_iff s F).1 hv
  have hl0 : l (ez s) = 0 := by
    rw [hl] at hxF hxt
    have h1 := hxF.2 _ hxt.1
    have h2 := hxt.2 _ hxF.1
    rw [map_add, map_smul, smul_eq_mul] at h1 h2
    have : t * l (ez s) = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left ht
  set a := l.comp (lift s)
  have key : ∀ y, l y = a (proj s y) := apply_eq_of_ez s l hl0
  have hmaxB : ∀ y ∈ F, ∀ v ∈ base, a v ≤ a (proj s y) := by
    intro y hy v hv
    rw [hl] at hy
    have := hy.2 (mk s v (lo v)) (mk_mem_prism s hv le_rfl (hlohi v hv))
    rwa [key, key, proj_mk] at this
  obtain ⟨y, hy⟩ := hne
  refine ⟨{u ∈ base | ∀ v ∈ base, a v ≤ a u}, ⟨⟨proj s y, ?_, hmaxB y hy⟩, fun _ => ⟨a, rfl⟩⟩, ?_⟩
  · rw [hl] at hy
    exact hy.1.1
  · ext z
    constructor
    · intro hz
      have hz' := hz
      rw [hl] at hz'
      exact ⟨⟨hz'.1.1, hmaxB z hz⟩, hz'.1.2⟩
    · rintro ⟨⟨hzB, hmax⟩, hlo, hhi⟩
      rw [hl]
      exact ⟨⟨hzB, hlo, hhi⟩, fun w hw => by rw [key, key]; exact hmax _ hw.1⟩

/-- The direction of a vertical prism is the preimage of the direction of its base. -/
theorem vectorSpan_prism {lo hi : (s.P' → ℝ) → ℝ} {G : Set (s.P' → ℝ)} (hG : ∀ u ∈ G, lo u ≤ hi u)
    (hgap : ∃ u ∈ G, lo u < hi u) :
    vectorSpan ℝ (prism s lo hi G) = (vectorSpan ℝ G).comap (proj s).toLinearMap := by
  apply le_antisymm
  · rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    show proj s (x -ᵥ y) ∈ vectorSpan ℝ G
    rw [vsub_eq_sub, map_sub]
    exact vsub_mem_vectorSpan ℝ hx.1 hy.1
  · intro w hw
    rw [Submodule.mem_comap] at hw
    obtain ⟨u, hu, hlt⟩ := hgap
    have hez : ez s ∈ vectorSpan ℝ (prism s lo hi G) := by
      have h := vsub_mem_vectorSpan ℝ (mk_mem_prism s hu hlt.le le_rfl) (mk_mem_prism s hu le_rfl hlt.le)
      have hdiff : mk s u (hi u) -ᵥ mk s u (lo u) = (hi u - lo u) • ez s := by
        simp only [mk, vsub_eq_sub, sub_smul]
        abel
      rw [hdiff] at h
      have := Submodule.smul_mem _ (hi u - lo u)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ (sub_pos.2 hlt).ne', one_smul] at this
    have hlift : vectorSpan ℝ G ≤ (vectorSpan ℝ (prism s lo hi G)).comap (lift s).toLinearMap := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨u1, hu1, u2, hu2, rfl⟩
      show lift s (u1 -ᵥ u2) ∈ vectorSpan ℝ (prism s lo hi G)
      have h := vsub_mem_vectorSpan ℝ (mk_mem_prism s hu1 le_rfl (hG u1 hu1))
        (mk_mem_prism s hu2 le_rfl (hG u2 hu2))
      have hdiff : lift s (u1 -ᵥ u2) = (mk s u1 (lo u1) -ᵥ mk s u2 (lo u2)) - (lo u1 - lo u2) • ez s := by
        simp only [mk, vsub_eq_sub, map_sub, sub_smul]
        abel
      rw [hdiff]
      exact Submodule.sub_mem _ h (Submodule.smul_mem _ _ hez)
    rw [← mk_proj s w]
    exact Submodule.add_mem _ (hlift hw) (Submodule.smul_mem _ _ hez)

/-- The faces of `B` that index the vertical `k`-faces of the prism `(lo, hi)` over `B`. -/
def vIndex (lo hi : (s.P' → ℝ) → ℝ) (k : ℕ) : Set (Set (s.P' → ℝ)) :=
  {G | IsFace s.B G ∧ (∃ u ∈ G, lo u < hi u) ∧ Module.finrank ℝ ((vectorSpan ℝ G).comap (proj s).toLinearMap) = k}

theorem vertical_faces_eq_image {lo hi : (s.P' → ℝ) → ℝ} (hlohi : ∀ u ∈ s.B, lo u ≤ hi u) (k : ℕ) :
    {F | IsFace (prism s lo hi s.B) F ∧ adim F = k ∧ HasVertical s F} = prism s lo hi '' vIndex s lo hi k := by
  ext F
  constructor
  · rintro ⟨hF, hk, hv⟩
    obtain ⟨G, hG, rfl⟩ := vertical_face_is_prism s hlohi hF hv
    have hgap := (hasVertical_prism_iff s).1 hv
    refine ⟨G, ⟨hG, hgap, ?_⟩, rfl⟩
    rw [← hk, adim, vectorSpan_prism s (fun u hu => hlohi u (hG.2.subset hu)) hgap]
  · rintro ⟨G, ⟨hG, hgap, hk⟩, rfl⟩
    refine ⟨face_prism s hlohi hG, ?_, (hasVertical_prism_iff s).2 hgap⟩
    rw [adim, vectorSpan_prism s (fun u hu => hlohi u (hG.2.subset hu)) hgap, hk]

theorem vertical_count {lo hi : (s.P' → ℝ) → ℝ} (hlohi : ∀ u ∈ s.B, lo u ≤ hi u) (k : ℕ) :
    {F | IsFace (prism s lo hi s.B) F ∧ adim F = k ∧ HasVertical s F}.ncard = (vIndex s lo hi k).ncard := by
  rw [vertical_faces_eq_image s hlohi k]
  refine Set.InjOn.ncard_image fun G1 h1 G2 h2 heq => ?_
  rw [← proj_image_prism s (lo := lo) (hi := hi) (fun u hu => hlohi u (h1.1.2.subset hu)), heq,
    proj_image_prism s (fun u hu => hlohi u (h2.1.2.subset hu))]

end Vertical

open Vertical in
/-- **Section 3, l. 435-441** (informal reading of Lemma 3.2): the two polytopes have equally many `k`-faces that
contain a segment parallel to the `z`-axis. -/
theorem sec3_informal_vertical_count {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (k : ℕ) :
    {F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ HasVertical s F}.ncard =
      {F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ HasVertical s F}.ncard := by
  have hA : chainOrderPolytope P s.I = prism s s.L s.U s.B := Set.ext fun x => (prop_3_1_proved s x).1
  have hC : chainOrderPolytope P (insert s.q s.I) = prism s (fun _ => 0) (fun u => s.U u - s.L u) s.B :=
    Set.ext fun x => (prop_3_1_proved s x).2
  rw [hA, hC, vertical_count s (fun u hu => (L_U_bounds s hu).2.1),
    vertical_count s (fun u hu => sub_nonneg.2 (L_U_bounds s hu).2.1)]
  congr 1
  ext G
  exact and_congr_right fun _ => and_congr_left fun _ => exists_congr fun u =>
    and_congr_right fun _ => (sub_pos (a := s.U u) (b := s.L u)).symm

end HibiLi.Proofs
