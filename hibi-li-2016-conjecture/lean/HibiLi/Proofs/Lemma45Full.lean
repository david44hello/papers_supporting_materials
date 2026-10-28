/-
HibiLi/Proofs/Lemma45Full.lean — proof of paper Lemma 4.5 with the full part (a): near `u₀`, membership in a face
`E ⊇ E₀` and in its relative interior are read off from `ζ` through the section `Q_E`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Lemma45
import HibiLi.Proofs.Lemma36
import HibiLi.Polytope.IntersectionFaces
import HibiLi.Defs.ExtraDefs

namespace HibiLi.Proofs

open Filter Topology

namespace Lemma45Full

section Abstract

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Line-extension test: if every segment from `u` into the convex set `C` extends a little beyond `u` inside `C`,
then `u ∈ relint C` (`u` lies strictly between a relative-interior point and a point of `C`). -/
lemma mem_intrinsicInterior_of_extend {C : Set V} (hC : Convex ℝ C) {u : V} (hu : u ∈ C)
    (h : ∀ v ∈ C, ∃ t < (0 : ℝ), AffineMap.lineMap u v t ∈ C) : u ∈ intrinsicInterior ℝ C := by
  obtain ⟨w, hw⟩ := Set.Nonempty.intrinsicInterior hC ⟨u, hu⟩
  obtain ⟨t, ht, hz⟩ := h w (intrinsicInterior_subset hw)
  have h1t : (1 - t) ≠ 0 := by linarith
  refine hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hw
    (subset_intrinsicClosure hz) ⟨-t / (1 - t), 1 / (1 - t), div_pos (by linarith) (by linarith),
      div_pos one_pos (by linarith), by field_simp; ring, ?_⟩
  have ha : -t / (1 - t) + 1 / (1 - t) * t = 0 := by field_simp; ring
  have hb : 1 / (1 - t) * (1 - t) = 1 := by field_simp
  rw [AffineMap.lineMap_apply_module']
  calc (-t / (1 - t)) • w + (1 / (1 - t)) • (t • (w - u) + u)
      = (-t / (1 - t) + 1 / (1 - t) * t) • w + (1 / (1 - t) * (1 - t)) • u := by module
    _ = u := by rw [ha, hb, zero_smul, one_smul, zero_add]

omit [FiniteDimensional ℝ V] in
/-- Short steps along a line from a point of an open set stay in it. -/
lemma eventually_lineMap_mem_open {N : Set V} (hN : IsOpen N) {u : V} (hu : u ∈ N) (v : V) :
    ∀ᶠ s in 𝓝 (0 : ℝ), AffineMap.lineMap u v s ∈ N :=
  (AffineMap.lineMap_continuous (p := u) (q := v)).continuousAt.eventually_mem
    (by rw [AffineMap.lineMap_apply_zero]; exact hN.mem_nhds hu)

/-- Relative interiors transfer along an affine `π` when, on an open set `N`, `C` is the preimage of `Q`. -/
lemma intrinsicInterior_transfer {C : Set V} {Q : Set W} (hC : Convex ℝ C) (hQ : Convex ℝ Q) (π : V → W)
    (hπ : ∀ u v (t : ℝ), π (AffineMap.lineMap u v t) = AffineMap.lineMap (π u) (π v) t)
    (hsurj : ∀ ζ ∈ Q, ∃ v ∈ C, π v = ζ) {N : Set V} (hN : IsOpen N) (hmem : ∀ u ∈ N, u ∈ C ↔ π u ∈ Q)
    {u : V} (hu : u ∈ N) : u ∈ intrinsicInterior ℝ C ↔ π u ∈ intrinsicInterior ℝ Q := by
  constructor
  · intro hi
    refine mem_intrinsicInterior_of_extend hQ ((hmem u hu).1 (intrinsicInterior_subset hi)) fun ζ hζ => ?_
    obtain ⟨v, hv, rfl⟩ := hsurj ζ hζ
    obtain ⟨s, ⟨hsC, hsN⟩, hs⟩ := (((eventually_lineMap_mem_of_intrinsicInterior hi hv).and
      (eventually_lineMap_mem_open hN hu v)).filter_mono nhdsWithin_le_nhds |>.and
      (eventually_mem_nhdsWithin (s := Set.Iio (0 : ℝ)) (a := 0))).exists
    exact ⟨s, hs, hπ u v s ▸ (hmem _ hsN).1 hsC⟩
  · intro hi
    have huC : u ∈ C := (hmem u hu).2 (intrinsicInterior_subset hi)
    refine mem_intrinsicInterior_of_extend hC huC fun v hv => ?_
    obtain ⟨t, ⟨ht0, ht1⟩, hwN⟩ := (Filter.Eventually.and (Ioo_mem_nhdsGT one_pos)
      ((eventually_lineMap_mem_open hN hu v).filter_mono nhdsWithin_le_nhds)).exists
    have hwC : AffineMap.lineMap u v t ∈ C := hC.lineMap_mem huC hv ⟨ht0.le, ht1.le⟩
    have hwQ := (hmem _ hwN).1 hwC
    obtain ⟨s, ⟨hsQ, hsN⟩, hs⟩ := (((eventually_lineMap_mem_of_intrinsicInterior hi hwQ).and
      (eventually_lineMap_mem_open hN hu (AffineMap.lineMap u v t))).filter_mono nhdsWithin_le_nhds |>.and
      (eventually_mem_nhdsWithin (s := Set.Iio (0 : ℝ)) (a := 0))).exists
    refine ⟨s * t, mul_neg_of_neg_of_pos hs ht0, ?_⟩
    rw [← AffineMap.lineMap_lineMap_right]
    exact (hmem _ hsN).2 (by rw [hπ]; exact hsQ)

end Abstract

open Lemma45

variable {P : Type*} [Fintype P] [PartialOrder P] (x : HibiLi.XSwitch P)

lemma isOpen_close : IsOpen {u | Close x u} := by
  have h : {u | Close x u} = box x.u0 (eps x) := by
    ext u
    simp [Close, box, Set.mem_pi, Metric.mem_ball, Real.dist_eq]
  rw [h]
  exact isOpen_box _ _

lemma zeta_lineMap (u v : x.toSwitch.P' → ℝ) (t : ℝ) :
    x.zeta (AffineMap.lineMap u v t) = AffineMap.lineMap (x.zeta u) (x.zeta v) t := by
  ext p
  simp [XSwitch.zeta, AffineMap.lineMap_apply_module']

lemma alphaPart_combo (a b : ℝ) (v w : x.toSwitch.P' → ℝ) :
    x.alphaPart (a • v + b • w) = a • x.alphaPart v + b • x.alphaPart w := by
  ext i
  fin_cases i <;> simp [XSwitch.alphaPart]

lemma QE_convex {E : Set (x.toSwitch.P' → ℝ)} (hEc : Convex ℝ E) : Convex ℝ (x.QE E) := by
  rintro _ ⟨v, hv, hva, rfl⟩ _ ⟨w, hw, hwa, rfl⟩ a b ha hb hab
  refine ⟨a • v + b • w, hEc hv hw ha hb hab, ?_, rfl⟩
  rw [alphaPart_combo, hva, hwa, ← add_smul, hab, one_smul]

/-- A special coordinate is fixed by `alphaPart`. -/
lemma eq_of_alphaPart {v : x.toSwitch.P' → ℝ} (hva : x.alphaPart v = x.alphaPart x.u0) {p : x.toSwitch.P'}
    (hp : p ∈ x.special) : v p = x.u0 p := by
  simp only [XSwitch.special, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · simpa [XSwitch.alphaPart] using congrFun hva 0
  · simpa [XSwitch.alphaPart] using congrFun hva 1
  · simpa [XSwitch.alphaPart] using congrFun hva 2
  · simpa [XSwitch.alphaPart] using congrFun hva 3

/-- (a), membership: on the box, `u ∈ E ↔ ζ(u) ∈ Q_E` (move `α, β, γ, η` to their `u₀`-values by Lemma 4.5). -/
lemma mem_iff_QE {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    {u : x.toSwitch.P' → ℝ} (hu : Close x u) : u ∈ E ↔ x.zeta u ∈ x.QE E := by
  classical
  constructor
  · intro huE
    let v : x.toSwitch.P' → ℝ := fun p => if p ∈ x.special then x.u0 p else u p
    have hvz : x.zeta u = x.zeta v := by
      ext ⟨p, hp⟩
      simp [XSwitch.zeta, v, hp]
    have hv : Close x v := fun p => by
      by_cases hp : p ∈ x.special
      · simp [v, hp, eps_pos x]
      · simpa [v, hp] using hu p
    have hva : x.alphaPart v = x.alphaPart x.u0 := by
      ext i
      fin_cases i <;> simp [XSwitch.alphaPart, v, XSwitch.special]
    exact ⟨v, face_transfer x hE hE0 hu hv hvz huE, hva, hvz.symm⟩
  · rintro ⟨v, hvE, hva, hvz⟩
    have hv : Close x v := fun p => by
      by_cases hp : p ∈ x.special
      · rw [eq_of_alphaPart x hva hp, sub_self, abs_zero]
        exact eps_pos x
      · rw [← eq_of_zeta x hvz hp]
        exact hu p
    exact face_transfer x hE hE0 hv hu hvz hvE

end Lemma45Full

/-- **Lemma 4.5, full form of (a)** (paper lines 752–759): for every face `E ⊇ E₀` of `B`, `ζ₀ ∈ Q_E`, and on `N₀`
both `E` and `relint E` are cut out by `ζ ∈ Q_E`, resp. `ζ ∈ relint Q_E`; part (b) as in `lemma_4_5_proved`. -/
theorem lemma_4_5_full_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)), IsOpen V4 ∧ IsOpen Vz ∧
      x.alphaPart x.u0 ∈ V4 ∧ x.zeta x.u0 ∈ Vz ∧
      (∀ E, IsFace x.toSwitch.B E → x.E0 ⊆ E → x.zeta x.u0 ∈ x.QE E ∧ ∀ u ∈ x.N0 V4 Vz,
        (u ∈ E ↔ x.zeta u ∈ x.QE E) ∧
        (u ∈ intrinsicInterior ℝ E ↔ x.zeta u ∈ intrinsicInterior ℝ (x.QE E))) ∧
      (∀ u ∈ x.toSwitch.B, u ∈ x.N0 V4 Vz →
        x.toSwitch.L u = max (u x.pa + x.lamA u) (u x.pb + x.lamB u) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) := by
  classical
  open Lemma45 Lemma45Full in
  refine ⟨box (x.alphaPart x.u0) (eps x), box (x.zeta x.u0) (eps x), isOpen_box _ _, isOpen_box _ _,
    center_mem_box _ (eps_pos x), center_mem_box _ (eps_pos x), fun E hE hE0 => ?_, fun u _ hu => ?_⟩
  · have hEc : Convex ℝ E := hE.2.convex (B_convex_closed x.toSwitch).1
    refine ⟨⟨x.u0, hE0 (mem_E0 x (fun p => by simp) (fun _ _ => rfl)), rfl, rfl⟩, fun u hu => ?_⟩
    have hc := close_of_mem x hu
    exact ⟨mem_iff_QE x hE hE0 hc, intrinsicInterior_transfer hEc (QE_convex x hEc) x.zeta (zeta_lineMap x)
      (fun _ ⟨v, hv, _, hζ⟩ => ⟨v, hv, hζ⟩) (isOpen_close x) (fun _ hw => mem_iff_QE x hE hE0 hw) hc⟩
  · exact ⟨L_eq x (close_of_mem x hu), U_eq x (close_of_mem x hu)⟩

end HibiLi.Proofs
