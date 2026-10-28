/-
HibiLi/Proofs/Lemma46.lean — proof of paper Lemma 4.6 (every face `E ⊇ E₀` has a crossing point), using Lemma 3.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Lemma45
import HibiLi.Proofs.LU
import HibiLi.Polytope.SwitchDomains

namespace HibiLi.Proofs

open Finset Filter Topology Metric

namespace Lemma46

section Abstract

variable {ι : Type*} [Fintype ι]

/-- Membership in the intrinsic interior, metrically: a ball of the affine span lies in the set. -/
lemma mem_intrinsicInterior_iff {s : Set (ι → ℝ)} {x : ι → ℝ} :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ affineSpan ℝ s ∧ ∃ ε > 0, ∀ y ∈ affineSpan ℝ s, dist y x < ε → y ∈ s := by
  rw [mem_intrinsicInterior]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
    obtain ⟨ε, hε, hball⟩ := hy
    exact ⟨y.2, ε, hε, fun z hz hdist => hball (show (⟨z, hz⟩ : affineSpan ℝ s) ∈ ball y ε from hdist)⟩
  · rintro ⟨hx, ε, hε, hball⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    exact ⟨ε, hε, fun z hz => hball z.1 z.2 hz⟩

omit [Fintype ι] in
lemma linear_lineMap (φ : (ι → ℝ) →ₗ[ℝ] ℝ) (p v : ι → ℝ) (t : ℝ) :
    φ (AffineMap.lineMap p v t) = φ p + t * (φ v - φ p) := by
  rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

omit [Fintype ι] in
/-- Two affine functions that agree at `p` and at `lineMap p v t` (`t ≠ 0`) agree at `v`. -/
lemma agree_of_lineMap (g g' : (ι → ℝ) →ᵃ[ℝ] ℝ) {p v : ι → ℝ} {t : ℝ} (ht : t ≠ 0) (hp : g p = g' p)
    (hq : g (AffineMap.lineMap p v t) = g' (AffineMap.lineMap p v t)) : g v = g' v := by
  rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring',
    AffineMap.lineMap_apply_ring', hp] at hq
  have h := mul_left_cancel₀ ht (add_right_cancel hq)
  linarith

/-- A short step from `p ∈ ball w r` towards `v` stays in the ball. -/
lemma eventually_lineMap_mem_ball {p v w : ι → ℝ} {r : ℝ} (hp : p ∈ ball w r) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 ∧ AffineMap.lineMap p v t ∈ ball w r := by
  have hc : ContinuousAt (fun t : ℝ => AffineMap.lineMap p v t) 0 :=
    AffineMap.lineMap_continuous.continuousAt
  have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), AffineMap.lineMap p v t ∈ ball w r :=
    hc.eventually_mem (isOpen_ball.mem_nhds (by simpa using hp))
  exact Filter.Eventually.and (Ioo_mem_nhdsGT one_pos) (nhdsWithin_le_nhds h1)

/-- From a point `p` of `N = E ∩ ball w r` with `φ w < φ p`, a short step towards any `v ∈ E` stays in `N` on
the same open side. -/
lemma exists_step {E : Set (ι → ℝ)} (hE : Convex ℝ E) {w p v : ι → ℝ} {r : ℝ} (φ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hp : p ∈ E ∩ ball w r) (hφp : φ w < φ p) (hv : v ∈ E) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, AffineMap.lineMap p v t ∈ E ∩ ball w r ∧ φ w < φ (AffineMap.lineMap p v t) := by
  have hc : ContinuousAt (fun t : ℝ => φ (AffineMap.lineMap p v t)) 0 :=
    (φ.continuous_of_finiteDimensional.comp AffineMap.lineMap_continuous).continuousAt
  have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), φ w < φ (AffineMap.lineMap p v t) :=
    hc.eventually (lt_mem_nhds (by simpa using hφp))
  obtain ⟨t, ⟨ht, hball⟩, hφ⟩ := ((eventually_lineMap_mem_ball (v := v) hp.2).and (nhdsWithin_le_nhds h2)).exists
  exact ⟨t, ht, ⟨hE.lineMap_mem hp.1 hv ⟨ht.1.le, ht.2.le⟩, hball⟩, hφ⟩

omit [Fintype ι] in
lemma vectorSpan_le_ker {A : Set (ι → ℝ)} (φ : (ι → ℝ) →ₗ[ℝ] ℝ) {c : ℝ} (hA : ∀ u ∈ A, φ u = c) :
    vectorSpan ℝ A ≤ LinearMap.ker φ := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨u, hu, v, hv, rfl⟩
  simp [hA u hu, hA v hv]

/-- A convex `A ⊆ E` with `dim A = dim E` that meets `N = E ∩ ball w r` meets it off the hyperplane `φ = φ w`, when
`φ` does not vanish on `dir E`. -/
lemma exists_off_hyperplane {E A : Set (ι → ℝ)} (hAc : Convex ℝ A) (hAE : A ⊆ E) (hdim : adim A = adim E)
    (φ : (ι → ℝ) →ₗ[ℝ] ℝ) {v₀ : ι → ℝ} (hv₀ : v₀ ∈ vectorSpan ℝ E) (hφ : φ v₀ ≠ 0) {w u : ι → ℝ} {r : ℝ}
    (hu : u ∈ A ∩ (E ∩ ball w r)) : ∃ p ∈ A ∩ (E ∩ ball w r), φ p ≠ φ w := by
  by_cases h : φ u = φ w
  · obtain ⟨v, hvA, hv⟩ : ∃ v ∈ A, φ v ≠ φ w := by
      by_contra hcon
      push Not at hcon
      have heq : vectorSpan ℝ A = vectorSpan ℝ E := Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hAE) hdim
      exact hφ (LinearMap.mem_ker.mp (vectorSpan_le_ker φ hcon (heq ▸ hv₀)))
    obtain ⟨t, ht, hball⟩ := (eventually_lineMap_mem_ball (v := v) hu.2.2).exists
    have hmem := hAc.lineMap_mem hu.1 hvA ⟨ht.1.le, ht.2.le⟩
    refine ⟨_, ⟨hmem, hAE hmem, hball⟩, ?_⟩
    rw [linear_lineMap, h]
    intro he
    have : t * (φ v - φ w) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact ht.1.ne' h0
    · exact hv (by linarith)
  · exact ⟨u, hu, h⟩

/-- A point `p ∈ E ∩ ball w r` with `φ w < φ p`, from a direction `v ∈ dir E` with `φ v > 0` and a ball of
`aff E` around `w` inside `E`. -/
lemma exists_side_point {E : Set (ι → ℝ)} {w : ι → ℝ} (hw : w ∈ affineSpan ℝ E) {ρ r : ℝ} (hρ : 0 < ρ)
    (hr : 0 < r) (hrel : ∀ y ∈ affineSpan ℝ E, dist y w < ρ → y ∈ E) (φ : (ι → ℝ) →ₗ[ℝ] ℝ) {v : ι → ℝ}
    (hv : v ∈ vectorSpan ℝ E) (hφv : 0 < φ v) : ∃ p ∈ E ∩ ball w r, φ w < φ p := by
  have hm : 0 < min ρ r := lt_min hρ hr
  obtain ⟨t, ⟨ht0, -⟩, hball⟩ := (eventually_lineMap_mem_ball (v := w + v) (mem_ball_self hm)).exists
  have hy : AffineMap.lineMap w (w + v) t = w + t • v := by
    rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  rw [hy] at hball
  have hmem : w + t • v ∈ affineSpan ℝ E := by
    rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction
      (by rw [direction_affineSpan]; exact Submodule.smul_mem _ t hv) hw
  refine ⟨w + t • v, ⟨hrel _ hmem (lt_of_lt_of_le (mem_ball.mp hball) (min_le_left _ _)),
    mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hball) (min_le_right _ _))⟩, ?_⟩
  rw [map_add, map_smul, smul_eq_mul]
  nlinarith

section TwoCells

variable {E : Set (ι → ℝ)} (F : (ι → ℝ) → ℝ) (Cell : Set (ι → ℝ) → Prop)

/-- The common step: if `F` is affine (`= g'`) on `D ⊆ E`, and `F = g` near `w` on the side `φ ≥ φ w`, then a point
`p ∈ D` on the open side whose short steps towards `D` stay in `D` forces `F = g` on all of `D`. -/
lemma eq_of_step (hE : Convex ℝ E) (g φ : (ι → ℝ) →ₗ[ℝ] ℝ) (g' : (ι → ℝ) →ᵃ[ℝ] ℝ) {w : ι → ℝ} {r : ℝ}
    (hg : ∀ u ∈ E ∩ ball w r, φ w ≤ φ u → F u = g u) {D : Set (ι → ℝ)} (hDE : D ⊆ E)
    (hD : ∀ u ∈ D, F u = g' u) {p : ι → ℝ} (hp : p ∈ D ∩ (E ∩ ball w r)) (hφp : φ w < φ p)
    (hstep : ∀ v ∈ D, ∀ t ∈ Set.Ioo (0 : ℝ) 1, AffineMap.lineMap p v t ∈ E ∩ ball w r →
      φ w < φ (AffineMap.lineMap p v t) → AffineMap.lineMap p v t ∈ D)
    {v : ι → ℝ} (hv : v ∈ D) : F v = g v := by
  obtain ⟨t, ht, hqN, hφq⟩ := exists_step hE φ hp.2 hφp (hDE hv)
  have hqD := hstep v hv t ht hqN hφq
  have h := agree_of_lineMap g.toAffineMap g' ht.1.ne'
    (by rw [LinearMap.coe_toAffineMap, ← hg p hp.2 hφp.le, hD p hp.1])
    (by rw [LinearMap.coe_toAffineMap, ← hg _ hqN hφq.le, hD _ hqD])
  rw [hD v hv, ← h, LinearMap.coe_toAffineMap]

/-- One side of a crossing: `S = {u ∈ E | F u = g u}` is a cell (Lemma 3.6's characterization), and every cell
meeting `N` on the open side `φ > φ w` is `S`. -/
lemma side_cell (hE : Convex ℝ E)
    (hcell : ∀ A, Cell A ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn F A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn F D → D = A)
    (g φ : (ι → ℝ) →ₗ[ℝ] ℝ) {w : ι → ℝ} {r : ℝ} (hg : ∀ u ∈ E ∩ ball w r, φ w ≤ φ u → F u = g u)
    (hc : Convex ℝ {u | u ∈ E ∧ F u = g u}) {p₁ : ι → ℝ} (hp₁ : p₁ ∈ E ∩ ball w r) (hφp₁ : φ w < φ p₁) :
    Cell {u | u ∈ E ∧ F u = g u} ∧
      ∀ A, Cell A → ∀ p ∈ A ∩ (E ∩ ball w r), φ w < φ p → A = {u | u ∈ E ∧ F u = g u} := by
  set S := {u | u ∈ E ∧ F u = g u} with hS
  have hSE : S ⊆ E := fun u hu => hu.1
  have hNS : ∀ u ∈ E ∩ ball w r, φ w ≤ φ u → u ∈ S := fun u hu h => ⟨hu.1, hg u hu h⟩
  have hSaff : AffineOn F S := ⟨g.toAffineMap, fun u hu => hu.2⟩
  have hp₁S := hNS p₁ hp₁ hφp₁.le
  have hspan : vectorSpan ℝ E ≤ vectorSpan ℝ S := by
    have aux : ∀ e ∈ E, e -ᵥ p₁ ∈ vectorSpan ℝ S := fun e he => by
      obtain ⟨t, ht, hqN, hφq⟩ := exists_step hE φ hp₁ hφp₁ he
      have hmem := vsub_mem_vectorSpan ℝ (hNS _ hqN hφq.le) hp₁S
      rw [AffineMap.lineMap_vsub_left] at hmem
      have h2 := Submodule.smul_mem _ t⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ ht.1.ne', one_smul] at h2
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨e, he, e', he', rfl⟩
    have h := Submodule.sub_mem _ (aux e he) (aux e' he')
    rwa [vsub_sub_vsub_cancel_right] at h
  have hdim : adim S = adim E :=
    le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ hSE)) (Submodule.finrank_mono hspan)
  refine ⟨(hcell S).mpr ⟨hSE, hc, hdim, hSaff, fun D hSD hDE _ ⟨g', hg'⟩ => ?_⟩, fun A hA p hp hφp => ?_⟩
  · refine Set.Subset.antisymm (fun v hv => ⟨hDE hv, ?_⟩) hSD
    exact eq_of_step F hE g φ g' hg hDE hg' ⟨hSD hp₁S, hp₁⟩ hφp₁
      (fun _ _ _ _ hq hφq => hSD (hNS _ hq hφq.le)) hv
  · obtain ⟨hAE, hAc, -, ⟨g', hg'⟩, hmax⟩ := (hcell A).mp hA
    have hAS : A ⊆ S := fun v hv => ⟨hAE hv, eq_of_step F hE g φ g' hg hAE hg' hp hφp
      (fun v hv t ht _ _ => hAc.lineMap_mem hp.1 hv ⟨ht.1.le, ht.2.le⟩) hv⟩
    exact (hmax S hAS hSE hc hSaff).symm

/-- **Two cells at a crossing.**  Near `w`, `F` is `g₁` on the side `φ ≥ φ w` and `g₂` on the side `φ ≤ φ w`; then
`S₁ = {F = g₁}` and `S₂ = {F = g₂}` (inside `E`) are cells, they are the only cells meeting `N = E ∩ ball w r`, and
they cut `N` along `φ = φ w`. -/
lemma two_cells (hE : Convex ℝ E)
    (hcell : ∀ A, Cell A ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧ AffineOn F A ∧
      ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn F D → D = A)
    (g₁ g₂ φ : (ι → ℝ) →ₗ[ℝ] ℝ) {w : ι → ℝ} {r : ℝ}
    (h1 : ∀ u ∈ E ∩ ball w r, F u = g₁ u ↔ φ w ≤ φ u) (h2 : ∀ u ∈ E ∩ ball w r, F u = g₂ u ↔ φ u ≤ φ w)
    (hc1 : Convex ℝ {u | u ∈ E ∧ F u = g₁ u}) (hc2 : Convex ℝ {u | u ∈ E ∧ F u = g₂ u})
    {p₁ p₂ : ι → ℝ} (hp₁ : p₁ ∈ E ∩ ball w r) (hφp₁ : φ w < φ p₁) (hp₂ : p₂ ∈ E ∩ ball w r)
    (hφp₂ : φ p₂ < φ w) {v₀ : ι → ℝ} (hv₀ : v₀ ∈ vectorSpan ℝ E) (hφv₀ : φ v₀ ≠ 0) :
    Cell {u | u ∈ E ∧ F u = g₁ u} ∧ Cell {u | u ∈ E ∧ F u = g₂ u} ∧
    (∀ A, Cell A → (A ∩ (E ∩ ball w r)).Nonempty →
      A = {u | u ∈ E ∧ F u = g₁ u} ∨ A = {u | u ∈ E ∧ F u = g₂ u}) ∧
    {u | u ∈ E ∧ F u = g₁ u} ∩ (E ∩ ball w r) = {u ∈ E ∩ ball w r | φ w ≤ φ u} ∧
    {u | u ∈ E ∧ F u = g₂ u} ∩ (E ∩ ball w r) = {u ∈ E ∩ ball w r | φ u ≤ φ w} := by
  have s1 := side_cell F Cell hE hcell g₁ φ (fun u hu h => (h1 u hu).mpr h) hc1 hp₁ hφp₁
  have s2 := side_cell F Cell hE hcell g₂ (-φ)
    (fun u hu h => (h2 u hu).mpr (by simpa using h)) hc2 hp₂ (by simpa using hφp₂)
  refine ⟨s1.1, s2.1, fun A hA ⟨u, hu⟩ => ?_, ?_, ?_⟩
  · obtain ⟨hAE, hAc, hdim, -⟩ := (hcell A).mp hA
    obtain ⟨p, hp, hφp⟩ := exists_off_hyperplane hAc hAE hdim φ hv₀ hφv₀ hu
    rcases lt_or_gt_of_ne hφp with hlt | hgt
    · exact Or.inr (s2.2 A hA p hp (by simpa using hlt))
    · exact Or.inl (s1.2 A hA p hp hgt)
  · ext u
    exact ⟨fun ⟨⟨_, hF⟩, hN⟩ => ⟨hN, (h1 u hN).mp hF⟩, fun ⟨hN, h⟩ => ⟨⟨hN.1, (h1 u hN).mpr h⟩, hN⟩⟩
  · ext u
    exact ⟨fun ⟨⟨_, hF⟩, hN⟩ => ⟨hN, (h2 u hN).mp hF⟩, fun ⟨hN, h⟩ => ⟨⟨hN.1, (h2 u hN).mpr h⟩, hN⟩⟩

end TwoCells

/-- Points of the intrinsic interior arbitrarily close to any point `u` of a nonempty convex set. -/
lemma exists_relint_near {E : Set (ι → ℝ)} (hEc : Convex ℝ E) {u : ι → ℝ} (hu : u ∈ E) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z ∈ intrinsicInterior ℝ E, dist z u < δ := by
  obtain ⟨w', hw'⟩ := Set.Nonempty.intrinsicInterior hEc ⟨u, hu⟩
  have hc : ContinuousAt (fun t : ℝ => AffineMap.lineMap w' u t) 1 := AffineMap.lineMap_continuous.continuousAt
  have h1 : ∀ᶠ t in 𝓝 (1 : ℝ), AffineMap.lineMap w' u t ∈ ball u δ :=
    hc.eventually_mem (isOpen_ball.mem_nhds (by simpa using hδ))
  obtain ⟨t, ht, hball⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT one_pos) (nhdsWithin_le_nhds h1)).exists
  refine ⟨_, hEc.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hw'
    (subset_intrinsicClosure hu) ?_, hball⟩
  rw [openSegment_eq_image_lineMap]
  exact ⟨t, ht, rfl⟩

end Abstract

section Concrete

open Classical

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

lemma B_convex : Convex ℝ x.toSwitch.B := by
  obtain ⟨S, hS⟩ := Switch.B_isPolytope x.toSwitch
  rw [hS]
  exact convex_convexHull ℝ _

/-- The chain sum `u ↦ Σ_{p∈K} u_p` as a linear map. -/
noncomputable def csL (K : Finset x.toSwitch.P') : (x.toSwitch.P' → ℝ) →ₗ[ℝ] ℝ :=
  ∑ p ∈ K, LinearMap.proj (R := ℝ) (φ := fun _ : x.toSwitch.P' => ℝ) p

lemma csL_apply (K : Finset x.toSwitch.P') (u : x.toSwitch.P' → ℝ) : csL x K u = x.toSwitch.chainSum K u := by
  simp [csL, Switch.chainSum]

/-- The coordinate functional `u ↦ u_p`. -/
abbrev crd (p : x.toSwitch.P') : (x.toSwitch.P' → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj (R := ℝ) (φ := fun _ : x.toSwitch.P' => ℝ) p

lemma mem_low {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) :
    ↑K ⊆ x.toSwitch.I' ∧ IsChainSet x.toSwitch.P' K ∧ ∀ p ∈ K, p.1 < x.toSwitch.q := by
  simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hK
  exact hK

/-- A chain of `L` contains at most one of the incomparable `a, b`. -/
lemma not_both {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) (ha : x.pa ∈ K) (hb : x.pb ∈ K) :
    False := by
  rcases (mem_low x hK).2.1 ha hb (Lemma45.distinct x).1 with h | h
  · exact x.isX.2.2.2.2.1 h
  · exact x.isX.2.2.2.2.2.1 h

/-- A coordinate of a form `Σ_{p∈K∖{c}} u_p` (`c ∈ {a, b}`, `c ∈ K`) is not special. -/
lemma form_not_special {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) {pc : x.toSwitch.P'}
    (hpc : pc = x.pa ∨ pc = x.pb) (hcK : pc ∈ K) {p : x.toSwitch.P'} (hp : p ∈ K.erase pc) : p ∉ x.special := by
  obtain ⟨hne, hpK⟩ := Finset.mem_erase.mp hp
  refine Lemma45.not_special_I x ((mem_low x hK).1 hpK) ?_ ?_
  · rintro rfl
    rcases hpc with rfl | rfl
    exacts [hne rfl, not_both x hK hpK hcK]
  · rintro rfl
    rcases hpc with rfl | rfl
    exacts [not_both x hK hcK hpK, hne rfl]

/-- The forms do not see the special coordinates. -/
lemma form_add {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) {pc : x.toSwitch.P'}
    (hpc : pc = x.pa ∨ pc = x.pb) (hcK : pc ∈ K) {u d : x.toSwitch.P' → ℝ} (hd : ∀ p, p ∉ x.special → d p = 0) :
    x.toSwitch.chainSum (K.erase pc) (u + d) = x.toSwitch.chainSum (K.erase pc) u := by
  unfold Switch.chainSum
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Pi.add_apply, hd p (form_not_special x hK hpc hcK hp), add_zero]

/-- Every form vanishes at `u₀` (at `ζ₀`). -/
lemma form_u0 {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) {pc : x.toSwitch.P'}
    (hpc : pc = x.pa ∨ pc = x.pb) (hcK : pc ∈ K) : x.toSwitch.chainSum (K.erase pc) x.u0 = 0 := by
  unfold Switch.chainSum
  exact Finset.sum_eq_zero fun p hp =>
    Lemma45.u0_I x (form_not_special x hK hpc hcK hp) ((mem_low x hK).1 (Finset.mem_of_mem_erase hp))

/-- The properties of `λ_a` (with `c = a`) and `λ_b` (with `c = b`) that the proof uses. -/
structure Family (lam : (x.toSwitch.P' → ℝ) → ℝ) (pc : x.toSwitch.P') : Prop where
  attain : ∀ u, ∃ K ∈ x.toSwitch.lowBranches, pc ∈ K ∧ x.toSwitch.chainSum (K.erase pc) u = lam u
  le : ∀ u, ∀ K ∈ x.toSwitch.lowBranches, pc ∈ K → x.toSwitch.chainSum (K.erase pc) u ≤ lam u
  cont : Continuous lam
  add : ∀ u d, (∀ p, p ∉ x.special → d p = 0) → lam (u + d) = lam u
  at_u0 : lam x.u0 = 0

lemma family_of_sup {s : Finset (Finset x.toSwitch.P')} (hs : s.Nonempty) {pc : x.toSwitch.P'}
    (hpc : pc = x.pa ∨ pc = x.pb) (hmem : ∀ K, K ∈ s ↔ K ∈ x.toSwitch.lowBranches ∧ pc ∈ K) :
    Family x (fun u => s.sup' hs fun K => x.toSwitch.chainSum (K.erase pc) u) pc where
  attain u := by
    obtain ⟨K, hK, h⟩ := Finset.exists_mem_eq_sup' hs fun K => x.toSwitch.chainSum (K.erase pc) u
    exact ⟨K, ((hmem K).mp hK).1, ((hmem K).mp hK).2, h.symm⟩
  le u K hK hcK := Finset.le_sup' (fun K => x.toSwitch.chainSum (K.erase pc) u) ((hmem K).mpr ⟨hK, hcK⟩)
  cont := Continuous.finset_sup'_apply hs fun K _ => continuous_finsetSum _ fun p _ => continuous_apply p
  add u d hd := Finset.sup'_congr hs rfl fun K hK => form_add x ((hmem K).mp hK).1 hpc ((hmem K).mp hK).2 hd
  at_u0 := by
    obtain ⟨K, hK, h⟩ := Finset.exists_mem_eq_sup' hs fun K => x.toSwitch.chainSum (K.erase pc) x.u0
    rw [h]
    exact form_u0 x ((hmem K).mp hK).1 hpc ((hmem K).mp hK).2

lemma familyA : Family x x.lamA x.pa := by
  show Family x (fun u => x.lamA u) x.pa
  unfold XSwitch.lamA
  exact family_of_sup x _ (Or.inl rfl) fun K => Finset.mem_filter

lemma familyB : Family x x.lamB x.pb := by
  show Family x (fun u => x.lamB u) x.pb
  unfold XSwitch.lamB
  exact family_of_sup x _ (Or.inr rfl) fun K => Finset.mem_filter

/-- The forms of the `c`-family attaining `λ` at `u`. -/
noncomputable def maxSet (lam : (x.toSwitch.P' → ℝ) → ℝ) (pc : x.toSwitch.P') (u : x.toSwitch.P' → ℝ) :
    Finset (Finset x.toSwitch.P') :=
  x.toSwitch.lowBranches.filter fun K => pc ∈ K ∧ x.toSwitch.chainSum (K.erase pc) u = lam u

lemma mem_maxSet {lam : (x.toSwitch.P' → ℝ) → ℝ} {pc : x.toSwitch.P'} {u : x.toSwitch.P' → ℝ}
    {K : Finset x.toSwitch.P'} :
    K ∈ maxSet x lam pc u ↔ K ∈ x.toSwitch.lowBranches ∧ pc ∈ K ∧ x.toSwitch.chainSum (K.erase pc) u = lam u := by
  unfold maxSet
  exact Finset.mem_filter

/-- Upper semicontinuity: near `z`, only forms attaining `λ` at `z` can attain it. -/
lemma maxSet_usc {lam : (x.toSwitch.P' → ℝ) → ℝ} {pc : x.toSwitch.P'} (hF : Family x lam pc)
    (z : x.toSwitch.P' → ℝ) : ∀ᶠ u in 𝓝 z, maxSet x lam pc u ⊆ maxSet x lam pc z := by
  obtain ⟨K₀, hK₀, hc₀, hK₀z⟩ := hF.attain z
  have cont : ∀ K : Finset x.toSwitch.P', Continuous fun u : x.toSwitch.P' → ℝ =>
      x.toSwitch.chainSum (K.erase pc) u := fun K => continuous_finsetSum _ fun p _ => continuous_apply p
  have h : ∀ K : Finset x.toSwitch.P', ∀ᶠ u in 𝓝 z, K ∈ maxSet x lam pc u → K ∈ maxSet x lam pc z := by
    intro K
    by_cases hKz : K ∈ maxSet x lam pc z
    · exact Eventually.of_forall fun _ _ => hKz
    by_cases hK : K ∈ x.toSwitch.lowBranches ∧ pc ∈ K
    · have hlt : x.toSwitch.chainSum (K.erase pc) z < x.toSwitch.chainSum (K₀.erase pc) z := by
        rw [hK₀z]
        exact lt_of_le_of_ne (hF.le z K hK.1 hK.2) fun h => hKz (mem_maxSet x |>.mpr ⟨hK.1, hK.2, h⟩)
      filter_upwards [(cont K).continuousAt.eventually_lt (cont K₀).continuousAt hlt] with u hu hKu
      exact absurd (mem_maxSet x |>.mp hKu).2.2 (ne_of_lt (lt_of_lt_of_le hu (hF.le u K₀ hK₀ hc₀)))
    · exact Eventually.of_forall fun u hKu =>
        absurd ⟨(mem_maxSet x |>.mp hKu).1, (mem_maxSet x |>.mp hKu).2.1⟩ hK
  filter_upwards [Filter.eventually_all.mpr h] with u hu K hK using hu K hK

/-- **Generic point.**  In any nonempty set `Z` there is a point `z` near which (within `Z`) the attaining forms of
both families do not change: minimize the number of attaining forms. -/
lemma exists_generic (Z : Set (x.toSwitch.P' → ℝ)) (hZ : Z.Nonempty) :
    ∃ z ∈ Z, ∀ᶠ u in 𝓝 z, u ∈ Z →
      maxSet x x.lamA x.pa u = maxSet x x.lamA x.pa z ∧ maxSet x x.lamB x.pb u = maxSet x x.lamB x.pb z := by
  classical
  let m : (x.toSwitch.P' → ℝ) → ℕ := fun u => (maxSet x x.lamA x.pa u).card + (maxSet x x.lamB x.pb u).card
  have hex : ∃ n, ∃ z ∈ Z, m z = n := ⟨_, hZ.some, hZ.some_mem, rfl⟩
  obtain ⟨z, hzZ, hz⟩ := Nat.find_spec hex
  refine ⟨z, hzZ, ?_⟩
  filter_upwards [maxSet_usc x (familyA x) z, maxSet_usc x (familyB x) z] with u hA hB huZ
  have hmin : m z ≤ m u := by
    rw [hz]
    exact Nat.find_min' hex ⟨u, huZ, rfl⟩
  have cA := Finset.card_le_card hA
  have cB := Finset.card_le_card hB
  simp only [m] at hmin
  exact ⟨Finset.eq_of_subset_of_card_le hA (by omega), Finset.eq_of_subset_of_card_le hB (by omega)⟩

/-- `{u ∈ E | L u = ℓ_K u}` is convex (`L` convex, `L ≥ ℓ_K`). -/
lemma convex_L_piece {E : Set (x.toSwitch.P' → ℝ)} (hEc : Convex ℝ E) {K : Finset x.toSwitch.P'}
    (hK : K ∈ x.toSwitch.lowBranches) : Convex ℝ {u | u ∈ E ∧ x.toSwitch.L u = csL x K u} := by
  intro u hu v hv a b ha hb hab
  refine ⟨hEc hu.1 hv.1 ha hb hab, le_antisymm ?_ ?_⟩
  · calc x.toSwitch.L (a • u + b • v) ≤ a • x.toSwitch.L u + b • x.toSwitch.L v :=
          (L_convex x.toSwitch).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ = csL x K (a • u + b • v) := by rw [hu.2, hv.2, map_add, map_smul, map_smul]
  · rw [csL_apply]
    exact chainSum_le_L x.toSwitch hK _

/-- `{u ∈ E | U u = u_r}` is convex (`U` concave, `U ≤ u_r`). -/
lemma convex_U_piece {E : Set (x.toSwitch.P' → ℝ)} (hEc : Convex ℝ E) {r : x.toSwitch.P'}
    (hr : some r ∈ x.toSwitch.upBranches) : Convex ℝ {u | u ∈ E ∧ x.toSwitch.U u = crd x r u} := by
  intro u hu v hv a b ha hb hab
  refine ⟨hEc hu.1 hv.1 ha hb hab, le_antisymm (U_le_upVal x.toSwitch hr _) ?_⟩
  calc crd x r (a • u + b • v) = a • x.toSwitch.U u + b • x.toSwitch.U v := by
        rw [map_add, map_smul, map_smul, ← hu.2, ← hv.2]
    _ ≤ x.toSwitch.U (a • u + b • v) := (U_concave x.toSwitch).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

lemma some_mem_up {r : x.toSwitch.P'} (hr : r = x.pg ∨ r = x.ph) : some r ∈ x.toSwitch.upBranches := by
  classical
  simp only [Switch.upBranches, Finset.mem_insert, reduceCtorEq, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Option.some.injEq, false_or]
  rcases hr with rfl | rfl
  exacts [⟨x.pg, x.q_covby_g'.lt, rfl⟩, ⟨x.ph, x.q_covby_h'.lt, rfl⟩]

/-- The four coordinate directions `α, β, γ, η` lie in `dir E₀ ⊆ dir E`. -/
lemma singles_mem {E : Set (x.toSwitch.P' → ℝ)} (hE0 : x.E0 ⊆ E) :
    Pi.single x.pa (1 : ℝ) ∈ vectorSpan ℝ E ∧ Pi.single x.pb (1 : ℝ) ∈ vectorSpan ℝ E ∧
    Pi.single x.pg (1 : ℝ) ∈ vectorSpan ℝ E ∧ Pi.single x.ph (1 : ℝ) ∈ vectorSpan ℝ E := by
  obtain ⟨hab, hag, hah, hbg, hbh, hgh⟩ := Lemma45.distinct x
  have h0 := Lemma44.v0_mem x (pa := x.pa) (pb := x.pb) (pg := x.pg) (ph := x.ph) rfl rfl rfl rfl
  have mem := Lemma44.perturb_mem x (pa := x.pa) (pb := x.pb) (pg := x.pg) (ph := x.ph) rfl rfl rfl rfl
  have hV := vectorSpan_mono ℝ hE0
  refine ⟨hV ?_, hV ?_, hV ?_, hV ?_⟩
  · have h := mem (Pi.single x.pa 1) (fun p hp _ _ _ => by simp [hp])
      (by simp) (by simp [hab.symm]) (by simp [hab.symm, hag.symm, hah.symm])
      (by simp [hag.symm]) (by simp [hah.symm])
    simpa using vsub_mem_vectorSpan ℝ h h0
  · have h := mem (Pi.single x.pb 1) (fun p _ hp _ _ => by simp [hp])
      (by simp [hab]) (by simp) (by simp [hab, hbg.symm, hbh.symm])
      (by simp [hbg.symm]) (by simp [hbh.symm])
    simpa using vsub_mem_vectorSpan ℝ h h0
  · have h := mem (-Pi.single x.pg 1) (fun p _ _ hp _ => by simp [hp])
      (by simp [hag]) (by simp [hbg]) (by simp [hag, hbg, hgh.symm])
      (by simp) (by simp [hgh.symm])
    simpa using vsub_mem_vectorSpan ℝ h0 h
  · have h := mem (-Pi.single x.ph 1) (fun p _ _ _ hp => by simp [hp])
      (by simp [hah]) (by simp [hbh]) (by simp [hah, hbh, hgh])
      (by simp [hgh]) (by simp)
    simpa using vsub_mem_vectorSpan ℝ h0 h

lemma close_of_dist {u : x.toSwitch.P' → ℝ} (h : dist u x.u0 < Lemma45.eps x) : Lemma45.Close x u := fun p => by
  have h' := (dist_pi_lt_iff (Lemma45.eps_pos x)).mp h p
  rwa [Real.dist_eq] at h'

/-- The `α`–`β` shift that ties the two branches of `L`. -/
noncomputable def sA (z : x.toSwitch.P' → ℝ) : ℝ := ((z x.pb + x.lamB z) - (z x.pa + x.lamA z)) / 2

/-- The `γ`–`η` shift that ties the two branches of `U`. -/
noncomputable def sG (z : x.toSwitch.P' → ℝ) : ℝ := (z x.ph - z x.pg) / 2

/-- The tie-making shift of a point `z`: it moves only `α, β, γ, η`. -/
noncomputable def shift (z : x.toSwitch.P' → ℝ) : x.toSwitch.P' → ℝ :=
  sA x z • (Pi.single x.pa 1 - Pi.single x.pb 1) + sG x z • (Pi.single x.pg 1 - Pi.single x.ph 1)

lemma shift_continuous : Continuous fun z => z + shift x z := by
  have hA := (familyA x).cont
  have hB := (familyB x).cont
  have hsA : Continuous (sA x) := by unfold sA; fun_prop
  have hsG : Continuous (sG x) := by unfold sG; fun_prop
  exact continuous_id.add ((hsA.smul continuous_const).add (hsG.smul continuous_const))

lemma shift_u0 : shift x x.u0 = 0 := by
  have hA := (familyA x).at_u0
  have hB := (familyB x).at_u0
  simp [shift, sA, sG, hA, hB, Lemma45.u0_pa, Lemma45.u0_pb, Lemma45.u0_pg, Lemma45.u0_ph]

lemma shift_special (z : x.toSwitch.P' → ℝ) {p : x.toSwitch.P'} (hp : p ∉ x.special) : shift x z p = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := (Lemma45.not_special x).mp hp
  simp [shift, h1, h2, h3, h4]

lemma shift_values (z : x.toSwitch.P' → ℝ) :
    shift x z x.pa = sA x z ∧ shift x z x.pb = -sA x z ∧ shift x z x.pg = sG x z ∧ shift x z x.ph = -sG x z := by
  obtain ⟨hab, hag, hah, hbg, hbh, hgh⟩ := Lemma45.distinct x
  simp [shift, hab, hag, hah, hbg, hbh, hgh, hab.symm, hag.symm, hah.symm, hbg.symm, hbh.symm,
    hgh.symm]

lemma shift_mem {V : Submodule ℝ (x.toSwitch.P' → ℝ)} (ha : Pi.single x.pa (1 : ℝ) ∈ V)
    (hb : Pi.single x.pb (1 : ℝ) ∈ V) (hg : Pi.single x.pg (1 : ℝ) ∈ V) (hh : Pi.single x.ph (1 : ℝ) ∈ V)
    (z : x.toSwitch.P' → ℝ) : shift x z ∈ V :=
  V.add_mem (V.smul_mem _ (V.sub_mem ha hb)) (V.smul_mem _ (V.sub_mem hg hh))

/-- At the shifted point both branches of `L` tie, and both branches of `U` tie. -/
lemma tie {z : x.toSwitch.P' → ℝ} {Ka Kb : Finset x.toSwitch.P'} (hKa : Ka ∈ x.toSwitch.lowBranches)
    (haK : x.pa ∈ Ka) (hfa : x.toSwitch.chainSum (Ka.erase x.pa) z = x.lamA z)
    (hKb : Kb ∈ x.toSwitch.lowBranches) (hbK : x.pb ∈ Kb) (hfb : x.toSwitch.chainSum (Kb.erase x.pb) z = x.lamB z) :
    x.toSwitch.chainSum Ka (z + shift x z) = x.toSwitch.chainSum Kb (z + shift x z) ∧
      (z + shift x z) x.pg = (z + shift x z) x.ph := by
  obtain ⟨va, vb, vg, vh⟩ := shift_values x z
  have ea := Finset.add_sum_erase Ka (z + shift x z) haK
  have eb := Finset.add_sum_erase Kb (z + shift x z) hbK
  have fa := form_add x hKa (Or.inl rfl) haK (u := z) (d := shift x z) fun p hp => shift_special x z hp
  have fb := form_add x hKb (Or.inr rfl) hbK (u := z) (d := shift x z) fun p hp => shift_special x z hp
  unfold Switch.chainSum at fa fb hfa hfb ⊢
  rw [← ea, ← eb, fa, fb, hfa, hfb]
  simp only [Pi.add_apply, va, vb, vg, vh]
  unfold sA sG
  constructor <;> ring

lemma chainSum_single (K : Finset x.toSwitch.P') (p : x.toSwitch.P') :
    x.toSwitch.chainSum K (Pi.single p 1) = if p ∈ K then 1 else 0 := by
  unfold Switch.chainSum
  exact Finset.sum_pi_single' p 1 K

lemma ph_not_mem {K : Finset x.toSwitch.P'} (hK : K ∈ x.toSwitch.lowBranches) : x.ph ∉ K := fun h =>
  Lemma44.h'_notMem_I x ((mem_low x hK).1 h)

/-- From the local picture at `w` (a relative ball of `E` around `w`; `L = max(ℓ_{K_a}, ℓ_{K_b})` and
`U = min(γ, η)` on `N = E ∩ ball w r`; both pairs tied at `w`) the crossing hypotheses of Lemma 4.2 hold at `w`, with
`φ = ℓ_{K_a} − ℓ_{K_b}` and `ψ = η − γ`. -/
lemma crossing_of_local {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E)
    (hS : ∀ A, A ∈ x.toSwitch.topCells x.toSwitch.cellsS E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧
      AffineOn x.toSwitch.L A ∧ ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn x.toSwitch.L D → D = A)
    (hT : ∀ A, A ∈ x.toSwitch.topCells x.toSwitch.cellsT E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧
      AffineOn x.toSwitch.U A ∧ ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn x.toSwitch.U D → D = A)
    {w : x.toSwitch.P' → ℝ} {ρ r : ℝ} (hwA : w ∈ affineSpan ℝ E) (hρ : 0 < ρ)
    (hrel : ∀ y ∈ affineSpan ℝ E, dist y w < ρ → y ∈ E) (hr : 0 < r)
    {Ka Kb : Finset x.toSwitch.P'} (hKa : Ka ∈ x.toSwitch.lowBranches) (haK : x.pa ∈ Ka)
    (hKb : Kb ∈ x.toSwitch.lowBranches) (hbK : x.pb ∈ Kb)
    (hL : ∀ u ∈ E ∩ ball w r, x.toSwitch.L u = max (x.toSwitch.chainSum Ka u) (x.toSwitch.chainSum Kb u))
    (hU : ∀ u ∈ E ∩ ball w r, x.toSwitch.U u = min (u x.pg) (u x.ph))
    (htL : x.toSwitch.chainSum Ka w = x.toSwitch.chainSum Kb w) (htU : w x.pg = w x.ph) :
    CrossingAt x.toSwitch E w := by
  have hEc : Convex ℝ E := hE.2.convex (B_convex x)
  obtain ⟨hea, -, -, heh⟩ := singles_mem x hE0
  obtain ⟨-, hag, hah, -, -, hgh⟩ := Lemma45.distinct x
  obtain ⟨φ, hφ⟩ : ∃ φ : (x.toSwitch.P' → ℝ) →ₗ[ℝ] ℝ,
      ∀ u, φ u = x.toSwitch.chainSum Ka u - x.toSwitch.chainSum Kb u :=
    ⟨csL x Ka - csL x Kb, fun u => by simp [csL_apply]⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (x.toSwitch.P' → ℝ) →ₗ[ℝ] ℝ, ∀ u, ψ u = u x.ph - u x.pg :=
    ⟨crd x x.ph - crd x x.pg, fun u => by simp⟩
  have hφa : φ (Pi.single x.pa 1) = 1 := by
    rw [hφ, chainSum_single, chainSum_single, ite_eq_left haK, ite_eq_right fun h => not_both x hKb h hbK, sub_zero]
  have hφh : φ (Pi.single x.ph 1) = 0 := by
    rw [hφ, chainSum_single, chainSum_single, ite_eq_right (ph_not_mem x hKa), ite_eq_right (ph_not_mem x hKb), sub_zero]
  have hψa : ψ (Pi.single x.pa 1) = 0 := by simp [hψ, hah.symm, hag.symm]
  have hψh : ψ (Pi.single x.ph 1) = 1 := by simp [hψ, hgh]
  have hφw : φ w = 0 := by rw [hφ, htL, sub_self]
  have hψw : ψ w = 0 := by rw [hψ, htU, sub_self]
  obtain ⟨p₁, hp₁, hφp₁⟩ := exists_side_point hwA hρ hr hrel φ hea (by rw [hφa]; norm_num)
  obtain ⟨p₂, hp₂, hφp₂⟩ := exists_side_point hwA hρ hr hrel (-φ) (neg_mem hea) (by simp [hφa])
  obtain ⟨q₁, hq₁, hψq₁⟩ := exists_side_point hwA hρ hr hrel ψ heh (by rw [hψh]; norm_num)
  obtain ⟨q₂, hq₂, hψq₂⟩ := exists_side_point hwA hρ hr hrel (-ψ) (neg_mem heh) (by simp [hψh])
  have SS := two_cells x.toSwitch.L (· ∈ x.toSwitch.topCells x.toSwitch.cellsS E) hEc hS (csL x Ka) (csL x Kb) φ
    (fun u hu => by
      rw [hL u hu, csL_apply, max_eq_left_iff, hφw, hφ]; constructor <;> intro h <;> linarith)
    (fun u hu => by
      rw [hL u hu, csL_apply, max_eq_right_iff, hφw, hφ]; constructor <;> intro h <;> linarith)
    (convex_L_piece x hEc hKa) (convex_L_piece x hEc hKb) hp₁ hφp₁ hp₂ (by simpa using hφp₂) hea
    (by rw [hφa]; norm_num)
  have TT := two_cells x.toSwitch.U (· ∈ x.toSwitch.topCells x.toSwitch.cellsT E) hEc hT (crd x x.pg)
    (crd x x.ph) ψ
    (fun u hu => by
      rw [hU u hu, LinearMap.proj_apply, min_eq_left_iff, hψw, hψ]; constructor <;> intro h <;> linarith)
    (fun u hu => by
      rw [hU u hu, LinearMap.proj_apply, min_eq_right_iff, hψw, hψ]; constructor <;> intro h <;> linarith)
    (convex_U_piece x hEc (some_mem_up x (Or.inl rfl))) (convex_U_piece x hEc (some_mem_up x (Or.inr rfl)))
    hq₁ hψq₁ hq₂ (by simpa using hψq₂) heh (by rw [hψh]; norm_num)
  have hli : LinearIndependent ℝ ![φ.domRestrict (vectorSpan ℝ E), ψ.domRestrict (vectorSpan ℝ E)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := LinearMap.congr_fun hst ⟨_, hea⟩
    have h2 := LinearMap.congr_fun hst ⟨_, heh⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.domRestrict_apply, LinearMap.zero_apply,
      smul_eq_mul, hφa, hψa, hφh, hψh] at h1 h2
    constructor <;> linarith
  exact ⟨mem_intrinsicInterior_iff.mpr ⟨hwA, ρ, hρ, hrel⟩, E ∩ ball w r, hEc.inter (convex_ball w r),
    Set.inter_subset_left, inter_mem_nhdsWithin E (ball_mem_nhds w hr), _, _, _, _, φ, ψ, SS.1, SS.2.1, TT.1,
    TT.2.1, SS.2.2.1, TT.2.2.1, SS.2.2.2.1, SS.2.2.2.2, TT.2.2.2.1, TT.2.2.2.2, hli⟩

/-- **The local picture.**  Some `w` of the intrinsic interior of `E` (a relative ball of radius `ρ` lies in `E`), a
radius `r` and chains `K_a ∋ a`, `K_b ∋ b` have `L = max(ℓ_{K_a}, ℓ_{K_b})` and `U = min(γ, η)` on `E ∩ ball w r`,
with both pairs tied at `w`.  (`w` = a generic point `z` of `relint E` near `u₀`, shifted in `α, β, γ, η`.) -/
lemma exists_local {E : Set (x.toSwitch.P' → ℝ)} (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ (w : x.toSwitch.P' → ℝ) (ρ r : ℝ) (Ka Kb : Finset x.toSwitch.P'), w ∈ affineSpan ℝ E ∧ 0 < ρ ∧
      (∀ y ∈ affineSpan ℝ E, dist y w < ρ → y ∈ E) ∧ 0 < r ∧
      Ka ∈ x.toSwitch.lowBranches ∧ x.pa ∈ Ka ∧ Kb ∈ x.toSwitch.lowBranches ∧ x.pb ∈ Kb ∧
      (∀ u ∈ E ∩ ball w r, x.toSwitch.L u = max (x.toSwitch.chainSum Ka u) (x.toSwitch.chainSum Kb u)) ∧
      (∀ u ∈ E ∩ ball w r, x.toSwitch.U u = min (u x.pg) (u x.ph)) ∧
      x.toSwitch.chainSum Ka w = x.toSwitch.chainSum Kb w ∧ w x.pg = w x.ph := by
  have hEc : Convex ℝ E := hE.2.convex (B_convex x)
  have hu0E : x.u0 ∈ E := hE0 (Lemma45.mem_E0 x (fun p => by simp) (fun _ _ => rfl))
  obtain ⟨hea, heb, heg, heh⟩ := singles_mem x hE0
  have hε := Lemma45.eps_pos x
  -- `δ`: points within `δ` of `u₀` shift to points within `ε/2` of `u₀`
  obtain ⟨δ₁, hδ₁, hcont⟩ :=
    Metric.continuousAt_iff.mp ((shift_continuous x).continuousAt (x := x.u0)) (Lemma45.eps x / 2) (half_pos hε)
  simp only [shift_u0, add_zero] at hcont
  obtain ⟨δ, hδ, hδ₁', hδε⟩ : ∃ δ, 0 < δ ∧ δ ≤ δ₁ ∧ δ ≤ Lemma45.eps x / 2 :=
    ⟨min δ₁ (Lemma45.eps x / 2), lt_min hδ₁ (half_pos hε), min_le_left _ _, min_le_right _ _⟩
  -- the generic point `z`
  obtain ⟨z₀, hz₀, hz₀d⟩ := exists_relint_near hEc hu0E hδ
  obtain ⟨z, ⟨hzI, hzd⟩, hgen⟩ :=
    exists_generic x {z | z ∈ intrinsicInterior ℝ E ∧ dist z x.u0 < δ} ⟨z₀, hz₀, hz₀d⟩
  obtain ⟨hzA, εz, hεz, hrelz⟩ := mem_intrinsicInterior_iff.mp hzI
  obtain ⟨rz, hrz, hgen'⟩ := Metric.eventually_nhds_iff.mp hgen
  obtain ⟨Ka, hKa, haK, hfa⟩ := (familyA x).attain z
  obtain ⟨Kb, hKb, hbK, hfb⟩ := (familyB x).attain z
  obtain ⟨r₁, hr₁, hr₁z, hr₁ε, hr₁δ⟩ : ∃ r₁, 0 < r₁ ∧ r₁ ≤ rz ∧ r₁ ≤ εz / 2 ∧ r₁ ≤ δ - dist z x.u0 :=
    ⟨min rz (min (εz / 2) (δ - dist z x.u0)), lt_min hrz (lt_min (half_pos hεz) (by linarith)),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  -- near `z`, within `E`, `λ_a` and `λ_b` are the single forms of `K_a` and `K_b`
  have hloc : ∀ u ∈ E, dist u z < r₁ → x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u ∧
      x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u := by
    intro u huE hu
    have huI : u ∈ intrinsicInterior ℝ E := by
      refine mem_intrinsicInterior_iff.mpr
        ⟨subset_affineSpan ℝ E huE, εz / 2, half_pos hεz, fun y hy hyd => hrelz y hy ?_⟩
      linarith [dist_triangle y u z]
    have huδ : dist u x.u0 < δ := by linarith [dist_triangle u z x.u0]
    obtain ⟨hA, hB⟩ := hgen' (lt_of_lt_of_le hu hr₁z) ⟨huI, huδ⟩
    have hKaM : Ka ∈ maxSet x x.lamA x.pa u := by rw [hA]; exact (mem_maxSet x).mpr ⟨hKa, haK, hfa⟩
    have hKbM : Kb ∈ maxSet x x.lamB x.pb u := by rw [hB]; exact (mem_maxSet x).mpr ⟨hKb, hbK, hfb⟩
    exact ⟨((mem_maxSet x).mp hKaM).2.2.symm, ((mem_maxSet x).mp hKbM).2.2.symm⟩
  -- the shift `d` and the crossing point `w = z + d`
  obtain ⟨d, hd⟩ : ∃ d, d = shift x z := ⟨_, rfl⟩
  have hdS : ∀ p, p ∉ x.special → d p = 0 := fun p hp => by rw [hd]; exact shift_special x z hp
  have hdV : d ∈ vectorSpan ℝ E := by rw [hd]; exact shift_mem x hea heb heg heh z
  have hwd : dist (z + d) x.u0 < Lemma45.eps x / 2 := by rw [hd]; exact hcont (lt_of_lt_of_le hzd hδ₁')
  have hdist : ∀ y, dist (y - d) z = dist y (z + d) := fun y => by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    abel
  have hzeta : ∀ y, x.zeta (y - d) = x.zeta y := fun y => funext fun q => by
    simp [XSwitch.zeta, hdS q.1 q.2]
  have hclose : ∀ y, dist y (z + d) < Lemma45.eps x / 2 → Lemma45.Close x y ∧ Lemma45.Close x (y - d) :=
    fun y hy => ⟨close_of_dist x (by linarith [dist_triangle y (z + d) x.u0]),
      close_of_dist x (by linarith [dist_triangle (y - d) z x.u0, hdist y])⟩
  have hsub : ∀ y ∈ affineSpan ℝ E, y - d ∈ affineSpan ℝ E := fun y hy => by
    rw [sub_eq_add_neg, add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (by rw [direction_affineSpan]; exact neg_mem hdV) hy
  refine ⟨z + d, min εz (Lemma45.eps x / 2), min r₁ (Lemma45.eps x / 2), Ka, Kb, ?_, lt_min hεz (half_pos hε),
    ?_, lt_min hr₁ (half_pos hε), hKa, haK, hKb, hbK, ?_, ?_, ?_⟩
  · rw [add_comm]
    exact AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) hzA
  · intro y hy hyd
    have hc := hclose y (lt_of_lt_of_le hyd (min_le_right _ _))
    exact Lemma45.face_transfer x hE hE0 hc.2 hc.1 (hzeta y)
      (hrelz _ (hsub y hy) (by rw [hdist]; exact lt_of_lt_of_le hyd (min_le_left _ _)))
  · intro u hu
    obtain ⟨hcu, hcud⟩ := hclose u (lt_of_lt_of_le (mem_ball.mp hu.2) (min_le_right _ _))
    have hudE : u - d ∈ E := Lemma45.face_transfer x hE hE0 hcu hcud (hzeta u).symm hu.1
    obtain ⟨hla, hlb⟩ := hloc (u - d) hudE
      (by rw [hdist]; exact lt_of_lt_of_le (mem_ball.mp hu.2) (min_le_left _ _))
    have ha : x.lamA u = x.toSwitch.chainSum (Ka.erase x.pa) u := by
      have h1 := (familyA x).add (u - d) d hdS
      have h2 := form_add x hKa (Or.inl rfl) haK (u := u - d) hdS
      rw [sub_add_cancel] at h1 h2
      rw [h1, hla, h2]
    have hb : x.lamB u = x.toSwitch.chainSum (Kb.erase x.pb) u := by
      have h1 := (familyB x).add (u - d) d hdS
      have h2 := form_add x hKb (Or.inr rfl) hbK (u := u - d) hdS
      rw [sub_add_cancel] at h1 h2
      rw [h1, hlb, h2]
    rw [Lemma45.L_eq x hcu, ha, hb]
    unfold Switch.chainSum
    rw [Finset.add_sum_erase Ka u haK, Finset.add_sum_erase Kb u hbK]
  · intro u hu
    exact Lemma45.U_eq x (hclose u (lt_of_lt_of_le (mem_ball.mp hu.2) (min_le_right _ _))).1
  · rw [hd]
    exact tie x hKa haK hfa hKb hbK hfb

end Concrete

end Lemma46

/-- **Lemma 4.6** (paper lines 792–795), from **Lemma 3.6** (hypothesis `h36`): every face `E ⊇ E₀` of `B` has a
point where the hypotheses of Lemma 4.2 hold. -/
theorem lemma_4_6_of_3_6 {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (h36 : ∀ (E : Set (x.toSwitch.P' → ℝ)), IsFace x.toSwitch.B E → ∀ A,
      (A ∈ x.toSwitch.topCells x.toSwitch.cellsS E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧
        AffineOn x.toSwitch.L A ∧ ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn x.toSwitch.L D → D = A) ∧
      (A ∈ x.toSwitch.topCells x.toSwitch.cellsT E ↔ A ⊆ E ∧ Convex ℝ A ∧ adim A = adim E ∧
        AffineOn x.toSwitch.U A ∧ ∀ D, A ⊆ D → D ⊆ E → Convex ℝ D → AffineOn x.toSwitch.U D → D = A))
    (E : Set (x.toSwitch.P' → ℝ)) (hE : IsFace x.toSwitch.B E) (hE0 : x.E0 ⊆ E) :
    ∃ w, CrossingAt x.toSwitch E w := by
  obtain ⟨w, ρ, r, Ka, Kb, hwA, hρ, hrel, hr, hKa, haK, hKb, hbK, hL, hU, htL, htU⟩ :=
    Lemma46.exists_local x hE hE0
  exact ⟨w, Lemma46.crossing_of_local x hE hE0 (fun A => (h36 E hE A).1) (fun A => (h36 E hE A).2) hwA hρ hrel
    hr hKa haK hKb hbK hL hU htL htU⟩

end HibiLi.Proofs
