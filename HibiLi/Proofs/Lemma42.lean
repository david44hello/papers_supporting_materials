/-
HibiLi/Proofs/Lemma42.lean — paper Lemma 4.2 (one crossing gives δ_E ≥ t^{e−2}(1+t)^2), from transversality and Lemma 3.5.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Polytope.TopCells
import HibiLi.Proofs.SwitchFacts
import HibiLi.Proofs.FacePoly

open Set Filter
open scoped Topology

namespace HibiLi.Proofs.L42

/-! ## Part 1: linear algebra and local geometry in a finite-dimensional normed space -/

section Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_small {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * M < ε := by
  refine ⟨ε / (ε + M), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith

theorem norm_smul_of_pos {t : ℝ} (ht : 0 < t) (v : V) : ‖t • v‖ = t * ‖v‖ := by
  rw [norm_smul, Real.norm_of_nonneg ht.le]

/-- A neighbourhood of a relative-interior point `w` of `E`, taken within `E`, contains a small ball of `w + dir E`. -/
theorem exists_ball {E N : Set V} {w : V} (hw : w ∈ intrinsicInterior ℝ E) (hN : N ∈ 𝓝[E] w) :
    ∃ ε > 0, ∀ v ∈ vectorSpan ℝ E, ‖v‖ < ε → w + v ∈ N := by
  obtain ⟨y, hy, rfl⟩ := mem_intrinsicInterior.mp hw
  obtain ⟨t, ht, hwt, htN⟩ := mem_nhdsWithin.mp hN
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp ht _ hwt
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun v hv hnorm => htN ⟨hball₁ ?_, ?_⟩⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hnorm (min_le_left _ _)
  · have hmem : (y : V) + v ∈ affineSpan ℝ E := by
      have := AffineSubspace.vadd_mem_of_mem_direction (by rwa [direction_affineSpan]) y.2
      rwa [vadd_eq_add, add_comm] at this
    have hin : (⟨_, hmem⟩ : affineSpan ℝ E) ∈ Metric.ball y ε₂ := by
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hnorm (min_le_right _ _)
    exact hball₂ hin

/-- If `X` contains a small ball of `w + W` and `dir X ≤ W`, then `w` is in the relative interior of `X`. -/
theorem mem_intrinsicInterior_of_ball {X : Set V} {W : Submodule ℝ V} {w : V} {ε : ℝ} (hε : 0 < ε)
    (hwX : w ∈ X) (hspan : vectorSpan ℝ X ≤ W) (hball : ∀ v ∈ W, ‖v‖ < ε → w + v ∈ X) :
    w ∈ intrinsicInterior ℝ X := by
  refine mem_intrinsicInterior.mpr ⟨⟨w, subset_affineSpan ℝ X hwX⟩, ?_, rfl⟩
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨ε, hε, fun z hz => ?_⟩
  have hdir : (z : V) - w ∈ W := hspan (by
    rw [← direction_affineSpan, ← vsub_eq_sub]
    exact AffineSubspace.vsub_mem_direction z.2 (subset_affineSpan ℝ X hwX))
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] at hz
  have := hball _ hdir hz
  rwa [add_sub_cancel] at this

/-- Spanning from a cone: if `X` contains `w + v` for all small `v` of a cone `C` that generates `W`
(every `z ∈ W` is a difference of two members of `C`), then `W ≤ dir X`. -/
theorem le_vectorSpan_of_cone {X : Set V} {W : Submodule ℝ V} {C : V → Prop} {w : V} {ε : ℝ} (hε : 0 < ε)
    (hcone : ∀ v, C v → ∀ c : ℝ, 0 < c → C (c • v)) (hgen : ∀ z ∈ W, ∃ a, C a ∧ C (z + a))
    (hball : ∀ v, C v → ‖v‖ < ε → w + v ∈ X) : W ≤ vectorSpan ℝ X := by
  intro z hz
  obtain ⟨a, ha, hza⟩ := hgen z hz
  obtain ⟨c, hc, -, hcM⟩ := exists_small hε (add_nonneg (norm_nonneg a) (norm_nonneg (z + a)))
  have h₁ := hball _ (hcone _ hza c hc) (by rw [norm_smul_of_pos hc]; nlinarith [norm_nonneg a])
  have h₂ := hball _ (hcone _ ha c hc) (by rw [norm_smul_of_pos hc]; nlinarith [norm_nonneg (z + a)])
  have hsub := vsub_mem_vectorSpan ℝ h₁ h₂
  have heq : (w + c • (z + a)) -ᵥ (w + c • a) = c • z := by
    rw [vsub_eq_sub, smul_add]; abel
  rw [heq] at hsub
  have := Submodule.smul_mem _ c⁻¹ hsub
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this

/-- A set on which a linear functional is constant has its direction inside the kernel. -/
theorem vectorSpan_le_ker {X : Set V} (f : V →ₗ[ℝ] ℝ) (c : ℝ) (hX : ∀ u ∈ X, f u = c) :
    vectorSpan ℝ X ≤ LinearMap.ker f := by
  rw [vectorSpan_def, Submodule.span_le]
  rintro _ ⟨p, hp, q, hq, rfl⟩
  simp [vsub_eq_sub, hX p hp, hX q hq]

/-- Local to global: a functional constant near `w` on a convex set `X ⊆ E` through `w` is constant on `X`. -/
theorem eq_of_local {X E N : Set V} {w : V} {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ v ∈ vectorSpan ℝ E, ‖v‖ < ε → w + v ∈ N) (hX : Convex ℝ X) (hXE : X ⊆ E) (hwX : w ∈ X)
    (f : V →ₗ[ℝ] ℝ) (hloc : ∀ u ∈ X ∩ N, f u = f w) : ∀ u ∈ X, f u = f w := by
  intro u hu
  obtain ⟨t, ht, ht1, htM⟩ := exists_small hε (norm_nonneg (u - w))
  have hD : t • (u - w) ∈ vectorSpan ℝ E :=
    Submodule.smul_mem _ t (by rw [← vsub_eq_sub]; exact vsub_mem_vectorSpan ℝ (hXE hu) (hXE hwX))
  have hN := hball _ hD (by rwa [norm_smul_of_pos ht])
  have hXp := hX.add_smul_sub_mem hwX hu ⟨ht.le, ht1⟩
  have := hloc _ ⟨hXp, hN⟩
  rw [map_add, map_smul, map_sub, smul_eq_mul] at this
  have h0 : t * (f u - f w) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h ht.ne'
  · linarith

/-- Rank–nullity for a functional (or pair) restricted to a subspace `D` on which it is onto. -/
theorem finrank_inf_ker_add [FiniteDimensional ℝ V] {F : Type*} [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (D : Submodule ℝ V) (f : V →ₗ[ℝ] F) (hsurj : ∀ y, ∃ x ∈ D, f x = y) :
    Module.finrank ℝ (D ⊓ LinearMap.ker f : Submodule ℝ V) + Module.finrank ℝ F = Module.finrank ℝ D := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict D)
  have hrange : LinearMap.range (f.domRestrict D) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    obtain ⟨x, hx, rfl⟩ := hsurj y
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange, finrank_top, LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype] at hrn
  omega

/-- Independence of `φ|_D, ψ|_D` makes `(φ, ψ) : D → ℝ²` onto. -/
theorem surj_of_linearIndependent (D : Submodule ℝ V) (φ ψ : V →ₗ[ℝ] ℝ)
    (h : LinearIndependent ℝ ![φ.domRestrict D, ψ.domRestrict D]) : ∀ y, ∃ x ∈ D, (φ.prod ψ) x = y := by
  suffices hs : Function.Surjective ((φ.prod ψ).domRestrict D) by
    intro y
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, x.2, hx⟩
  by_contra hns
  rw [← LinearMap.range_eq_top, ← Ne, ← lt_top_iff_ne_top] at hns
  obtain ⟨f, hf0, hle⟩ := (LinearMap.range ((φ.prod ψ).domRestrict D)).exists_le_ker_of_lt_top hns
  have hdecomp : ∀ a b : ℝ, f (a, b) = a * f (1, 0) + b * f (0, 1) := by
    intro a b
    have : ((a, b) : ℝ × ℝ) = a • (1, 0) + b • (0, 1) := by ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hcomb : f (1, 0) • φ.domRestrict D + f (0, 1) • ψ.domRestrict D = 0 := by
    ext x
    have hx : f (φ x, ψ x) = 0 := hle ⟨x, rfl⟩
    rw [hdecomp] at hx
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.domRestrict_apply, smul_eq_mul,
      LinearMap.zero_apply]
    linarith
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp h _ _ hcomb
  exact hf0 (LinearMap.ext fun ⟨a, b⟩ => by rw [hdecomp, h1, h2]; simp)

end Geometry

/-! ## Part 2: the local picture at a crossing point -/

section Local

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A small ball of `w + dir E` lies in `N`. -/
structure Local (E N : Set V) (w : V) (ε : ℝ) : Prop where
  pos : 0 < ε
  ball : ∀ v ∈ vectorSpan ℝ E, ‖v‖ < ε → w + v ∈ N

namespace Local

variable {E N A A₁ A₂ B B₁ B₂ : Set V} {w : V} {ε : ℝ} {φ ψ : V →ₗ[ℝ] ℝ}

theorem half_neg (hA : A ∩ N = {u ∈ N | φ u ≤ φ w}) : A ∩ N = {u ∈ N | (-φ) w ≤ (-φ) u} := by
  rw [hA]; ext u; simp

theorem mem_of_half (hL : Local E N w ε) (hA : A ∩ N = {u ∈ N | φ w ≤ φ u}) {v : V}
    (hv : v ∈ vectorSpan ℝ E) (hvε : ‖v‖ < ε) (hφ : 0 ≤ φ v) : w + v ∈ A := by
  have h : w + v ∈ A ∩ N := by
    rw [hA]
    exact ⟨hL.ball v hv hvε, by rw [map_add]; linarith⟩
  exact h.1

theorem le_of_half (hA : A ∩ N = {u ∈ N | φ w ≤ φ u}) {u : V} (hu : u ∈ A) (huN : u ∈ N) : φ w ≤ φ u := by
  have h : u ∈ A ∩ N := ⟨hu, huN⟩
  rw [hA] at h
  exact h.2

theorem w_mem (hL : Local E N w ε) (hA : A ∩ N = {u ∈ N | φ w ≤ φ u}) : w ∈ A := by
  simpa using hL.mem_of_half hA (Submodule.zero_mem _) (by simpa using hL.pos) (by simp)

theorem w_mem_N (hL : Local E N w ε) : w ∈ N := by
  simpa using hL.ball 0 (Submodule.zero_mem _) (by simpa using hL.pos)

/-- A point of `N` strictly on the positive side of `φ`. -/
theorem exists_pos (hL : Local E N w ε) (hA : A ∩ N = {u ∈ N | φ w ≤ φ u}) {v : V}
    (hv : v ∈ vectorSpan ℝ E) (hφv : 0 < φ v) : ∃ u ∈ A, u ∈ N ∧ φ w < φ u := by
  obtain ⟨t, ht, -, htM⟩ := exists_small hL.pos (norm_nonneg v)
  have hD : t • v ∈ vectorSpan ℝ E := Submodule.smul_mem _ t hv
  have hsmall : ‖t • v‖ < ε := by rwa [norm_smul_of_pos ht]
  refine ⟨w + t • v, hL.mem_of_half hA hD hsmall (by rw [map_smul, smul_eq_mul]; positivity),
    hL.ball _ hD hsmall, ?_⟩
  rw [map_add, map_smul, smul_eq_mul]
  nlinarith

/-- The two sides of a hyperplane are different cells. -/
theorem ne_of_halves (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) {v : V} (hv : v ∈ vectorSpan ℝ E) (hφv : 0 < φ v) : A₁ ≠ A₂ := by
  rintro rfl
  obtain ⟨u, hu, huN, hlt⟩ := hL.exists_pos hA₁ hv hφv
  have := le_of_half (half_neg hA₂) hu huN
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  linarith

/-- A ball of `w + (dir E ∩ ker φ)` lies in the wall `A₁ ∩ A₂`. -/
theorem wall_ball (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) :
    ∀ v ∈ vectorSpan ℝ E ⊓ LinearMap.ker φ, ‖v‖ < ε → w + v ∈ A₁ ∩ A₂ := by
  intro v hv hvε
  have hφ : φ v = 0 := LinearMap.mem_ker.mp hv.2
  exact ⟨hL.mem_of_half hA₁ hv.1 hvε hφ.ge, hL.mem_of_half (half_neg hA₂) hv.1 hvε (by simp [hφ])⟩

/-- If a ball of `w + W` lies in `X` and `dir X ≤ W`, then `dir X = W`. -/
theorem span_eq_of_ball (hL : Local E N w ε) {X : Set V} {W : Submodule ℝ V}
    (hball : ∀ v ∈ W, ‖v‖ < ε → w + v ∈ X) (hle : vectorSpan ℝ X ≤ W) : vectorSpan ℝ X = W :=
  le_antisymm hle (le_vectorSpan_of_cone hL.pos (C := (· ∈ W)) (fun _ hv c _ => Submodule.smul_mem _ c hv)
    (fun z hz => ⟨0, Submodule.zero_mem _, by simpa using hz⟩) hball)

/-- The wall `A₁ ∩ A₂` lies in the hyperplane `φ = φ w`. -/
theorem wall_const (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hconv : Convex ℝ (A₁ ∩ A₂)) (hsub : A₁ ∩ A₂ ⊆ E) :
    ∀ u ∈ A₁ ∩ A₂, φ u = φ w := by
  refine eq_of_local hL.pos hL.ball hconv hsub ⟨hL.w_mem hA₁, hL.w_mem (half_neg hA₂)⟩ φ ?_
  rintro u ⟨⟨hu₁, hu₂⟩, huN⟩
  have h₁ := le_of_half hA₁ hu₁ huN
  have h₂ := le_of_half (half_neg hA₂) hu₂ huN
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at h₂
  linarith

/-- The direction of the wall is `dir E ∩ ker φ`. -/
theorem wall_span (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hconv : Convex ℝ (A₁ ∩ A₂)) (hsub : A₁ ∩ A₂ ⊆ E) :
    vectorSpan ℝ (A₁ ∩ A₂) = vectorSpan ℝ E ⊓ LinearMap.ker φ :=
  hL.span_eq_of_ball (hL.wall_ball hA₁ hA₂)
    (le_inf (vectorSpan_mono ℝ hsub) (vectorSpan_le_ker φ (φ w) (hL.wall_const hA₁ hA₂ hconv hsub)))

/-- The crossing `R_w` of two walls: its direction is `dir E ∩ ker φ ∩ ker ψ`, and it contains a ball of it. -/
theorem cross_ball (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hB₁ : B₁ ∩ N = {u ∈ N | ψ w ≤ ψ u})
    (hB₂ : B₂ ∩ N = {u ∈ N | ψ u ≤ ψ w}) :
    ∀ v ∈ vectorSpan ℝ E ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ, ‖v‖ < ε → w + v ∈ A₁ ∩ A₂ ∩ (B₁ ∩ B₂) :=
  fun v hv hvε => ⟨hL.wall_ball hA₁ hA₂ v hv.1 hvε, hL.wall_ball hB₁ hB₂ v ⟨hv.1.1, hv.2⟩ hvε⟩

theorem cross_span (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hB₁ : B₁ ∩ N = {u ∈ N | ψ w ≤ ψ u})
    (hB₂ : B₂ ∩ N = {u ∈ N | ψ u ≤ ψ w}) (hconvA : Convex ℝ (A₁ ∩ A₂)) (hsubA : A₁ ∩ A₂ ⊆ E)
    (hconvB : Convex ℝ (B₁ ∩ B₂)) (hsubB : B₁ ∩ B₂ ⊆ E) :
    vectorSpan ℝ (A₁ ∩ A₂ ∩ (B₁ ∩ B₂)) = vectorSpan ℝ E ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ := by
  refine hL.span_eq_of_ball (hL.cross_ball hA₁ hA₂ hB₁ hB₂) ?_
  have h₁ := (vectorSpan_mono ℝ (inter_subset_left : A₁ ∩ A₂ ∩ (B₁ ∩ B₂) ⊆ _)).trans
    (hL.wall_span hA₁ hA₂ hconvA hsubA).le
  have h₂ := (vectorSpan_mono ℝ (inter_subset_right : A₁ ∩ A₂ ∩ (B₁ ∩ B₂) ⊆ _)).trans
    (hL.wall_span hB₁ hB₂ hconvB hsubB).le
  exact le_inf h₁ (h₂.trans inf_le_right)

/-- Half of a wall: `A₁ ∩ A₂ ∩ B` (with `B` on the positive side of `ψ`) spans `dir E ∩ ker φ`. -/
theorem halfwall_span (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hB : B ∩ N = {u ∈ N | ψ w ≤ ψ u}) {v₂ : V}
    (hv₂ : v₂ ∈ vectorSpan ℝ E) (hφ₂ : φ v₂ = 0) (hψ₂ : ψ v₂ = 1) :
    vectorSpan ℝ E ⊓ LinearMap.ker φ ≤ vectorSpan ℝ (A₁ ∩ A₂ ∩ B) := by
  refine le_vectorSpan_of_cone hL.pos (C := fun v => v ∈ vectorSpan ℝ E ⊓ LinearMap.ker φ ∧ 0 ≤ ψ v)
    (fun v hv c hc => ⟨Submodule.smul_mem _ c hv.1, by rw [map_smul, smul_eq_mul]; nlinarith [hv.2]⟩)
    (fun z hz => ?_) (fun v hv hvε => ⟨hL.wall_ball hA₁ hA₂ v hv.1 hvε, hL.mem_of_half hB hv.1.1 hvε hv.2⟩)
  have ha : |ψ z| • v₂ ∈ vectorSpan ℝ E ⊓ LinearMap.ker φ :=
    Submodule.smul_mem _ _ ⟨hv₂, LinearMap.mem_ker.mpr hφ₂⟩
  refine ⟨|ψ z| • v₂, ⟨ha, by simp [hψ₂]⟩, Submodule.add_mem _ hz ha, ?_⟩
  rw [map_add, map_smul, hψ₂, smul_eq_mul, mul_one]
  linarith [neg_abs_le (ψ z)]

/-- A point of the half wall strictly on the positive side of `ψ`. -/
theorem halfwall_point (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hB : B ∩ N = {u ∈ N | ψ w ≤ ψ u}) {v₂ : V}
    (hv₂ : v₂ ∈ vectorSpan ℝ E) (hφ₂ : φ v₂ = 0) (hψ₂ : ψ v₂ = 1) :
    ∃ u ∈ A₁ ∩ A₂ ∩ B, u ∈ N ∧ ψ w < ψ u := by
  obtain ⟨t, ht, -, htM⟩ := exists_small hL.pos (norm_nonneg v₂)
  have hW : t • v₂ ∈ vectorSpan ℝ E ⊓ LinearMap.ker φ :=
    Submodule.smul_mem _ t ⟨hv₂, LinearMap.mem_ker.mpr hφ₂⟩
  have hsmall : ‖t • v₂‖ < ε := by rwa [norm_smul_of_pos ht]
  refine ⟨w + t • v₂, ⟨hL.wall_ball hA₁ hA₂ _ hW hsmall, hL.mem_of_half hB hW.1 hsmall ?_⟩,
    hL.ball _ hW.1 hsmall, ?_⟩
  · rw [map_smul, hψ₂, smul_eq_mul]; linarith
  · rw [map_add, map_smul, hψ₂, smul_eq_mul]; linarith

/-- The two halves of a wall are different. -/
theorem halfwall_ne (hL : Local E N w ε) (hA₁ : A₁ ∩ N = {u ∈ N | φ w ≤ φ u})
    (hA₂ : A₂ ∩ N = {u ∈ N | φ u ≤ φ w}) (hB₁ : B₁ ∩ N = {u ∈ N | ψ w ≤ ψ u})
    (hB₂ : B₂ ∩ N = {u ∈ N | ψ u ≤ ψ w}) {v₂ : V}
    (hv₂ : v₂ ∈ vectorSpan ℝ E) (hφ₂ : φ v₂ = 0) (hψ₂ : ψ v₂ = 1) : A₁ ∩ A₂ ∩ B₁ ≠ A₁ ∩ A₂ ∩ B₂ := by
  intro heq
  obtain ⟨u, hu, huN, hlt⟩ := hL.halfwall_point hA₁ hA₂ hB₁ hv₂ hφ₂ hψ₂
  rw [heq] at hu
  have := le_of_half (half_neg hB₂) hu.2 huN
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  linarith

/-- A quadrant `A ∩ B` (positive sides of `φ` and `ψ`) spans `dir E`. -/
theorem quadrant_span (hL : Local E N w ε) (hA : A ∩ N = {u ∈ N | φ w ≤ φ u})
    (hB : B ∩ N = {u ∈ N | ψ w ≤ ψ u}) {v₁ v₂ : V} (hv₁ : v₁ ∈ vectorSpan ℝ E) (hv₂ : v₂ ∈ vectorSpan ℝ E)
    (h11 : φ v₁ = 1) (h12 : ψ v₁ = 0) (h21 : φ v₂ = 0) (h22 : ψ v₂ = 1) :
    vectorSpan ℝ E ≤ vectorSpan ℝ (A ∩ B) := by
  refine le_vectorSpan_of_cone hL.pos (C := fun v => v ∈ vectorSpan ℝ E ∧ 0 ≤ φ v ∧ 0 ≤ ψ v)
    (fun v hv c hc => ⟨Submodule.smul_mem _ c hv.1, by rw [map_smul, smul_eq_mul]; nlinarith [hv.2.1],
      by rw [map_smul, smul_eq_mul]; nlinarith [hv.2.2]⟩)
    (fun z hz => ?_) (fun v hv hvε => ⟨hL.mem_of_half hA hv.1 hvε hv.2.1, hL.mem_of_half hB hv.1 hvε hv.2.2⟩)
  have ha : |φ z| • v₁ + |ψ z| • v₂ ∈ vectorSpan ℝ E :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ hv₁) (Submodule.smul_mem _ _ hv₂)
  refine ⟨|φ z| • v₁ + |ψ z| • v₂, ⟨ha, by simp [h11, h21], by simp [h12, h22]⟩,
    Submodule.add_mem _ hz ha, ?_, ?_⟩
  · simp only [map_add, map_smul, h11, h21, smul_eq_mul, mul_one, mul_zero, add_zero]
    linarith [neg_abs_le (φ z)]
  · simp only [map_add, map_smul, h12, h22, smul_eq_mul, mul_one, mul_zero, zero_add]
    linarith [neg_abs_le (ψ z)]

end Local

end Local

/-! ## Part 3: affinity domains of a maximum of affine functions (covers `L`, and `U` via `-U`) -/

section Family

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {ι : Type*}

/-- `dom i = {u ∈ B : F u = aff i u}`, with `aff i ≤ F` on `B`, and every domain convex. -/
structure MaxFamily (B : Set V) (dom : ι → Set V) (br : Finset ι) (aff : ι → V →ᵃ[ℝ] ℝ) (F : V → ℝ) :
    Prop where
  mem_iff : ∀ i u, u ∈ dom i ↔ u ∈ B ∧ F u = aff i u
  le : ∀ i ∈ br, ∀ u ∈ B, aff i u ≤ F u
  convex : ∀ i ∈ br, Convex ℝ (dom i)

/-- The cells of the subdivision: nonempty faces of the full-dimensional domains. -/
def famCells (dom : ι → Set V) (br : Finset ι) (n : ℕ) : Set (Set V) :=
  {C | ∃ i ∈ br, adim (dom i) = n ∧ IsFace (dom i) C}

/-- Where an affine function `≤ 0` on `A` vanishes is a face of `A` (if nonempty). -/
theorem isFace_of_affine_nonpos {A : Set V} (f : V →ᵃ[ℝ] ℝ) (hle : ∀ u ∈ A, f u ≤ 0)
    (hne : {u ∈ A | f u = 0}.Nonempty) : IsFace A {u ∈ A | f u = 0} := by
  refine ⟨hne, fun _ => ⟨LinearMap.toContinuousLinearMap f.linear, ?_⟩⟩
  have hlin : ∀ x y, f.linear y - f.linear x = f y - f x := by
    intro x y
    rw [← map_sub, ← vsub_eq_sub, AffineMap.linear_apply_vsub, vsub_eq_sub]
  ext x
  simp only [mem_ofPred_eq, LinearMap.coe_toContinuousLinearMap']
  constructor
  · rintro ⟨hxA, hx0⟩
    refine ⟨hxA, fun y hy => ?_⟩
    have h1 := hlin x y
    have h2 := hle y hy
    linarith
  · rintro ⟨hxA, hmax⟩
    obtain ⟨z, hzA, hz0⟩ := hne
    have h1 := hmax z hzA
    have h2 := hlin x z
    exact ⟨hxA, le_antisymm (hle x hxA) (by linarith)⟩

namespace MaxFamily

variable {B : Set V} {dom : ι → Set V} {br : Finset ι} {aff : ι → V →ᵃ[ℝ] ℝ} {F : V → ℝ} {n : ℕ}

/-- Two domains meet in a face of each. -/
theorem inter_isFace (h : MaxFamily B dom br aff F) {i j : ι} (hj : j ∈ br)
    (hne : (dom i ∩ dom j).Nonempty) : IsFace (dom i) (dom i ∩ dom j) := by
  have heq : dom i ∩ dom j = {u ∈ dom i | (aff j - aff i) u = 0} := by
    ext u
    simp only [mem_inter_iff, mem_ofPred_eq, AffineMap.coe_sub, Pi.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨hui, huj⟩
      exact ⟨hui, ((h.mem_iff j u).1 huj).2.symm.trans ((h.mem_iff i u).1 hui).2⟩
    · rintro ⟨hui, heq⟩
      have hi' := (h.mem_iff i u).1 hui
      exact ⟨hui, (h.mem_iff j u).2 ⟨hi'.1, hi'.2.trans heq.symm⟩⟩
  rw [heq]
  refine isFace_of_affine_nonpos _ (fun u hu => ?_) (by rw [← heq]; exact hne)
  have hi' := (h.mem_iff i u).1 hu
  have := h.le j hj u hi'.1
  simp only [AffineMap.coe_sub, Pi.sub_apply]
  linarith [hi'.2]

/-- A full-dimensional piece `C ∩ E` of a cell is a whole domain piece `dom i ∩ E`. -/
theorem top_eq {C E : Set V} (hC : C ∈ famCells dom br n) (hne : (C ∩ E).Nonempty)
    (hdim : adim (C ∩ E) = adim E) : ∃ i ∈ br, adim (dom i) = n ∧ C ∩ E = dom i ∩ E := by
  obtain ⟨i, hi, hn, hface⟩ := hC
  refine ⟨i, hi, hn, ?_⟩
  have hset : (dom i ∩ E) ∩ C = C ∩ E := by
    ext u
    constructor
    · rintro ⟨⟨_, huE⟩, huC⟩
      exact ⟨huC, huE⟩
    · rintro ⟨huC, huE⟩
      exact ⟨⟨hface.subset huC, huE⟩, huC⟩
  have hface' := hface.inter_subset (inter_subset_left : dom i ∩ E ⊆ dom i) (by rw [hset]; exact hne)
  rw [hset] at hface'
  have hle1 : adim (dom i ∩ E) ≤ adim E := Submodule.finrank_mono (vectorSpan_mono ℝ inter_subset_right)
  have hle2 : adim (C ∩ E) ≤ adim (dom i ∩ E) := Submodule.finrank_mono (vectorSpan_mono ℝ hface'.subset)
  exact hface'.eq_of_adim_eq (by omega)

/-- Two domain pieces meeting in full dimension `e` coincide. -/
theorem eq_of_inter (h : MaxFamily B dom br aff F) {i j : ι} {E : Set V}
    (hne : (dom i ∩ E ∩ (dom j ∩ E)).Nonempty) (hdim : adim (dom i ∩ E ∩ (dom j ∩ E)) = adim E) :
    dom i ∩ E = dom j ∩ E := by
  set Y := dom i ∩ E ∩ (dom j ∩ E) with hY
  have hYE : Y ⊆ E := fun u hu => hu.1.2
  have hspan : vectorSpan ℝ Y = vectorSpan ℝ E :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hYE) hdim
  have haff : affineSpan ℝ Y = affineSpan ℝ E :=
    AffineSubspace.eq_of_direction_eq_of_nonempty_of_le (by simpa only [direction_affineSpan] using hspan)
      (hne.mono (subset_affineSpan ℝ Y)) (affineSpan_mono ℝ hYE)
  have hagree : EqOn (aff i) (aff j) Y := fun u hu =>
    ((h.mem_iff i u).1 hu.1.1).2.symm.trans ((h.mem_iff j u).1 hu.2.1).2
  have hagreeE : ∀ u ∈ E, aff i u = aff j u := fun u hu =>
    AffineMap.eqOn_affineSpan hagree (by rw [haff]; exact subset_affineSpan ℝ E hu)
  ext u
  simp only [mem_inter_iff, h.mem_iff]
  constructor
  · rintro ⟨⟨hB, hF⟩, hE⟩
    exact ⟨⟨hB, hF.trans (hagreeE u hE)⟩, hE⟩
  · rintro ⟨⟨hB, hF⟩, hE⟩
    exact ⟨⟨hB, hF.trans (hagreeE u hE).symm⟩, hE⟩

omit [FiniteDimensional ℝ V] in
/-- Cells are convex. -/
theorem convex_of_mem (h : MaxFamily B dom br aff F) {C : Set V} (hC : C ∈ famCells dom br n) :
    Convex ℝ C := by
  obtain ⟨i, hi, -, hface⟩ := hC
  exact hface.2.convex (h.convex i hi)

end MaxFamily

end Family

/-! ## Part 4: the switch — `S` and `T` as families, and the facts about one side of the crossing -/

section Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- `ℓ_K` as an affine map. -/
noncomputable def chainAff (K : Finset s.P') : (s.P' → ℝ) →ᵃ[ℝ] ℝ :=
  (∑ p ∈ K, (LinearMap.proj p : (s.P' → ℝ) →ₗ[ℝ] ℝ)).toAffineMap

theorem chainAff_apply (K : Finset s.P') (u : s.P' → ℝ) : chainAff s K u = s.chainSum K u := by
  simp [chainAff, Switch.chainSum]

/-- An upper branch as an affine map. -/
noncomputable def upAff : Option s.P' → (s.P' → ℝ) →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ _ 1
  | some r => (LinearMap.proj r : (s.P' → ℝ) →ₗ[ℝ] ℝ).toAffineMap

theorem upAff_apply (j : Option s.P') (u : s.P' → ℝ) : upAff s j u = s.upVal j u := by
  cases j <;> rfl

theorem maxFamily_L : MaxFamily s.B s.domL s.lowBranches (chainAff s) s.L where
  mem_iff K u := by rw [chainAff_apply]; rfl
  le K hK u _ := by rw [chainAff_apply]; exact Finset.le_sup' (fun K => s.chainSum K u) hK
  convex K hK := by
    obtain ⟨S, hS⟩ := s.domL_isPolytope K hK
    rw [hS]
    exact convex_convexHull ℝ _

theorem maxFamily_U : MaxFamily s.B s.domU s.upBranches (fun j => -upAff s j) (fun u => -s.U u) where
  mem_iff j u := by
    simp only [AffineMap.coe_neg, Pi.neg_apply, neg_inj, upAff_apply]
    rfl
  le j hj u _ := by
    simp only [AffineMap.coe_neg, Pi.neg_apply, upAff_apply, neg_le_neg_iff]
    exact Finset.inf'_le (fun j => s.upVal j u) hj
  convex j hj := by
    obtain ⟨S, hS⟩ := s.domU_isPolytope j hj
    rw [hS]
    exact convex_convexHull ℝ _

theorem cellsS_eq : s.cellsS = famCells s.domL s.lowBranches (Fintype.card s.P') := rfl

theorem cellsT_eq : s.cellsT = famCells s.domU s.upBranches (Fintype.card s.P') := rfl

variable {s}

section Side

variable {ι : Type*} {dom : ι → Set (s.P' → ℝ)} {br : Finset ι} {aff : ι → (s.P' → ℝ) →ᵃ[ℝ] ℝ}
  {F : (s.P' → ℝ) → ℝ} {E : Set (s.P' → ℝ)}

/-- A top cell of the restriction is a domain piece. -/
theorem top_dom {A : Set (s.P' → ℝ)} (hA : A ∈ s.topCells (famCells dom br (Fintype.card s.P')) E) :
    ∃ i ∈ br, adim (dom i) = Fintype.card s.P' ∧ A = dom i ∩ E := by
  obtain ⟨⟨hne, C, hC, rfl⟩, hdim⟩ := hA
  exact MaxFamily.top_eq hC hne hdim

/-- Two top cells meeting in dimension `e` are equal (paper G5). -/
theorem top_eq_of_inter (hfam : MaxFamily s.B dom br aff F) {A A' : Set (s.P' → ℝ)}
    (hA : A ∈ s.topCells (famCells dom br (Fintype.card s.P')) E)
    (hA' : A' ∈ s.topCells (famCells dom br (Fintype.card s.P')) E)
    (hne : (A ∩ A').Nonempty) (hdim : adim (A ∩ A') = adim E) : A = A' := by
  obtain ⟨i, -, -, rfl⟩ := top_dom hA
  obtain ⟨j, -, -, rfl⟩ := top_dom hA'
  exact hfam.eq_of_inter hne hdim

/-- Two top cells meet in a cell (when they meet). -/
theorem top_inter_mem (hfam : MaxFamily s.B dom br aff F)
    (hres : s.restrict (famCells dom br (Fintype.card s.P')) E ⊆ famCells dom br (Fintype.card s.P'))
    {A A' : Set (s.P' → ℝ)}
    (hA : A ∈ s.topCells (famCells dom br (Fintype.card s.P')) E)
    (hA' : A' ∈ s.topCells (famCells dom br (Fintype.card s.P')) E)
    (hne : (A ∩ A').Nonempty) : A ∩ A' ∈ famCells dom br (Fintype.card s.P') := by
  obtain ⟨i, hi, hn, rfl⟩ := top_dom hA
  obtain ⟨j, hj, -, rfl⟩ := top_dom hA'
  have hset : dom i ∩ E ∩ (dom j ∩ E) = (dom i ∩ dom j) ∩ E := by
    ext u; simp only [mem_inter_iff]; tauto
  rw [hset] at hne ⊢
  have hcell : dom i ∩ dom j ∈ famCells dom br (Fintype.card s.P') :=
    ⟨i, hi, hn, hfam.inter_isFace hj (hne.mono inter_subset_left)⟩
  exact hres ⟨hne, _, hcell, rfl⟩

/-- A top cell lies in `E`. -/
theorem top_subset {K : Set (Set (s.P' → ℝ))} {A : Set (s.P' → ℝ)} (hA : A ∈ s.topCells K E) : A ⊆ E := by
  obtain ⟨⟨-, C, -, rfl⟩, -⟩ := hA
  exact inter_subset_right

end Side

end Switch

/-! ## Part 5: carriers, relative interiors, and the counting tools -/

section Tools

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A face of `Q` through a relative-interior point of `Q` is `Q`. -/
theorem face_eq_of_relint {Q F : Set V} (hF : IsFace Q F) {w : V} (hwF : w ∈ F)
    (hwQ : w ∈ intrinsicInterior ℝ Q) : F = Q := by
  obtain ⟨l, hl⟩ := hF.2 hF.1
  have hmax : ∀ y ∈ Q, l y ≤ l w := by
    have h := hwF
    rw [hl] at h
    exact h.2
  have hconst := linear_eq_of_intrinsicInterior_max hwQ l hmax
  apply Subset.antisymm hF.subset
  intro y hy
  rw [hl]
  exact ⟨hy, fun z hz => (hconst z hz).le.trans (hconst y hy).ge⟩

/-- A cell inside the face `E` through a relative-interior point of `E` has carrier `E`. -/
theorem isCarrier_of_relint {B E C : Set V} (hE : IsFace B E) (hCE : C ⊆ E) {w : V} (hwC : w ∈ C)
    (hwE : w ∈ intrinsicInterior ℝ E) : IsCarrier B E C := by
  refine ⟨hE, hCE, fun E' hE' hCE' => ?_⟩
  have hface : IsFace E (E ∩ E') := hE'.inter_subset hE.subset ⟨w, hCE hwC, hCE' hwC⟩
  exact inter_eq_left.mp (face_eq_of_relint hface ⟨hCE hwC, hCE' hwC⟩ hwE)

/-- `w` is in the relative interior of `Y ⊇ R` when `dim Y = dim R` and `R` contains a ball of `w + W ⊇ w + dir R`. -/
theorem mem_relint_of_superset {R Y : Set V} {W : Submodule ℝ V} {w : V} {ε : ℝ} (hε : 0 < ε)
    (hRY : R ⊆ Y) (hdim : adim Y = adim R) (hspan : vectorSpan ℝ R ≤ W)
    (hball : ∀ v ∈ W, ‖v‖ < ε → w + v ∈ R) : w ∈ intrinsicInterior ℝ Y := by
  have heq : vectorSpan ℝ R = vectorSpan ℝ Y :=
    Submodule.eq_of_le_of_finrank_eq (vectorSpan_mono ℝ hRY) hdim.symm
  refine mem_intrinsicInterior_of_ball hε (hRY ?_) (heq ▸ hspan) (fun v hv hvε => hRY (hball v hv hvε))
  simpa using hball 0 (Submodule.zero_mem _) (by simpa using hε)

end Tools

/-- A connected finite graph with two different paths `a b c`, `a d c` has at least as many edges as vertices. -/
theorem card_le_card_edgeSet {W : Type*} [Finite W] {G : SimpleGraph W} (hconn : G.Connected) {a b c d : W}
    (hab : G.Adj a b) (hbc : G.Adj b c) (had : G.Adj a d) (hdc : G.Adj d c) (hac : a ≠ c) (hbd : b ≠ d) :
    Nat.card W ≤ Nat.card G.edgeSet := by
  have hle := hconn.card_vert_le_card_edgeSet_add_one
  by_contra hlt
  have htree := SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, by omega⟩
  have hp : (SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc SimpleGraph.Walk.nil)).IsPath := by
    simp [SimpleGraph.Walk.cons_isPath_iff, hab.ne, hbc.ne, hac]
  have hq : (SimpleGraph.Walk.cons had (SimpleGraph.Walk.cons hdc SimpleGraph.Walk.nil)).IsPath := by
    simp [SimpleGraph.Walk.cons_isPath_iff, had.ne, hdc.ne, hac]
  have hpq := (htree.isAcyclic.subsingleton_path a c).elim ⟨_, hp⟩ ⟨_, hq⟩
  have hsupp := congrArg (fun p : G.Path a c => p.1.support) hpq
  simp at hsupp
  exact hbd hsupp

/-- Counting by an injection: disjoint nonempty families inside `𝒞`, plus extra members of `𝒞` outside the chosen
representatives. -/
theorem card_add_card_le {α ι κ : Type*} [Finite ι] [Finite κ] {𝒞 : Set α} (h𝒞 : 𝒞.Finite)
    (Fam : ι → Set α) (hdisj : ∀ i j, i ≠ j → Disjoint (Fam i) (Fam j)) (g : ι → α) (hg : ∀ i, g i ∈ Fam i)
    (hgC : ∀ i, g i ∈ 𝒞) (x : κ → α) (hxC : ∀ j, x j ∈ 𝒞) (hxinj : Function.Injective x)
    (hxg : ∀ j i, x j ≠ g i) : Nat.card ι + Nat.card κ ≤ 𝒞.ncard := by
  have : Finite 𝒞 := h𝒞.to_subtype
  let f : ι ⊕ κ → 𝒞 := Sum.elim (fun i => ⟨g i, hgC i⟩) (fun j => ⟨x j, hxC j⟩)
  have hf : Function.Injective f := by
    rintro (i | j) (i' | j') h <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · by_contra hne
      have hii : i ≠ i' := fun e => hne (congrArg Sum.inl e)
      exact Set.disjoint_left.mp (hdisj i i' hii) (hg i) (h ▸ hg i')
    · exact absurd h.symm (hxg j' i)
    · exact absurd h (hxg j i')
    · rw [hxinj h]
  rw [← Nat.card_sum, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective f hf

/-! ## Part 6: the three degree counts for one switch -/

section Count

variable {P : Type*} [Fintype P] [PartialOrder P] {s : Switch P} {E : Set (s.P' → ℝ)}

/-- The `k`-cells of `K` with carrier `E`; `carrierNum K E k` is its `ncard`. -/
def cset (s : Switch P) (K : Set (Set (s.P' → ℝ))) (E : Set (s.P' → ℝ)) (k : ℕ) : Set (Set (s.P' → ℝ)) :=
  {C | C ∈ K ∧ adim C = k ∧ IsCarrier s.B E C}

/-- The `k`-cells of `S` and of `T` with carrier `E`, as one index type. -/
abbrev YIdx (s : Switch P) (E : Set (s.P' → ℝ)) (k : ℕ) : Type _ :=
  ↥(cset s s.cellsS E k) ⊕ ↥(cset s s.cellsT E k)

def Ycell {k : ℕ} : YIdx s E k → Set (s.P' → ℝ) := Sum.elim Subtype.val Subtype.val

theorem Ycell_props {k : ℕ} (i : YIdx s E k) :
    (Ycell i ∈ s.cellsS ∨ Ycell i ∈ s.cellsT) ∧ adim (Ycell i) = k ∧ IsCarrier s.B E (Ycell i) := by
  rcases i with ⟨Y, hY, hk, hc⟩ | ⟨Y, hY, hk, hc⟩
  exacts [⟨Or.inl hY, hk, hc⟩, ⟨Or.inr hY, hk, hc⟩]

/-- Lemma 3.5(i), cover part, specialized to `E`. -/
abbrev CoverHyp (s : Switch P) (E : Set (s.P' → ℝ)) : Prop :=
  ∀ Y : Set (s.P' → ℝ), (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → IsCarrier s.B E Y → adim Y < adim E →
    (s.RR Y).Nonempty ∧ ∀ R ∈ s.RR Y, IsCarrier s.B E R

/-- Lemma 3.5(i), disjointness part, specialized to `E`. -/
abbrev DisjHyp (s : Switch P) (E : Set (s.P' → ℝ)) : Prop :=
  ∀ Y Y' : Set (s.P' → ℝ), ((Y ∈ s.cellsS ∧ Y' ∈ s.cellsS ∧ Y ≠ Y') ∨ (Y ∈ s.cellsT ∧ Y' ∈ s.cellsT ∧ Y ≠ Y') ∨
      (Y ∈ s.cellsS ∧ Y' ∈ s.cellsT)) →
    IsCarrier s.B E Y → IsCarrier s.B E Y' → adim Y = adim Y' → adim Y < adim E → Disjoint (s.RR Y) (s.RR Y')

theorem Ycell_disj (hdisj : DisjHyp s E) {k : ℕ} (hk : k < adim E) (i j : YIdx s E k) (hij : i ≠ j) :
    Disjoint (s.RR (Ycell i)) (s.RR (Ycell j)) := by
  rcases i with ⟨Y, hY, hYk, hYc⟩ | ⟨Y, hY, hYk, hYc⟩ <;>
    rcases j with ⟨Y', hY', hY'k, hY'c⟩ | ⟨Y', hY', hY'k, hY'c⟩
  · have hne : Y ≠ Y' := fun h => hij (by subst h; rfl)
    exact hdisj Y Y' (Or.inl ⟨hY, hY', hne⟩) hYc hY'c (hYk.trans hY'k.symm) (by omega)
  · exact hdisj Y Y' (Or.inr (Or.inr ⟨hY, hY'⟩)) hYc hY'c (hYk.trans hY'k.symm) (by omega)
  · exact (hdisj Y' Y (Or.inr (Or.inr ⟨hY', hY⟩)) hY'c hYc (hY'k.trans hYk.symm) (by omega)).symm
  · have hne : Y ≠ Y' := fun h => hij (by subst h; rfl)
    exact hdisj Y Y' (Or.inr (Or.inl ⟨hY, hY', hne⟩)) hYc hY'c (hYk.trans hY'k.symm) (by omega)

theorem RR_mem_cset (hcover : CoverHyp s E) {k : ℕ} {Y R : Set (s.P' → ℝ)}
    (hY : Y ∈ s.cellsS ∨ Y ∈ s.cellsT) (hYk : adim Y = k) (hYc : IsCarrier s.B E Y) (hk : k < adim E)
    (hR : R ∈ s.RR Y) : R ∈ cset s s.cellsR E k :=
  ⟨hR.1, hR.2.2.trans hYk, (hcover Y hY hYc (by omega)).2 R hR⟩

theorem Ycell_nonempty (hcover : CoverHyp s E) {k : ℕ} (hk : k < adim E) (i : YIdx s E k) :
    (s.RR (Ycell i)).Nonempty :=
  (hcover _ (Ycell_props i).1 (Ycell_props i).2.2 (by rw [(Ycell_props i).2.1]; exact hk)).1

/-- The count below the top degree: `σ_E(k) + τ_E(k) + |κ| ≤ ρ_E(k)`. -/
theorem count_lt (hcover : CoverHyp s E) (hdisj : DisjHyp s E) {k : ℕ} (hk : k < adim E) {κ : Type*}
    [Finite κ] (x : κ → Set (s.P' → ℝ)) (hxC : ∀ j, x j ∈ cset s s.cellsR E k)
    (hxinj : Function.Injective x) (g : YIdx s E k → Set (s.P' → ℝ)) (hg : ∀ i, g i ∈ s.RR (Ycell i))
    (hxg : ∀ j i, x j ≠ g i) :
    s.carrierNum s.cellsS E k + s.carrierNum s.cellsT E k + Nat.card κ ≤ s.carrierNum s.cellsR E k := by
  have hfinS : (cset s s.cellsS E k).Finite := s.carrierCells_finite s.cellsS_finite E k
  have hfinT : (cset s s.cellsT E k).Finite := s.carrierCells_finite s.cellsT_finite E k
  have : Finite (cset s s.cellsS E k) := hfinS.to_subtype
  have : Finite (cset s s.cellsT E k) := hfinT.to_subtype
  have h := card_add_card_le (s.carrierCells_finite s.cellsR_finite E k) (fun i => s.RR (Ycell i))
    (Ycell_disj hdisj hk) g hg
    (fun i => RR_mem_cset hcover (Ycell_props i).1 (Ycell_props i).2.1 (Ycell_props i).2.2 hk (hg i))
    x hxC hxinj hxg
  rw [Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
  exact h

/-- Degree `e − 2`: an extra cell `R₀` of `R` in none of the sets `R(Y)` gives `ρ ≥ σ + τ + 1`. -/
theorem count_low (hcover : CoverHyp s E) (hdisj : DisjHyp s E) {k : ℕ} (hk : k < adim E)
    {R₀ : Set (s.P' → ℝ)} (hR₀ : R₀ ∈ cset s s.cellsR E k)
    (hnot : ∀ Y, (Y ∈ s.cellsS ∨ Y ∈ s.cellsT) → adim Y = k → IsCarrier s.B E Y → R₀ ∉ s.RR Y) :
    s.carrierNum s.cellsS E k + s.carrierNum s.cellsT E k + 1 ≤ s.carrierNum s.cellsR E k := by
  have hne := Ycell_nonempty hcover hk
  have h := count_lt hcover hdisj hk (κ := Unit) (fun _ => R₀) (fun _ => hR₀) (fun _ _ _ => rfl)
    (fun i => (hne i).some) (fun i => (hne i).some_mem)
    (fun _ i h => hnot _ (Ycell_props i).1 (Ycell_props i).2.1 (Ycell_props i).2.2 (h ▸ (hne i).some_mem))
  simpa using h

/-- Degree `e − 1`: one cell of `S` and one of `T` with two members of `R(Y)` each give `ρ ≥ σ + τ + 2`. -/
theorem count_mid (hcover : CoverHyp s E) (hdisj : DisjHyp s E) {k : ℕ} (hk : k < adim E)
    {Ys Yt c₁ c₂ d₁ d₂ : Set (s.P' → ℝ)} (hYs : Ys ∈ cset s s.cellsS E k) (hYt : Yt ∈ cset s s.cellsT E k)
    (hc₁ : c₁ ∈ s.RR Ys) (hc₂ : c₂ ∈ s.RR Ys) (hc : c₁ ≠ c₂)
    (hd₁ : d₁ ∈ s.RR Yt) (hd₂ : d₂ ∈ s.RR Yt) (hd : d₁ ≠ d₂) :
    s.carrierNum s.cellsS E k + s.carrierNum s.cellsT E k + 2 ≤ s.carrierNum s.cellsR E k := by
  classical
  let iS : YIdx s E k := Sum.inl ⟨Ys, hYs⟩
  let iT : YIdx s E k := Sum.inr ⟨Yt, hYt⟩
  have hTS : iT ≠ iS := Sum.inr_ne_inl
  have hne := Ycell_nonempty hcover hk
  let g : YIdx s E k → Set (s.P' → ℝ) := fun i => if i = iS then c₁ else if i = iT then d₁ else (hne i).some
  have hg : ∀ i, g i ∈ s.RR (Ycell i) := by
    intro i
    simp only [g]
    split_ifs with h1 h2
    · subst h1; exact hc₁
    · subst h2; exact hd₁
    · exact (hne i).some_mem
  have hsep : ∀ i₀ i a b, i ≠ i₀ → a ∈ s.RR (Ycell i₀) → b ∈ s.RR (Ycell i) → a ≠ b :=
    fun i₀ i a b hii ha hb hab => Set.disjoint_left.mp (Ycell_disj hdisj hk i i₀ hii) hb (hab ▸ ha)
  let x : Bool → Set (s.P' → ℝ) := fun b => if b then c₂ else d₂
  have hxinj : Function.Injective x := by
    intro b b' h
    cases b <;> cases b' <;> simp only [x, Bool.false_eq_true, ite_true, ite_false] at h
    · rfl
    · exact absurd h.symm (hsep iS iT c₂ d₂ hTS hc₂ hd₂)
    · exact absurd h (hsep iS iT c₂ d₂ hTS hc₂ hd₂)
    · rfl
  have hxg : ∀ j i, x j ≠ g i := by
    intro j i
    cases j
    · by_cases hi : i = iT
      · subst hi
        simp only [x, g, Bool.false_eq_true, ite_false, hTS, ite_true]
        exact hd.symm
      · exact hsep iT i d₂ (g i) hi hd₂ (hg i)
    · by_cases hi : i = iS
      · subst hi
        simp only [x, g, ite_true]
        exact hc.symm
      · exact hsep iS i c₂ (g i) hi hc₂ (hg i)
  have hxC : ∀ j, x j ∈ cset s s.cellsR E k := by
    intro j
    cases j
    · exact RR_mem_cset hcover (Or.inr hYt.1) hYt.2.1 hYt.2.2 hk hd₂
    · exact RR_mem_cset hcover (Or.inl hYs.1) hYs.2.1 hYs.2.2 hk hc₂
  have h := count_lt hcover hdisj hk x hxC hxinj g hg hxg
  simpa using h

end Count

section Top

variable {P : Type*} [Fintype P] [PartialOrder P] {s : Switch P} {E : Set (s.P' → ℝ)}

/-- Edges of `G_E` all have the form `{A, D}` with `A ∩ D` an `e`-cell of `R|_E`. -/
theorem edge_form {e : Sym2 (↥(s.topCells s.cellsS E) ⊕ ↥(s.topCells s.cellsT E))}
    (he : e ∈ (s.graphG E).edgeSet) :
    ∃ A D, e = s(Sum.inl A, Sum.inr D) ∧ A.1 ∩ D.1 ∈ s.topCells s.cellsR E := by
  induction e using Sym2.ind with
  | h x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    rcases x with A | D <;> rcases y with A' | D'
    · exact (he : False).elim
    · exact ⟨A, D', rfl, he⟩
    · exact ⟨A', D, Sym2.eq_swap, he⟩
    · exact (he : False).elim

/-- Degree `e`: the 4-cycle `S₁ T₁ S₂ T₂` in the connected graph `G_E` gives `ρ_E(e) ≥ σ_E(e) + τ_E(e)`. -/
theorem count_top (hE : IsFace s.B E) (hconn : (s.graphG E).Connected)
    {S₁ S₂ T₁ T₂ : Set (s.P' → ℝ)} (hS₁ : S₁ ∈ s.topCells s.cellsS E) (hS₂ : S₂ ∈ s.topCells s.cellsS E)
    (hT₁ : T₁ ∈ s.topCells s.cellsT E) (hT₂ : T₂ ∈ s.topCells s.cellsT E) (hS : S₁ ≠ S₂) (hT : T₁ ≠ T₂)
    (h11 : S₁ ∩ T₁ ∈ s.topCells s.cellsR E) (h12 : S₁ ∩ T₂ ∈ s.topCells s.cellsR E)
    (h21 : S₂ ∩ T₁ ∈ s.topCells s.cellsR E) (h22 : S₂ ∩ T₂ ∈ s.topCells s.cellsR E)
    (hSeq : ∀ A A', A ∈ s.topCells s.cellsS E → A' ∈ s.topCells s.cellsS E → (A ∩ A').Nonempty →
      adim (A ∩ A') = adim E → A = A')
    (hTeq : ∀ D D', D ∈ s.topCells s.cellsT E → D' ∈ s.topCells s.cellsT E → (D ∩ D').Nonempty →
      adim (D ∩ D') = adim E → D = D') :
    s.carrierNum s.cellsS E (adim E) + s.carrierNum s.cellsT E (adim E) ≤
      s.carrierNum s.cellsR E (adim E) := by
  unfold Switch.carrierNum
  rw [← s.topCellsS_eq_carried hE, ← s.topCellsT_eq_carried hE, ← s.topCellsR_eq_carried hE]
  have : Finite (s.topCells s.cellsS E) :=
    ((s.restrict_finite s.cellsS_finite E).subset fun _ h => h.1).to_subtype
  have : Finite (s.topCells s.cellsT E) :=
    ((s.restrict_finite s.cellsT_finite E).subset fun _ h => h.1).to_subtype
  have : Finite (s.topCells s.cellsR E) :=
    ((s.restrict_finite s.cellsR_finite E).subset fun _ h => h.1).to_subtype
  -- vertices ≤ edges
  have hVE := card_le_card_edgeSet hconn (a := Sum.inl ⟨S₁, hS₁⟩) (b := Sum.inr ⟨T₁, hT₁⟩)
    (c := Sum.inl ⟨S₂, hS₂⟩) (d := Sum.inr ⟨T₂, hT₂⟩) h11 h21 h12 h22
    (fun h => hS (congrArg Subtype.val (Sum.inl_injective h))) (fun h => hT (congrArg Subtype.val (Sum.inr_injective h)))
  rw [Nat.card_sum, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hVE
  -- edges ≤ e-cells of R|_E
  let cellOf : (↥(s.topCells s.cellsS E) ⊕ ↥(s.topCells s.cellsT E)) → Set (s.P' → ℝ) :=
    Sum.elim Subtype.val Subtype.val
  let f : Sym2 (↥(s.topCells s.cellsS E) ⊕ ↥(s.topCells s.cellsT E)) → Set (s.P' → ℝ) :=
    Sym2.lift ⟨fun x y => cellOf x ∩ cellOf y, fun _ _ => inter_comm _ _⟩
  let fe : (s.graphG E).edgeSet → s.topCells s.cellsR E := fun e => ⟨f e.1, by
    obtain ⟨A, D, he, hmem⟩ := edge_form e.2
    rw [he]
    exact hmem⟩
  have hinj : Function.Injective fe := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    obtain ⟨A, D, rfl, hmem⟩ := edge_form he₁
    obtain ⟨A', D', rfl, hmem'⟩ := edge_form he₂
    have hcell : A.1 ∩ D.1 = A'.1 ∩ D'.1 := congrArg Subtype.val h
    have hsubE : ∀ {X Y : Set (s.P' → ℝ)}, X ∈ s.topCells s.cellsS E ∨ X ∈ s.topCells s.cellsT E →
        X ∩ Y ⊆ E := by
      rintro X Y (hX | hX) <;> exact inter_subset_left.trans (top_subset hX)
    have hdimE : ∀ {X Y : Set (s.P' → ℝ)}, X ∈ s.topCells s.cellsS E ∨ X ∈ s.topCells s.cellsT E →
        A.1 ∩ D.1 ⊆ X ∩ Y → adim (X ∩ Y) = adim E := by
      intro X Y hX hsub
      apply le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ (hsubE hX)))
      exact hmem.2.symm.le.trans (Submodule.finrank_mono (vectorSpan_mono ℝ hsub))
    have hAA : A.1 ∩ D.1 ⊆ A.1 ∩ A'.1 := fun u hu => ⟨hu.1, (hcell ▸ hu).1⟩
    have hDD : A.1 ∩ D.1 ⊆ D.1 ∩ D'.1 := fun u hu => ⟨hu.2, (hcell ▸ hu).2⟩
    have hA : A = A' := Subtype.ext (hSeq _ _ A.2 A'.2 (hmem.1.1.mono hAA) (hdimE (Or.inl A.2) hAA))
    have hD : D = D' := Subtype.ext (hTeq _ _ D.2 D'.2 (hmem.1.1.mono hDD) (hdimE (Or.inr D.2) hDD))
    subst hA hD
    rfl
  have hER := Nat.card_le_card_of_injective fe hinj
  rw [Nat.card_coe_set_eq (s.topCells s.cellsR E)] at hER
  omega

end Top

/-! ## Part 7: the crossing gives the three degree inequalities -/

section Crossing

variable {P : Type*} [Fintype P] [PartialOrder P] {s : Switch P}

theorem crossing_counts (hT : s.Transverse) {E : Set (s.P' → ℝ)} (hE : IsFace s.B E)
    (hcover : CoverHyp s E) (hdisj : DisjHyp s E) (hconn : (s.graphG E).Connected) {w : s.P' → ℝ}
    (hw : CrossingAt s E w) :
    2 ≤ adim E ∧
    s.carrierNum s.cellsS E (adim E - 2) + s.carrierNum s.cellsT E (adim E - 2) + 1 ≤
      s.carrierNum s.cellsR E (adim E - 2) ∧
    s.carrierNum s.cellsS E (adim E - 1) + s.carrierNum s.cellsT E (adim E - 1) + 2 ≤
      s.carrierNum s.cellsR E (adim E - 1) ∧
    s.carrierNum s.cellsS E (adim E) + s.carrierNum s.cellsT E (adim E) ≤ s.carrierNum s.cellsR E (adim E) := by
  obtain ⟨hwE, N, -, -, hNw, S₁, S₂, T₁, T₂, φ, ψ, hS₁, hS₂, hT₁, hT₂, -, -, hS₁N, hS₂N, hT₁N, hT₂N, hind⟩ := hw
  obtain ⟨ε, hε, hball⟩ := exists_ball hwE hNw
  have hL : Local E N w ε := ⟨hε, hball⟩
  -- dual vectors and the dimensions of the model subspaces
  obtain ⟨v₁, hv₁, h1⟩ := surj_of_linearIndependent _ φ ψ hind (1, 0)
  obtain ⟨v₂, hv₂, h2⟩ := surj_of_linearIndependent _ φ ψ hind (0, 1)
  have h11 : φ v₁ = 1 := congrArg Prod.fst h1
  have h12 : ψ v₁ = 0 := congrArg Prod.snd h1
  have h21 : φ v₂ = 0 := congrArg Prod.fst h2
  have h22 : ψ v₂ = 1 := congrArg Prod.snd h2
  have hadim : adim E = Module.finrank ℝ (vectorSpan ℝ E) := rfl
  have hdimφ : Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ) + 1 = adim E := by
    have := finrank_inf_ker_add (vectorSpan ℝ E) φ
      (fun y => ⟨y • v₁, Submodule.smul_mem _ _ hv₁, by simp [h11]⟩)
    rw [Module.finrank_self] at this
    rw [hadim]; exact this
  have hdimψ : Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker ψ) + 1 = adim E := by
    have := finrank_inf_ker_add (vectorSpan ℝ E) ψ
      (fun y => ⟨y • v₂, Submodule.smul_mem _ _ hv₂, by simp [h22]⟩)
    rw [Module.finrank_self] at this
    rw [hadim]; exact this
  have hdim2 : Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ) + 2 = adim E := by
    have := finrank_inf_ker_add (vectorSpan ℝ E) (φ.prod ψ) (surj_of_linearIndependent _ φ ψ hind)
    rw [LinearMap.ker_prod, ← inf_assoc, Module.finrank_prod, Module.finrank_self] at this
    rw [hadim]; omega
  have he2 : 2 ≤ adim E := by omega
  -- the walls `S_w = S₁ ∩ S₂`, `T_w = T₁ ∩ T₂` and the crossing `R_w`
  have hS₁c : S₁ ∈ s.cellsS := s.restrict_cellsS_subset hE hS₁.1
  have hS₂c : S₂ ∈ s.cellsS := s.restrict_cellsS_subset hE hS₂.1
  have hT₁c : T₁ ∈ s.cellsT := s.restrict_cellsT_subset hE hT₁.1
  have hT₂c : T₂ ∈ s.cellsT := s.restrict_cellsT_subset hE hT₂.1
  have hwS₁ : w ∈ S₁ := hL.w_mem hS₁N
  have hwS₂ : w ∈ S₂ := hL.w_mem (Local.half_neg hS₂N)
  have hwT₁ : w ∈ T₁ := hL.w_mem hT₁N
  have hwT₂ : w ∈ T₂ := hL.w_mem (Local.half_neg hT₂N)
  have hSw : S₁ ∩ S₂ ∈ s.cellsS :=
    top_inter_mem (maxFamily_L s) (s.restrict_cellsS_subset hE) hS₁ hS₂ ⟨w, hwS₁, hwS₂⟩
  have hTw : T₁ ∩ T₂ ∈ s.cellsT :=
    top_inter_mem (maxFamily_U s) (s.restrict_cellsT_subset hE) hT₁ hT₂ ⟨w, hwT₁, hwT₂⟩
  have hSwE : S₁ ∩ S₂ ⊆ E := inter_subset_left.trans (top_subset hS₁)
  have hTwE : T₁ ∩ T₂ ⊆ E := inter_subset_left.trans (top_subset hT₁)
  have hSwspan := hL.wall_span hS₁N hS₂N ((maxFamily_L s).convex_of_mem hSw) hSwE
  have hTwspan := hL.wall_span hT₁N hT₂N ((maxFamily_U s).convex_of_mem hTw) hTwE
  have hSwdim : adim (S₁ ∩ S₂) = adim E - 1 := by
    have : adim (S₁ ∩ S₂) = Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ) := by
      unfold adim; rw [hSwspan]
    omega
  have hTwdim : adim (T₁ ∩ T₂) = adim E - 1 := by
    have : adim (T₁ ∩ T₂) = Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker ψ) := by
      unfold adim; rw [hTwspan]
    omega
  have hSwcar : IsCarrier s.B E (S₁ ∩ S₂) := isCarrier_of_relint hE hSwE ⟨hwS₁, hwS₂⟩ hwE
  have hTwcar : IsCarrier s.B E (T₁ ∩ T₂) := isCarrier_of_relint hE hTwE ⟨hwT₁, hwT₂⟩ hwE
  have hwR : w ∈ S₁ ∩ S₂ ∩ (T₁ ∩ T₂) := ⟨⟨hwS₁, hwS₂⟩, ⟨hwT₁, hwT₂⟩⟩
  have hRw : S₁ ∩ S₂ ∩ (T₁ ∩ T₂) ∈ s.cellsR := ⟨⟨w, hwR⟩, _, hSw, _, hTw, rfl⟩
  have hRwspan := hL.cross_span hS₁N hS₂N hT₁N hT₂N ((maxFamily_L s).convex_of_mem hSw) hSwE
    ((maxFamily_U s).convex_of_mem hTw) hTwE
  have hRwdim : adim (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) = adim E - 2 := by
    have : adim (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) =
        Module.finrank ℝ ↥(vectorSpan ℝ E ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ) := by
      unfold adim; rw [hRwspan]
    omega
  have hRwcar : IsCarrier s.B E (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) :=
    isCarrier_of_relint hE (inter_subset_left.trans hSwE) hwR hwE
  have hSwrel : w ∈ intrinsicInterior ℝ (S₁ ∩ S₂) :=
    mem_intrinsicInterior_of_ball hε ⟨hwS₁, hwS₂⟩ hSwspan.le (hL.wall_ball hS₁N hS₂N)
  have hTwrel : w ∈ intrinsicInterior ℝ (T₁ ∩ T₂) :=
    mem_intrinsicInterior_of_ball hε ⟨hwT₁, hwT₂⟩ hTwspan.le (hL.wall_ball hT₁N hT₂N)
  have hres : ∀ {K : Set (Set (s.P' → ℝ))} {Y : Set (s.P' → ℝ)}, Y ∈ K → Y ⊆ E → w ∈ Y → Y ∈ s.restrict K E :=
    fun hY hYE hwY => ⟨⟨w, hwY⟩, _, hY, (inter_eq_left.mpr hYE).symm⟩
  refine ⟨he2, ?_, ?_, ?_⟩
  · -- degree `e − 2`: `R_w` lies in no `R(Y)` (transversality)
    refine count_low hcover hdisj (by omega) ⟨hRw, hRwdim, hRwcar⟩ ?_
    intro Y hY hYk hYc hRY
    have hwY : w ∈ intrinsicInterior ℝ Y :=
      mem_relint_of_superset hε hRY.2.1 hRY.2.2.symm hRwspan.le (hL.cross_ball hS₁N hS₂N hT₁N hT₂N)
    have hwY' : w ∈ Y := hRY.2.1 hwR
    rcases hY with hY | hY
    · have htr := hT E hE w hwE Y (hres hY hYc.2.1 hwY') (T₁ ∩ T₂) (hres hTw hTwE ⟨hwT₁, hwT₂⟩) hwY hTwrel
      have hle : adim (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) ≤ adim (Y ∩ (T₁ ∩ T₂)) :=
        Submodule.finrank_mono (vectorSpan_mono ℝ (fun u hu => ⟨hRY.2.1 hu, hu.2⟩))
      omega
    · have htr := hT E hE w hwE (S₁ ∩ S₂) (hres hSw hSwE ⟨hwS₁, hwS₂⟩) Y (hres hY hYc.2.1 hwY') hSwrel hwY
      have hle : adim (S₁ ∩ S₂ ∩ (T₁ ∩ T₂)) ≤ adim (S₁ ∩ S₂ ∩ Y) :=
        Submodule.finrank_mono (vectorSpan_mono ℝ (fun u hu => ⟨hu.1, hRY.2.1 hu⟩))
      omega
  · -- degree `e − 1`: each wall is cut in two by the other hyperplane
    have hRR : ∀ {Y Z : Set (s.P' → ℝ)}, Z ∈ s.cellsR → Z ⊆ Y → vectorSpan ℝ Y ≤ vectorSpan ℝ Z →
        Z ∈ s.RR Y :=
      fun hZ hZY hspan => ⟨hZ, hZY, le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ hZY))
        (Submodule.finrank_mono hspan)⟩
    refine count_mid hcover hdisj (by omega) (Ys := S₁ ∩ S₂) (Yt := T₁ ∩ T₂) ⟨hSw, hSwdim, hSwcar⟩
      ⟨hTw, hTwdim, hTwcar⟩ (c₁ := S₁ ∩ S₂ ∩ T₁) (c₂ := S₁ ∩ S₂ ∩ T₂) (d₁ := T₁ ∩ T₂ ∩ S₁)
      (d₂ := T₁ ∩ T₂ ∩ S₂) ?_ ?_ (hL.halfwall_ne hS₁N hS₂N hT₁N hT₂N hv₂ h21 h22) ?_ ?_
      (hL.halfwall_ne hT₁N hT₂N hS₁N hS₂N hv₁ h12 h11)
    · exact hRR ⟨⟨w, ⟨hwS₁, hwS₂⟩, hwT₁⟩, _, hSw, _, hT₁c, rfl⟩ inter_subset_left
        (hSwspan ▸ hL.halfwall_span hS₁N hS₂N hT₁N hv₂ h21 h22)
    · exact hRR ⟨⟨w, ⟨hwS₁, hwS₂⟩, hwT₂⟩, _, hSw, _, hT₂c, rfl⟩ inter_subset_left
        (hSwspan ▸ hL.halfwall_span hS₁N hS₂N (Local.half_neg hT₂N) (Submodule.neg_mem _ hv₂)
          (by simp [h21]) (by simp [h22]))
    · exact hRR ⟨⟨w, ⟨hwT₁, hwT₂⟩, hwS₁⟩, _, hS₁c, _, hTw, inter_comm _ _⟩ inter_subset_left
        (hTwspan ▸ hL.halfwall_span hT₁N hT₂N hS₁N hv₁ h12 h11)
    · exact hRR ⟨⟨w, ⟨hwT₁, hwT₂⟩, hwS₂⟩, _, hS₂c, _, hTw, inter_comm _ _⟩ inter_subset_left
        (hTwspan ▸ hL.halfwall_span hT₁N hT₂N (Local.half_neg hS₂N) (Submodule.neg_mem _ hv₁)
          (by simp [h12]) (by simp [h11]))
  · -- degree `e`: the four quadrants are `e`-cells of `R|_E`, giving a 4-cycle in `G_E`
    have htopR : ∀ {A D : Set (s.P' → ℝ)}, A ∈ s.topCells s.cellsS E → D ∈ s.topCells s.cellsT E →
        w ∈ A → w ∈ D → vectorSpan ℝ E ≤ vectorSpan ℝ (A ∩ D) → A ∩ D ∈ s.topCells s.cellsR E := by
      intro A D hA hD hwA hwD hspan
      have hADE : A ∩ D ⊆ E := inter_subset_left.trans (top_subset hA)
      exact ⟨hres ⟨⟨w, hwA, hwD⟩, A, s.restrict_cellsS_subset hE hA.1, D, s.restrict_cellsT_subset hE hD.1, rfl⟩
          hADE ⟨hwA, hwD⟩,
        le_antisymm (Submodule.finrank_mono (vectorSpan_mono ℝ hADE)) (Submodule.finrank_mono hspan)⟩
    exact count_top hE hconn hS₁ hS₂ hT₁ hT₂
      (hL.ne_of_halves hS₁N hS₂N hv₁ (by rw [h11]; norm_num))
      (hL.ne_of_halves hT₁N hT₂N hv₂ (by rw [h22]; norm_num))
      (htopR hS₁ hT₁ hwS₁ hwT₁ (hL.quadrant_span hS₁N hT₁N hv₁ hv₂ h11 h12 h21 h22))
      (htopR hS₁ hT₂ hwS₁ hwT₂ (hL.quadrant_span hS₁N (Local.half_neg hT₂N) hv₁ (Submodule.neg_mem _ hv₂)
        h11 (by simp [h12]) (by simp [h21]) (by simp [h22])))
      (htopR hS₂ hT₁ hwS₂ hwT₁ (hL.quadrant_span (Local.half_neg hS₂N) hT₁N (Submodule.neg_mem _ hv₁) hv₂
        (by simp [h11]) (by simp [h12]) (by simp [h21]) h22))
      (htopR hS₂ hT₂ hwS₂ hwT₂ (hL.quadrant_span (Local.half_neg hS₂N) (Local.half_neg hT₂N)
        (Submodule.neg_mem _ hv₁) (Submodule.neg_mem _ hv₂)
        (by simp [h11]) (by simp [h12]) (by simp [h21]) (by simp [h22])))
      (fun _ _ hA hA' hne hdim => top_eq_of_inter (maxFamily_L s) hA hA' hne hdim)
      (fun _ _ hD hD' hne hdim => top_eq_of_inter (maxFamily_U s) hD hD' hne hdim)

end Crossing

end HibiLi.Proofs.L42

namespace HibiLi.Proofs

open HibiLi Polynomial L42

/-- **Lemma 4.2** (one crossing), from transversality and Lemma 3.5 (given as hypotheses, each the corresponding
statement of `HibiLi/Paper/Statements.lean` for this switch): `δ_E(t) ≥ t^{e−2}(1+t)^2` coefficientwise. -/
theorem lemma_4_2_of {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hT : s.Transverse)
    (h35cover : ∀ (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E)
      (Y : Set (s.P' → ℝ)) (hY : Y ∈ s.cellsS ∨ Y ∈ s.cellsT) (hYE : IsCarrier s.B E Y) (hdim : adim Y < adim E),
      (s.RR Y).Nonempty ∧ ∀ R ∈ s.RR Y, IsCarrier s.B E R)
    (h35disj : ∀ (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (Y Y' : Set (s.P' → ℝ))
      (hYY' : (Y ∈ s.cellsS ∧ Y' ∈ s.cellsS ∧ Y ≠ Y') ∨ (Y ∈ s.cellsT ∧ Y' ∈ s.cellsT ∧ Y ≠ Y') ∨
        (Y ∈ s.cellsS ∧ Y' ∈ s.cellsT))
      (hYE : IsCarrier s.B E Y) (hY'E : IsCarrier s.B E Y') (hdim : adim Y = adim Y') (hlt : adim Y < adim E),
      Disjoint (s.RR Y) (s.RR Y'))
    (h35ii : ∀ (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E), (s.graphG E).Connected)
    (h35iii : ∀ (hT : s.Transverse) (E : Set (s.P' → ℝ)) (hE : IsFace s.B E) (k : ℕ), 0 ≤ s.deltaCoeff E k)
    (hcarrier : ∀ (C : Set (s.P' → ℝ)) (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR),
      (∃! E, IsCarrier s.B E C) ∧ ∀ E, IsCarrier s.B E C → intrinsicInterior ℝ C ⊆ intrinsicInterior ℝ E)
    (E : Set (s.P' → ℝ))
    (hE : IsFace s.B E) (w : s.P' → ℝ) (hw : CrossingAt s E w) (k : ℕ) :
    (X ^ (adim E - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (s.delta E).coeff k := by
  obtain ⟨he2, hlow, hmid, htop⟩ :=
    crossing_counts hT hE (h35cover hT E hE) (h35disj hT E hE) (h35ii hT E hE) hw
  have hcard : adim E ≤ Fintype.card s.P' := adim_le_card E
  have hnn := h35iii hT E hE k
  rw [coeff_X_pow_mul', coeff_one_add_X_pow, delta_coeff]
  unfold Switch.deltaCoeff at hnn ⊢
  rcases (by omega : k < adim E - 2 ∨ k = adim E - 2 ∨ k = adim E - 1 ∨ k = adim E ∨ adim E < k) with
    hk | rfl | rfl | rfl | hk
  · -- below `e − 2`: the left side is `0`
    have h1 : ¬ adim E - 2 ≤ k := by omega
    simp only [h1, ite_false]
    split_ifs at hnn ⊢ <;> omega
  · -- degree `e − 2`: coefficient `1`
    have h2 : adim E - 2 ≤ Fintype.card s.P' := by omega
    have h3 : adim E - 2 ≠ adim E := by omega
    simp only [le_refl, h2, h3, ite_true, ite_false, Nat.sub_self, Nat.choose_zero_right]
    push_cast
    omega
  · -- degree `e − 1`: coefficient `2`
    have h1 : adim E - 2 ≤ adim E - 1 := by omega
    have h2 : adim E - 1 ≤ Fintype.card s.P' := by omega
    have h3 : adim E - 1 ≠ adim E := by omega
    have h4 : adim E - 1 - (adim E - 2) = 1 := by omega
    simp only [h1, h2, h3, h4, ite_true, ite_false, Nat.choose_one_right]
    push_cast
    omega
  · -- degree `e`: coefficient `1`
    have h1 : adim E - 2 ≤ adim E := by omega
    have h4 : adim E - (adim E - 2) = 2 := by omega
    simp only [h1, hcard, h4, ite_true, Nat.choose_self]
    push_cast
    omega
  · -- above `e`: the left side is `0`, the right side is `≥ 0` by Lemma 3.5(iii)
    have h4 : Nat.choose 2 (k - (adim E - 2)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp only [h4, Nat.cast_zero, ite_self]
    split_ifs at hnn ⊢ <;> omega

end HibiLi.Proofs
