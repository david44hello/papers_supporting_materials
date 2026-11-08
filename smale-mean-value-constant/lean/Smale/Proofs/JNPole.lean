/-
Smale/Proofs/JNPole.lean — pole pushing: for a compact `E` with connected complement, every `1/(w - y)`, `y ∉ E`, is a
uniform limit of polynomials on `E`.
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial Complex Metric Filter Topology Set

/-- The closure of the polynomials in `C(E, ℂ)`. -/
local notation "𝒜[" E "]" => Subalgebra.topologicalClosure (polynomialFunctions E)

/-- A polynomial, as an element of the closure. -/
theorem poly_mem_closure (E : Set ℂ) [CompactSpace E] (p : ℂ[X]) : p.toContinuousMapOn E ∈ 𝒜[E] := by
  apply Subalgebra.le_topologicalClosure
  rw [← SetLike.mem_coe, polynomialFunctions_coe]
  exact ⟨p, rfl⟩

/-- An element of the closure is uniformly near a polynomial. -/
theorem exists_poly_near_of_mem_closure {E : Set ℂ} [CompactSpace E] {f : C(E, ℂ)} (hf : f ∈ 𝒜[E]) {ε : ℝ}
    (hε : 0 < ε) : ∃ p : ℂ[X], ∀ w : E, ‖p.eval (w : ℂ) - f w‖ < ε := by
  have hf' : f ∈ closure ((polynomialFunctions E : Subalgebra ℂ C(E, ℂ)) : Set C(E, ℂ)) := hf
  obtain ⟨g, hg, hd⟩ := Metric.mem_closure_iff.1 hf' ε hε
  rw [polynomialFunctions_coe] at hg
  obtain ⟨p, rfl⟩ := hg
  refine ⟨p, fun w => ?_⟩
  have h1 := ContinuousMap.dist_apply_le_dist (f := f) (g := Polynomial.toContinuousMapOnAlgHom E p) w
  rw [dist_comm, dist_eq_norm] at h1
  exact lt_of_le_of_lt h1 hd

/-- Geometric series in the closed subalgebra. -/
theorem exists_mem_closure_inv_one_sub {E : Set ℂ} [CompactSpace E] {g : C(E, ℂ)} (hg : g ∈ 𝒜[E]) (hn : ‖g‖ < 1) :
    ∃ S ∈ 𝒜[E], ∀ w : E, S w = (1 - g w)⁻¹ := by
  have hsum : Summable fun n : ℕ => g ^ n := summable_geometric_of_norm_lt_one hn
  refine ⟨∑' n : ℕ, g ^ n, ?_, fun w => ?_⟩
  · have hlim := hsum.hasSum.tendsto_sum_nat
    refine (Subalgebra.isClosed_topologicalClosure _).mem_of_tendsto hlim (Eventually.of_forall fun N => ?_)
    exact Subalgebra.sum_mem _ fun n _ => Subalgebra.pow_mem _ hg n
  · have h1 : (1 - g) * ∑' n : ℕ, g ^ n = 1 := mul_neg_geom_series g hn
    have h2 := congrArg (fun F : C(E, ℂ) => F w) h1
    simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply] at h2
    exact eq_inv_of_mul_eq_one_right h2

/-- The set of poles reached so far: `y ∉ E` with `1/(w - y)` in the closure. -/
def PoleIn (E : Set ℂ) [CompactSpace E] (y : ℂ) : Prop := y ∉ E ∧ ∃ f ∈ 𝒜[E], ∀ w : E, f w = ((w : ℂ) - y)⁻¹

/-- Far poles: the geometric series in `w/y`. -/
theorem poleIn_of_far {E : Set ℂ} [CompactSpace E] {y : ℂ} {M : ℝ} (hM : ∀ w ∈ E, ‖w‖ ≤ M) (hM0 : 0 ≤ M)
    (hy : 2 * M + 1 ≤ ‖y‖) : PoleIn E y := by
  have hypos : 0 < ‖y‖ := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.1 hypos
  have hyE : y ∉ E := fun h => by
    have := hM y h
    linarith
  set g : C(E, ℂ) := (C y⁻¹ * X : ℂ[X]).toContinuousMapOn E with hgdef
  have hgapply : ∀ w : E, g w = y⁻¹ * (w : ℂ) := fun w => by simp [hgdef]
  have hgn : ‖g‖ < 1 := by
    have h1 : ‖g‖ ≤ M / ‖y‖ := by
      refine (ContinuousMap.norm_le _ (by positivity)).2 fun w => ?_
      rw [hgapply, norm_mul, norm_inv, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right (hM w w.2) hypos.le
    have h2 : M / ‖y‖ < 1 := by
      rw [div_lt_one hypos]
      linarith
    linarith
  obtain ⟨S, hS, hSw⟩ := exists_mem_closure_inv_one_sub (poly_mem_closure E _) hgn
  refine ⟨hyE, (-y⁻¹) • S, Subalgebra.smul_mem _ hS _, fun w => ?_⟩
  have hwy : (w : ℂ) - y ≠ 0 := fun h => hyE (by rw [← sub_eq_zero.1 h]; exact w.2)
  have hS2 : S w = (1 - y⁻¹ * (w : ℂ))⁻¹ := by rw [hSw, ← hgapply]
  rw [ContinuousMap.smul_apply, smul_eq_mul, hS2]
  have h1 : 1 - y⁻¹ * (w : ℂ) = -((w : ℂ) - y) * y⁻¹ := by
    field_simp
    ring
  rw [h1, mul_inv, inv_inv, inv_neg]
  field_simp

/-- Pole pushing: from `y` to `y'`, when `|y' - y| ≤ ρ |w - y|` on `E` with `ρ < 1`. -/
theorem poleIn_push {E : Set ℂ} [CompactSpace E] {y y' : ℂ} (hy : PoleIn E y) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hclose : ∀ w ∈ E, ‖y' - y‖ ≤ ρ * ‖w - y‖) : PoleIn E y' := by
  obtain ⟨hyE, f, hf, hfw⟩ := hy
  set g : C(E, ℂ) := (y' - y) • f with hgdef
  have hgmem : g ∈ 𝒜[E] := Subalgebra.smul_mem _ hf _
  have hgw : ∀ w : E, g w = (y' - y) * ((w : ℂ) - y)⁻¹ := fun w => by
    simp [hgdef, hfw]
  have hwy : ∀ w : E, (w : ℂ) - y ≠ 0 := fun w h => hyE (by rw [← sub_eq_zero.1 h]; exact w.2)
  have hgle : ∀ w : E, ‖g w‖ ≤ ρ := fun w => by
    rw [hgw, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_iff₀ (norm_pos_iff.2 (hwy w))]
    exact hclose w w.2
  have hgn : ‖g‖ < 1 := lt_of_le_of_lt ((ContinuousMap.norm_le _ hρ0).2 hgle) hρ1
  have hy'E : y' ∉ E := by
    intro hmem
    have h1 := hgle ⟨y', hmem⟩
    rw [hgw] at h1
    have h2 : (y' - y) * (y' - y)⁻¹ = 1 := mul_inv_cancel₀ (hwy ⟨y', hmem⟩)
    simp only [h2, norm_one] at h1
    linarith
  obtain ⟨S, hS, hSw⟩ := exists_mem_closure_inv_one_sub hgmem hgn
  refine ⟨hy'E, f * S, Subalgebra.mul_mem _ hf hS, fun w => ?_⟩
  have hwy' : (w : ℂ) - y' ≠ 0 := fun h => hy'E (by rw [← sub_eq_zero.1 h]; exact w.2)
  rw [ContinuousMap.mul_apply, hfw, hSw, hgw]
  have h1 := hwy w
  have h2 : 1 - (y' - y) * ((w : ℂ) - y)⁻¹ = ((w : ℂ) - y') / ((w : ℂ) - y) := by
    field_simp
    ring
  rw [h2]
  field_simp

/-- **Every pole outside `E` is reached**, when the complement of `E` is connected. -/
theorem poleIn_of_compl_preconnected {E : Set ℂ} (hE : IsCompact E) [CompactSpace E] (hc : IsPreconnected Eᶜ) {y : ℂ}
    (hy : y ∉ E) : PoleIn E y := by
  obtain ⟨M, hM⟩ := hE.isBounded.exists_norm_le
  have hM' : ∀ w ∈ E, ‖w‖ ≤ max M 0 := fun w hw => (hM w hw).trans (le_max_left _ _)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  set T : Set ℂ := {z | PoleIn E z} with hTdef
  -- a uniform gap around a point off `E`
  have hgap : ∀ z ∉ E, ∃ δ > 0, ∀ w ∈ E, δ ≤ ‖w - z‖ := by
    intro z hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hE.isClosed.isOpen_compl z hz
    refine ⟨δ, hδ, fun w hw => ?_⟩
    by_contra hlt
    exact hball (by rw [mem_ball_iff_norm]; exact not_le.1 hlt) hw
  have hopen : IsOpen T := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨δ, hδ, hgapz⟩ := hgap z hz.1
    refine ⟨δ / 2, by positivity, fun z' hz' => ?_⟩
    refine poleIn_push hz (ρ := 1 / 2) (by norm_num) (by norm_num) fun w hw => ?_
    have h1 : ‖z' - z‖ < δ / 2 := by rwa [mem_ball_iff_norm] at hz'
    have h2 := hgapz w hw
    linarith
  have hfar : (Eᶜ ∩ T).Nonempty := by
    obtain ⟨z, hz⟩ : ∃ z : ℂ, ‖z‖ = 2 * max M 0 + 1 := by
      refine ⟨((2 * max M 0 + 1 : ℝ) : ℂ), ?_⟩
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hp := poleIn_of_far hM' hM0 hz.ge
    exact ⟨z, hp.1, hp⟩
  have hclosed : closure T ∩ Eᶜ ⊆ T := by
    rintro z ⟨hzcl, hzE⟩
    obtain ⟨δ, hδ, hgapz⟩ := hgap z hzE
    obtain ⟨z', hz'T, hdist⟩ := Metric.mem_closure_iff.1 hzcl (δ / 3) (by positivity)
    refine poleIn_push hz'T (ρ := 1 / 2) (by norm_num) (by norm_num) fun w hw => ?_
    rw [dist_eq_norm] at hdist
    have h2 := hgapz w hw
    have h3 : ‖w - z‖ ≤ ‖w - z'‖ + ‖z' - z‖ := by
      have := norm_add_le (w - z') (z' - z)
      rwa [sub_add_sub_cancel] at this
    have h4 : ‖z - z'‖ = ‖z' - z‖ := norm_sub_rev _ _
    linarith
  exact hc.subset_of_closure_inter_subset hopen hfar hclosed hy

/-- **Runge for simple poles**: `1/(w - y)` is uniformly near a polynomial on `E`. -/
theorem exists_poly_near_inv {E : Set ℂ} (hE : IsCompact E) (hc : IsPreconnected Eᶜ) {y : ℂ} (hy : y ∉ E) {ε : ℝ}
    (hε : 0 < ε) : ∃ p : ℂ[X], ∀ w ∈ E, ‖p.eval w - (w - y)⁻¹‖ < ε := by
  have : CompactSpace E := isCompact_iff_compactSpace.1 hE
  obtain ⟨-, f, hf, hfw⟩ := poleIn_of_compl_preconnected hE hc hy
  obtain ⟨p, hp⟩ := exists_poly_near_of_mem_closure hf hε
  refine ⟨p, fun w hw => ?_⟩
  have h1 := hp ⟨w, hw⟩
  rwa [hfw] at h1

end Smale
