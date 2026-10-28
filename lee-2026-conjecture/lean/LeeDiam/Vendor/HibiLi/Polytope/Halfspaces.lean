/-
HibiLiLean — bounded intersections of finitely many closed affine halfspaces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Polytope.FiniteFaces

open Set Filter
open scoped Topology

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {κ : Type*} [Fintype κ]

private theorem extreme_eq_of_active_eq (linear : κ → StrongDual ℝ E) (bound : κ → ℝ)
    {point other : E}
    (extreme : point ∈ extremePoints ℝ {point | ∀ index, linear index point ≤ bound index})
    (active_eq : ∀ index, linear index point = bound index → linear index other = bound index) :
    other = point := by
  have nearby : ∀ᶠ scale : ℝ in 𝓝 0, ∀ index,
      linear index (point + scale • (other - point)) ≤ bound index ∧
      linear index (point - scale • (other - point)) ≤ bound index := by
    rw [Filter.eventually_all]
    intro index
    by_cases active : linear index point = bound index
    · exact Filter.Eventually.of_forall fun scale => by
        simp [map_add, map_sub, map_smul, active, active_eq index active]
    · have strict : linear index point < bound index := lt_of_le_of_ne (extreme.1 index) active
      have plus_cont : Continuous (fun scale : ℝ => linear index (point + scale • (other - point))) := by
        fun_prop
      have minus_cont : Continuous (fun scale : ℝ => linear index (point - scale • (other - point))) := by
        fun_prop
      have plus_event : ∀ᶠ scale : ℝ in 𝓝 0,
          linear index (point + scale • (other - point)) < bound index :=
        plus_cont.continuousAt.eventually_lt_const (by simpa using strict)
      have minus_event : ∀ᶠ scale : ℝ in 𝓝 0,
          linear index (point - scale • (other - point)) < bound index :=
        minus_cont.continuousAt.eventually_lt_const (by simpa using strict)
      filter_upwards [plus_event, minus_event] with scale plus minus
      exact ⟨plus.le, minus.le⟩
  obtain ⟨radius, positive, in_ball⟩ := Metric.eventually_nhds_iff.mp nearby
  have half_positive : 0 < radius / 2 := by linarith
  have at_half := in_ball (y := radius / 2) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos half_positive]
    linarith)
  have same := extreme.2 (fun index => (at_half index).2)
    (fun index => (at_half index).1)
    (mem_openSegment_sub_add (𝕜 := ℝ) point ((radius / 2) • (other - point)))
  have scaled_zero : (radius / 2) • (other - point) = 0 := by
    exact sub_eq_self.mp same
  exact sub_eq_zero.mp ((smul_eq_zero.mp scaled_zero).resolve_left (ne_of_gt half_positive))

theorem finite_extremePoints_halfspaces (linear : κ → StrongDual ℝ E) (bound : κ → ℝ) :
    (extremePoints ℝ {point | ∀ index, linear index point ≤ bound index}).Finite := by
  classical
  let active : E → Set κ := fun point => {index | linear index point = bound index}
  apply Set.Finite.of_injOn (f := active) (t := Set.univ)
    (fun _ _ => Set.mem_univ _) ?_ Set.finite_univ
  intro point hpoint other hother same
  symm
  apply extreme_eq_of_active_eq linear bound hpoint
  intro index equality
  have member : index ∈ active point := equality
  rw [same] at member
  exact member

theorem isPolytope_halfspaces [FiniteDimensional ℝ E]
    (linear : κ → StrongDual ℝ E) (bound : κ → ℝ)
    (bounded : Bornology.IsBounded {point | ∀ index, linear index point ≤ bound index}) :
    IsPolytope {point | ∀ index, linear index point ≤ bound index} := by
  classical
  let body : Set E := {point | ∀ index, linear index point ≤ bound index}
  have body_eq : body = ⋂ index, {point | linear index point ≤ bound index} := by
    ext point
    simp [body]
  have closed : IsClosed body := by
    rw [body_eq]
    exact isClosed_iInter fun index => isClosed_le (linear index).continuous continuous_const
  have convex : Convex ℝ body := by
    rw [body_eq]
    exact convex_iInter fun index => (convex_Iic (bound index)).linear_preimage (linear index).toLinearMap
  have compact : IsCompact body := Metric.isCompact_of_isClosed_isBounded closed bounded
  have finite := finite_extremePoints_halfspaces linear bound
  refine ⟨finite.toFinset, ?_⟩
  have hull_eq := closure_convexHull_extremePoints compact convex
  rw [(finite.isClosed_convexHull ℝ).closure_eq] at hull_eq
  simpa only [Set.Finite.coe_toFinset] using hull_eq.symm

end HibiLi
