/-
HibiLi/Example21/IntervalDecomposition.lean — interval indicators give finite convex-hull representations.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Example21.FiniteHull

namespace HibiLi

open MeasureTheory Set

noncomputable def intervalVector {P : Type*} (start finish : P → ℝ) (time : ℝ) : P → ℝ :=
  fun pp => (Ioc (start pp) (finish pp)).indicator (fun _ => (1 : ℝ)) time

theorem intervalVector_zero_one {P : Type*} (start finish : P → ℝ) (time : ℝ) (pp : P) :
    intervalVector start finish time pp = 0 ∨ intervalVector start finish time pp = 1 := by
  classical
  by_cases hh : time ∈ Ioc (start pp) (finish pp) <;> simp [intervalVector, hh]

theorem intervalVector_convexHull {P : Type*} [Fintype P]
    (start finish : P → ℝ) (hstart : ∀ pp, 0 ≤ start pp)
    (horder : ∀ pp, start pp ≤ finish pp) (hfinish : ∀ pp, finish pp ≤ 1)
    {vertices : Set (P → ℝ)} (hfinite : vertices.Finite)
    (hvertices : ∀ time ∈ Ioc (0 : ℝ) 1, intervalVector start finish time ∈ vertices) :
    (fun pp => finish pp - start pp) ∈ convexHull ℝ vertices := by
  let measure : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsProbabilityMeasure measure := ⟨by simp [measure, Real.volume_Ioc]⟩
  have hintegrable (pp : P) : Integrable (fun time => intervalVector start finish time pp) measure :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioc
  have haverage : (∫ time, intervalVector start finish time ∂measure) =
      (fun pp => finish pp - start pp) := by
    ext pp
    rw [eval_integral hintegrable pp]
    change (∫ time, (Ioc (start pp) (finish pp)).indicator (fun _ => (1 : ℝ)) time ∂measure) = _
    rw [integral_indicator_const _ measurableSet_Ioc, smul_eq_mul, mul_one]
    change (volume.restrict (Ioc (0 : ℝ) 1)).real (Ioc (start pp) (finish pp)) = _
    rw [measureReal_restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Ioc (hstart pp) (hfinish pp)),
      Real.volume_real_Ioc_of_le (horder pp)]
  rw [← haverage]
  apply (convex_convexHull ℝ vertices).integral_mem (hfinite.isClosed_convexHull ℝ)
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with time htime
    exact subset_convexHull ℝ vertices (hvertices time htime)
  · exact integrable_pi_iff.mpr hintegrable

end HibiLi
