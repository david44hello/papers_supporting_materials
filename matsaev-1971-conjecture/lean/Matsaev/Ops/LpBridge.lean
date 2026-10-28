-- Matsaev/Ops/LpBridge.lean — Matsaev's conjecture (all L^p spaces) implies `MatsaevOnL2` (ℓ^p_2 = L^p(Fin 2, count)).
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Conjecture
import Matsaev.Bridge.Basic

namespace Matsaev

open scoped ENNReal
open MeasureTheory Polynomial

/-! ## `ℓ^p_2` is `L^p` of the counting measure on `Fin 2` -/

/-- On `Fin 2` with counting measure, `eLpNorm f = ‖f‖_{ℓ^p_2}` (as an extended real). -/
theorem eLpNorm_count_fin2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (f : Fin 2 → ℂ) :
    eLpNorm f p (Measure.count : Measure (Fin 2)) = ENNReal.ofReal ‖WithLp.toLp p f‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, lintegral_count, tsum_fintype,
    PiLp.norm_eq_sum hpr, ← ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun i _ => by positivity) (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  congr 2; ext i
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpr.le]
  exact (measurable_of_finite f).aestronglyMeasurable

/-- Every function on `Fin 2` is in `L^p` of the counting measure. -/
theorem memLp_count_fin2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (f : Fin 2 → ℂ) :
    MemLp f p (Measure.count : Measure (Fin 2)) :=
  memLp_iff.2 (by rw [eLpNorm_count_fin2 p hptop]; exact ENNReal.ofReal_lt_top)

/-- The linear isometry `ℓ^p_2 → L^p(Fin 2, count)`, `x ↦ [ofLp x]`. -/
noncomputable def toLpCount (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) :
    WithLp p (Fin 2 → ℂ) →ₗᵢ[ℂ] Lp ℂ p (Measure.count : Measure (Fin 2)) where
  toFun x := (memLp_count_fin2 p hptop (WithLp.ofLp x)).toLp _
  map_add' x y := by
    simp only [WithLp.ofLp_add]
    exact MemLp.toLp_add _ _
  map_smul' c x := by
    simp only [WithLp.ofLp_smul, RingHom.id_apply]
    exact MemLp.toLp_const_smul _ _
  norm_map' x := by
    change ‖(memLp_count_fin2 p hptop (WithLp.ofLp x)).toLp _‖ = ‖x‖
    rw [Lp.norm_toLp, eLpNorm_count_fin2 p hptop, WithLp.toLp_ofLp,
      ENNReal.toReal_ofReal (norm_nonneg _)]

theorem toLpCount_surjective (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) :
    Function.Surjective (toLpCount p hptop) := fun f =>
  ⟨WithLp.toLp p ⇑f, Lp.toLp_coeFn f (Lp.memLp f)⟩

/-- The linear isometric equivalence `ℓ^p_2 ≃ L^p(Fin 2, count)`. -/
noncomputable def lpCountEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) :
    WithLp p (Fin 2 → ℂ) ≃ₗᵢ[ℂ] Lp ℂ p (Measure.count : Measure (Fin 2)) :=
  LinearIsometryEquiv.ofSurjective _ (toLpCount_surjective p hptop)

/-! ## Conjugation by a linear isometric equivalence -/

/-- Conjugation `A ↦ G ∘ A ∘ G⁻¹` by a linear isometric equivalence preserves operator norms. -/
theorem norm_conj_linearIsometryEquiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (G : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    ‖G.toContinuousLinearEquiv.conjContinuousAlgEquiv A‖ = ‖A‖ := by
  rw [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp G _).trans
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv A G.symm)

/-! ## The bridge -/

/-- Matsaev's conjecture at `p` (every contraction of every `L^p(μ)`) contains its case `ℓ^p_2 = L^p(Fin 2, count)`. -/
theorem matsaevOnL2_of_conjecture (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (h : MatsaevConjecture p) :
    MatsaevOnL2 p := by
  intro T hT P
  set φ := (lpCountEquiv p hptop).toContinuousLinearEquiv.conjContinuousAlgEquiv
  have hnorm : ∀ A, ‖φ A‖ = ‖A‖ := norm_conj_linearIsometryEquiv (lpCountEquiv p hptop)
  have key := h (Fin 2) Measure.count (φ (matOp p T)) (by rw [hnorm]; exact hT) P
  rw [aeval_algHom_apply, hnorm, ← matOp_aeval] at key
  exact key

end Matsaev
