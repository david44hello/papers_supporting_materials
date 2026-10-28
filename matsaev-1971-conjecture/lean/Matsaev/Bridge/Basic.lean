-- Matsaev/Bridge/Basic.lean — basic facts on `matOp`, `matNorm`, `shiftOp`, `shiftNorm`, `Pa`, `Jmat` (Defs/).
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces

namespace Matsaev

open scoped ENNReal Matrix
open Polynomial

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Matrices on `ℓ^p_n` -/

theorem matOp_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (x : n → 𝕜) :
    matOp p A (WithLp.toLp p x) = WithLp.toLp p (A *ᵥ x) :=
  rfl

theorem norm_toLp_rpow (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) {n : Type*} [Fintype n] (x : n → 𝕜) :
    ‖WithLp.toLp p x‖ ^ p.toReal = ∑ i, ‖x i‖ ^ p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hp
  rw [PiLp.norm_eq_sum hp0, ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity),
    one_div_mul_cancel hp0.ne', Real.rpow_one]

theorem norm_toLp_fin2_rpow (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u v : ℝ) :
    ‖WithLp.toLp p ![u, v]‖ ^ p.toReal = |u| ^ p.toReal + |v| ^ p.toReal := by
  rw [norm_toLp_rpow p hp, Fin.sum_univ_two]
  simp [Real.norm_eq_abs]

theorem matNorm_nonneg (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    0 ≤ matNorm p A :=
  norm_nonneg _

theorem norm_mulVec_le_matNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜)
    (x : n → 𝕜) : ‖WithLp.toLp p (A *ᵥ x)‖ ≤ matNorm p A * ‖WithLp.toLp p x‖ := by
  rw [← matOp_toLp]
  exact (matOp p A).le_opNorm _

theorem matNorm_le_iff (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) {C : ℝ}
    (hC : 0 ≤ C) : matNorm p A ≤ C ↔ ∀ x : n → 𝕜, ‖WithLp.toLp p (A *ᵥ x)‖ ≤ C * ‖WithLp.toLp p x‖ := by
  rw [matNorm, ContinuousLinearMap.opNorm_le_iff hC]
  refine ⟨fun h x => ?_, fun h y => ?_⟩
  · simpa only [matOp_toLp] using h (WithLp.toLp p x)
  · have hy := h (WithLp.ofLp y)
    rwa [← matOp_toLp, WithLp.toLp_ofLp] at hy

/-- The operator norm of a linear map on a finite-dimensional, nontrivial space is attained on the unit sphere. -/
theorem exists_norm_eq_opNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [Nontrivial E] (T : E →L[𝕜] E) : ∃ y : E, ‖y‖ = 1 ∧ ‖T y‖ = ‖T‖ := by
  have : ProperSpace E := FiniteDimensional.proper_rclike 𝕜 E
  obtain ⟨z, hz⟩ := exists_ne (0 : E)
  have hne : (Metric.sphere (0 : E) 1).Nonempty := ⟨_, by simpa using norm_smul_inv_norm (𝕜 := 𝕜) hz⟩
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hne
    (continuous_norm.comp T.continuous).continuousOn
  have hy1 : ‖y‖ = 1 := by simpa using hy
  refine ⟨y, hy1, le_antisymm ?_ ?_⟩
  · simpa [hy1] using T.le_opNorm y
  · refine ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun z hz => ?_
    exact hmax (by simpa using hz)

theorem exists_eq_matNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n 𝕜) : ∃ x : n → 𝕜, ‖WithLp.toLp p x‖ = 1 ∧ ‖WithLp.toLp p (A *ᵥ x)‖ = matNorm p A := by
  obtain ⟨y, hy, hA⟩ := exists_norm_eq_opNorm (matOp p A)
  refine ⟨WithLp.ofLp y, by simpa using hy, ?_⟩
  rw [← matOp_toLp, WithLp.toLp_ofLp, hA, matNorm]

theorem matOp_aeval (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (P : 𝕜[X]) :
    matOp p (aeval A P) = aeval (matOp p A) P :=
  aeval_algHom_apply ((Matrix.toLpLinAlgEquiv p).trans
    (Module.End.toContinuousLinearMap (WithLp p (n → 𝕜)))).toAlgHom A P |>.symm

/-! ## The rotation `J` and the polynomial `P_a` -/

theorem Jmat_mulVec (u v : 𝕜) : (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ ![u, v] = ![v, -u] := by
  ext i
  fin_cases i <;> simp [Jmat]

theorem Jmat_mul_Jmat : (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) * Jmat = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jmat]

theorem aeval_Jmat_Pa_proved {𝕜 : Type} [RCLike 𝕜] (a B : 𝕜) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) (Pa a B) = (1 + B) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) + a • Jmat := by
  simp only [Pa, map_add, map_sub, map_one, map_mul, aeval_C, aeval_X, sq, Jmat_mul_Jmat,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_neg]
  module

/-! ## The shift on `ℓ^p(ℕ)` -/

theorem shiftOp_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : lp (fun _ : ℕ => 𝕜) p) (n : ℕ) :
    shiftOp p 𝕜 x n = shiftSeq (⇑x) n :=
  rfl

theorem aeval_shiftOp_Pa_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B : 𝕜) (x : lp (fun _ : ℕ => 𝕜) p) (n : ℕ) :
    aeval (shiftOp p 𝕜) (Pa a B) x n = x n + a * shiftSeq (⇑x) n - B * shiftSeq (shiftSeq ⇑x) n := by
  simp only [Pa, map_add, map_sub, map_one, map_mul, aeval_C, aeval_X, sq,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, _root_.add_apply, _root_.sub_apply, _root_.smul_apply,
    one_apply_eq_self, mul_apply_eq_comp, lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, shiftOp_apply]
  rfl

theorem norm_shiftOp_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : lp (fun _ : ℕ => 𝕜) p) : ‖shiftOp p 𝕜 x‖ = ‖x‖ := by
  refine le_antisymm (by simpa [shiftOp] using norm_shiftLin_le p x) ?_
  obtain (hp0 | rfl | hp) := p.trichotomy
  · exact absurd (hp0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by simp)
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (shiftOp ⊤ 𝕜 x) (n + 1)
  · refine lp.norm_le_of_tsum_le hp (norm_nonneg _) ?_
    have hs : Summable fun n => ‖shiftOp p 𝕜 x n‖ ^ p.toReal := (lp.memℓp (shiftOp p 𝕜 x)).summable hp
    rw [lp.norm_rpow_eq_tsum hp (shiftOp p 𝕜 x), hs.tsum_eq_zero_add]
    simp [shiftOp_apply, shiftSeq, Real.zero_rpow hp.ne']

theorem shiftNorm_le_iff (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : 𝕜[X]) {C : ℝ} (hC : 0 ≤ C) :
    shiftNorm p 𝕜 P ≤ C ↔ ∀ x : lp (fun _ : ℕ => 𝕜) p, ‖aeval (shiftOp p 𝕜) P x‖ ≤ C * ‖x‖ :=
  ContinuousLinearMap.opNorm_le_iff hC

end Matsaev
