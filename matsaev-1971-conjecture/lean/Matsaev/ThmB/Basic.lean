/-
Matsaev/ThmB/Basic.lean — Theorem B and Corollary 5.1 of the paper (Section 5): for `P(z) = c₀ + c₁z + c₂z²` with
`|c₀| = |c₂|`, `‖P(T)‖_p ≤ ‖P(S)‖_p` for every contraction `T` of every `L^p` space (`1 ≤ p ≤ ∞`), and the exact value
`‖P(S)‖_p = ‖P(ζ̄J)‖_p = max_{|μ|=1} ‖P(μJ)‖_p`. Author: Dave Goel.

Route = the paper's: `P(z) = c₀ P̃(ζz)`, `P̃(z) = 1 + αz - z²` (`aeval_quad_eq`); `P̃(T)x = ½(2x + αTx) + ½T(αx - 2Tx)`
(`aeval_Pa_one_apply`); convexity of `t^p` and `‖T‖ ≤ 1` (`key_le`, `key_le_top`); the pointwise matrix bound integrated
over `Ω` (`pair_le_Lp`, `pair_le_Lp_top`; `pair_le_lp*` on `ℓ^p(ℕ)`); `‖P̃(J)‖ ≤ ‖P̃(S)‖` (Lemma 2.2); `‖Q(ζS)‖ = ‖Q(S)‖`
by the isometry `diag(ζ^n)` (`norm_aeval_smul_shift`). The paper uses `M = V P̃(J)`; Lean uses the rows of `P̃(J)` itself
(the second row is `-(αx - 2Tx)`), which gives the same bound.
-/
import Matsaev.Bridge.Basic
import Matsaev.Assembly.LpNat
import Matsaev.Ops.JLower
import Mathlib.MeasureTheory.Function.LpSpace.Basic

namespace Matsaev.ThmB

open Matsaev MeasureTheory
open scoped ENNReal Matrix
open Polynomial

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The pointwise bound: `‖A₀₀a + A₀₁b‖^q + ‖A₁₀a + A₁₁b‖^q ≤ ‖A‖^q (‖a‖^q + ‖b‖^q)` on `ℓ^p_2`, `p < ∞`. -/
theorem pointwise_le (hptop : p ≠ ⊤) (A : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    ‖A 0 0 * a + A 0 1 * b‖ ^ p.toReal + ‖A 1 0 * a + A 1 1 * b‖ ^ p.toReal ≤
      matNorm p A ^ p.toReal * (‖a‖ ^ p.toReal + ‖b‖ ^ p.toReal) := by
  have h := norm_mulVec_le_matNorm p A ![a, b]
  have hq : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have h' := Real.rpow_le_rpow (norm_nonneg _) h hq
  rw [Real.mul_rpow (matNorm_nonneg _ _) (norm_nonneg _), norm_toLp_rpow p hptop, norm_toLp_rpow p hptop] at h'
  simpa [Fin.sum_univ_two, Matrix.mulVec, dotProduct] using h'

/-- For `f ∈ L^p`, `p < ∞`: `‖f‖^p = ∫ ‖f‖^p` (as an extended real). -/
theorem ofReal_norm_rpow_Lp (hptop : p ≠ ⊤) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f : Lp ℂ p μ) :
    ENNReal.ofReal (‖f‖ ^ p.toReal) = ∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hfin : ∫⁻ ω, ‖f ω‖ₑ ^ p.toReal ∂μ ≠ ⊤ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop (Lp.eLpNorm_lt_top f)).ne
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop (Lp.aestronglyMeasurable f),
    ← ENNReal.toReal_rpow, ← Real.rpow_mul ENNReal.toReal_nonneg, one_div, inv_mul_cancel₀ hq.ne', Real.rpow_one,
    ENNReal.ofReal_toReal hfin]

/-- The pair bound on `L^p(μ)`, `p < ∞`: `‖A₀₀x + A₀₁y‖^q + ‖A₁₀x + A₁₁y‖^q ≤ ‖A‖^q (‖x‖^q + ‖y‖^q)`. -/
theorem pair_le_Lp (hptop : p ≠ ⊤) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : Lp ℂ p μ) :
    ‖A 0 0 • x + A 0 1 • y‖ ^ p.toReal + ‖A 1 0 • x + A 1 1 • y‖ ^ p.toReal ≤
      matNorm p A ^ p.toReal * (‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) := by
  set q := p.toReal with hqdef
  have hq0 : 0 ≤ q := ENNReal.toReal_nonneg
  set K := matNorm p A ^ q with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (matNorm_nonneg _ _) _
  have hrhs : 0 ≤ K * (‖x‖ ^ q + ‖y‖ ^ q) := by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hrhs, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul hK0, ENNReal.ofReal_add (by positivity) (by positivity),
    ofReal_norm_rpow_Lp p hptop, ofReal_norm_rpow_Lp p hptop, ofReal_norm_rpow_Lp p hptop,
    ofReal_norm_rpow_Lp p hptop]
  have hu := Lp.coeFn_add (A 0 0 • x) (A 0 1 • y)
  have hv := Lp.coeFn_add (A 1 0 • x) (A 1 1 • y)
  have h1 := Lp.coeFn_smul (A 0 0) x
  have h2 := Lp.coeFn_smul (A 0 1) y
  have h3 := Lp.coeFn_smul (A 1 0) x
  have h4 := Lp.coeFn_smul (A 1 1) y
  have hpt : ∀ᵐ ω ∂μ, ‖(A 0 0 • x + A 0 1 • y) ω‖ₑ ^ q + ‖(A 1 0 • x + A 1 1 • y) ω‖ₑ ^ q ≤
      ENNReal.ofReal K * (‖x ω‖ₑ ^ q + ‖y ω‖ₑ ^ q) := by
    filter_upwards [hu, hv, h1, h2, h3, h4] with ω e1 e2 e3 e4 e5 e6
    rw [e1, e2, Pi.add_apply, Pi.add_apply, e3, e4, e5, e6]
    simp only [Pi.smul_apply, smul_eq_mul]
    have key := pointwise_le p hptop A (x ω) (y ω)
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul hK0]
    exact ENNReal.ofReal_le_ofReal key
  calc ∫⁻ ω, ‖(A 0 0 • x + A 0 1 • y) ω‖ₑ ^ q ∂μ + ∫⁻ ω, ‖(A 1 0 • x + A 1 1 • y) ω‖ₑ ^ q ∂μ
      = ∫⁻ ω, (‖(A 0 0 • x + A 0 1 • y) ω‖ₑ ^ q + ‖(A 1 0 • x + A 1 1 • y) ω‖ₑ ^ q) ∂μ := by
        rw [lintegral_add_left' ((Lp.aestronglyMeasurable _).enorm.pow_const _)]
    _ ≤ ∫⁻ ω, ENNReal.ofReal K * (‖x ω‖ₑ ^ q + ‖y ω‖ₑ ^ q) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal K * (∫⁻ ω, ‖x ω‖ₑ ^ q ∂μ + ∫⁻ ω, ‖y ω‖ₑ ^ q ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left' ((Lp.aestronglyMeasurable _).enorm.pow_const _)]



/-- The diagonal map `x ↦ (μ^n x_n)_n` on `ℓ^p(ℕ)` for `‖μ‖ = 1`, as a linear map. -/
noncomputable def diagLin (μ : ℂ) (hμ : ‖μ‖ = 1) : lp (fun _ : ℕ => ℂ) p →ₗ[ℂ] lp (fun _ : ℕ => ℂ) p where
  toFun x := ⟨fun n => μ ^ n * x n, by
    have h : (fun n => ‖μ ^ n * x n‖) = fun n => ‖x n‖ := by
      funext n; rw [norm_mul, norm_pow, hμ, one_pow, one_mul]
    have hx : Memℓp (fun n => ‖x n‖) p := (memℓp_norm_iff).mpr (lp.memℓp x)
    exact (memℓp_norm_iff).mp (h ▸ hx)⟩
  map_add' x y := by
    ext n
    change μ ^ n * (x + y) n = μ ^ n * x n + μ ^ n * y n
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c x := by ext n; simp; ring

omit [Fact (1 ≤ p)] in
theorem diagLin_apply (μ : ℂ) (hμ : ‖μ‖ = 1) (x : lp (fun _ : ℕ => ℂ) p) (n : ℕ) :
    diagLin p μ hμ x n = μ ^ n * x n := rfl

theorem norm_diagLin (μ : ℂ) (hμ : ‖μ‖ = 1) (x : lp (fun _ : ℕ => ℂ) p) : ‖diagLin p μ hμ x‖ = ‖x‖ := by
  have h : ∀ n, ‖diagLin p μ hμ x n‖ = ‖x n‖ := fun n => by
    rw [diagLin_apply, norm_mul, norm_pow, hμ, one_pow, one_mul]
  obtain (hp0 | rfl | hp) := p.trichotomy
  · exact absurd (hp0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by simp)
  · rw [lp.norm_eq_ciSup, lp.norm_eq_ciSup]; simp only [h]
  · rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]; simp only [h]

/-- The isometry `U_μ = diag(μ^n)` of `ℓ^p(ℕ)`. -/
noncomputable def diag (μ : ℂ) (hμ : ‖μ‖ = 1) : lp (fun _ : ℕ => ℂ) p →L[ℂ] lp (fun _ : ℕ => ℂ) p :=
  (diagLin p μ hμ).mkContinuous 1 fun x => by rw [norm_diagLin, one_mul]

/-- `(μ c S) U_μ = U_μ (c S)`. -/
theorem smul_shift_comp_diag (μ : ℂ) (hμ : ‖μ‖ = 1) (c : ℂ) :
    ((μ * c) • shiftOp p ℂ).comp (diag p μ hμ) = (diag p μ hμ).comp (c • shiftOp p ℂ) := by
  ext x n
  change (μ * c) * (shiftLin p ℂ (diagLin p μ hμ x)) n = μ ^ n * (c * shiftLin p ℂ x n)
  cases n with
  | zero => simp [shiftLin_apply_zero]
  | succ k => rw [shiftLin_apply_succ, shiftLin_apply_succ, diagLin_apply, pow_succ]; ring

/-- `‖Q(ζS)‖ = ‖Q(S)‖` for `‖ζ‖ = 1` (conjugation by `diag(ζ^n)`). -/
theorem norm_aeval_smul_shift (ζ : ℂ) (hζ : ‖ζ‖ = 1) (Q : ℂ[X]) :
    ‖aeval (ζ • shiftOp p ℂ) Q‖ = ‖aeval (shiftOp p ℂ) Q‖ := by
  have hζc : ‖(starRingEnd ℂ) ζ‖ = 1 := by rw [Complex.norm_conj, hζ]
  have h1 : (ζ • shiftOp p ℂ).comp (diag p ζ hζ) = (diag p ζ hζ).comp (shiftOp p ℂ) := by
    have := smul_shift_comp_diag p ζ hζ 1
    rwa [mul_one, one_smul] at this
  have h2 : (shiftOp p ℂ).comp (diag p _ hζc) = (diag p _ hζc).comp (ζ • shiftOp p ℂ) := by
    have := smul_shift_comp_diag p _ hζc ζ
    have hcz : (starRingEnd ℂ) ζ * ζ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    rwa [hcz, one_smul] at this
  have hiso : ∀ (μ : ℂ) (hμ : ‖μ‖ = 1) (x : lp (fun _ : ℕ => ℂ) p), ‖diag p μ hμ x‖ = ‖x‖ :=
    fun μ hμ x => norm_diagLin p μ hμ x
  refine le_antisymm ?_ ?_
  · exact LpNat.opNorm_le_of_intertwine _ _ _ (hiso _ hζc) (LpNat.aeval_comp_intertwine _ _ _ h2 Q)
  · exact LpNat.opNorm_le_of_intertwine _ _ _ (hiso _ hζ) (LpNat.aeval_comp_intertwine _ _ _ h1 Q)

/-- The pair bound on `ℓ^p(ℕ)`, `p < ∞`. -/
theorem pair_le_lp (hptop : p ≠ ⊤) (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : lp (fun _ : ℕ => ℂ) p) :
    ‖A 0 0 • x + A 0 1 • y‖ ^ p.toReal + ‖A 1 0 • x + A 1 1 • y‖ ^ p.toReal ≤
      matNorm p A ^ p.toReal * (‖x‖ ^ p.toReal + ‖y‖ ^ p.toReal) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have sm : ∀ f : lp (fun _ : ℕ => ℂ) p, Summable fun n => ‖f n‖ ^ p.toReal := fun f => (lp.memℓp f).summable hq
  rw [lp.norm_rpow_eq_tsum hq, lp.norm_rpow_eq_tsum hq, lp.norm_rpow_eq_tsum hq, lp.norm_rpow_eq_tsum hq,
    ← (sm _).tsum_add (sm _), ← (sm x).tsum_add (sm y), ← tsum_mul_left]
  refine ((sm _).add (sm _)).tsum_le_tsum (fun n => ?_) (((sm x).add (sm y)).mul_left _)
  have key := pointwise_le p hptop A (x n) (y n)
  change ‖A 0 0 * x n + A 0 1 * y n‖ ^ p.toReal + ‖A 1 0 * x n + A 1 1 * y n‖ ^ p.toReal ≤ _
  exact key



/-- The pointwise bound for `p = ∞`: each row of `A` applied to `(a, b)` is at most `‖A‖ · max(‖a‖, ‖b‖)`. -/
theorem pointwise_le_top (A : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (i : Fin 2) :
    ‖A i 0 * a + A i 1 * b‖ ≤ matNorm ⊤ A * max ‖a‖ ‖b‖ := by
  have h := norm_mulVec_le_matNorm ⊤ A ![a, b]
  have hv : ‖WithLp.toLp ⊤ ![a, b]‖ ≤ max ‖a‖ ‖b‖ := by
    rw [PiLp.norm_eq_ciSup]
    refine ciSup_le fun j => ?_
    fin_cases j
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hi : ‖A i 0 * a + A i 1 * b‖ ≤ ‖WithLp.toLp ⊤ (A *ᵥ ![a, b])‖ := by
    have := PiLp.norm_apply_le (WithLp.toLp ⊤ (A *ᵥ ![a, b])) i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  calc _ ≤ _ := hi
    _ ≤ matNorm ⊤ A * ‖WithLp.toLp ⊤ ![a, b]‖ := h
    _ ≤ matNorm ⊤ A * max ‖a‖ ‖b‖ := mul_le_mul_of_nonneg_left hv (matNorm_nonneg _ _)

/-- The pair bound on `L^∞(μ)`: `‖A_{i0} x + A_{i1} y‖ ≤ ‖A‖ · max(‖x‖, ‖y‖)`. -/
theorem pair_le_Lp_top {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : MeasureTheory.Lp ℂ ⊤ μ) (i : Fin 2) :
    ‖A i 0 • x + A i 1 • y‖ ≤ matNorm ⊤ A * max ‖x‖ ‖y‖ := by
  have hC : 0 ≤ matNorm ⊤ A * max ‖x‖ ‖y‖ := mul_nonneg (matNorm_nonneg _ _) (le_max_of_le_left (norm_nonneg _))
  have hx : ∀ᵐ ω ∂μ, ‖x ω‖ ≤ ‖x‖ := MeasureTheory.ae_le_lpNorm_exponent_top (MeasureTheory.Lp.memLp x)
  have hy : ∀ᵐ ω ∂μ, ‖y ω‖ ≤ ‖y‖ := MeasureTheory.ae_le_lpNorm_exponent_top (MeasureTheory.Lp.memLp y)
  have hb : ∀ᵐ ω ∂μ, ‖(A i 0 • x + A i 1 • y) ω‖ ≤ matNorm ⊤ A * max ‖x‖ ‖y‖ := by
    filter_upwards [hx, hy, MeasureTheory.Lp.coeFn_add (A i 0 • x) (A i 1 • y),
      MeasureTheory.Lp.coeFn_smul (A i 0) x, MeasureTheory.Lp.coeFn_smul (A i 1) y] with ω h1 h2 e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3]
    simp only [Pi.smul_apply, smul_eq_mul]
    refine (pointwise_le_top A (x ω) (y ω) i).trans ?_
    exact mul_le_mul_of_nonneg_left (max_le_max h1 h2) (matNorm_nonneg _ _)
  rw [MeasureTheory.Lp.norm_def, MeasureTheory.eLpNorm_exponent_top (MeasureTheory.Lp.aestronglyMeasurable _)]
  exact ENNReal.toReal_le_of_le_ofReal hC (MeasureTheory.eLpNormEssSup_le_of_ae_bound hb)

/-- The pair bound on `ℓ^∞(ℕ)`. -/
theorem pair_le_lp_top (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : lp (fun _ : ℕ => ℂ) ⊤) (i : Fin 2) :
    ‖A i 0 • x + A i 1 • y‖ ≤ matNorm ⊤ A * max ‖x‖ ‖y‖ := by
  have hC : 0 ≤ matNorm ⊤ A * max ‖x‖ ‖y‖ := mul_nonneg (matNorm_nonneg _ _) (le_max_of_le_left (norm_nonneg _))
  refine lp.norm_le_of_forall_le hC fun n => ?_
  change ‖A i 0 * x n + A i 1 * y n‖ ≤ _
  refine (pointwise_le_top A (x n) (y n) i).trans ?_
  exact mul_le_mul_of_nonneg_left (max_le_max (lp.norm_apply_le_norm ENNReal.top_ne_zero x n)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero y n)) (matNorm_nonneg _ _)

/-- `P̃(T) x = ½ (2x + αTx) + ½ T(αx - 2Tx)` for `P̃(z) = 1 + αz - z²` (`= Pa α 1`). -/
theorem aeval_Pa_one_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (α : ℂ) (T : X →L[ℂ] X) (x : X) :
    aeval T (Pa α 1) x = (1 / 2 : ℂ) • ((2 : ℂ) • x + α • T x) + (1 / 2 : ℂ) • T (α • x - (2 : ℂ) • T x) := by
  simp only [Pa, map_sub, map_add, map_one, map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
    sub_apply, add_apply, one_apply_eq_self, mul_apply_eq_comp, smul_apply, sq, map_smul, map_sub]
  module

/-- The contraction step, `p < ∞` (`q = p`): if every pair satisfies the bound with constant `K`, then
`‖P̃(T)‖ ≤ K` for every contraction `T`. -/
theorem key_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (q : ℝ) (hq : 1 ≤ q) (α : ℂ)
    (T : X →L[ℂ] X) (hT : ‖T‖ ≤ 1) (K : ℝ) (hK : 0 ≤ K)
    (hpair : ∀ x y : X, ‖(2 : ℂ) • x + α • y‖ ^ q + ‖(-α) • x + (2 : ℂ) • y‖ ^ q ≤ K ^ q * (‖x‖ ^ q + ‖y‖ ^ q)) :
    ‖aeval T (Pa α 1)‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  set y := T x
  set u := (2 : ℂ) • x + α • y
  set v := α • x - (2 : ℂ) • y
  have hy : ‖y‖ ≤ ‖x‖ := (T.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  have hv : ‖v‖ = ‖(-α) • x + (2 : ℂ) • y‖ := by
    rw [← norm_neg]; congr 1; simp only [v, neg_sub, neg_smul]; abel
  have hTv : ‖T v‖ ≤ ‖v‖ := (T.le_opNorm v).trans (by nlinarith [norm_nonneg v])
  have h1 : ‖aeval T (Pa α 1) x‖ ≤ (1 / 2) * ‖u‖ + (1 / 2) * ‖v‖ := by
    rw [aeval_Pa_one_apply]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    linarith
  have hq0 : 0 < q := by linarith
  have hconv : ((1 / 2) * ‖u‖ + (1 / 2) * ‖v‖) ^ q ≤ (1 / 2) * ‖u‖ ^ q + (1 / 2) * ‖v‖ ^ q := by
    have := (convexOn_rpow hq).2 (Set.mem_Ici.mpr (norm_nonneg u)) (Set.mem_Ici.mpr (norm_nonneg v))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [smul_eq_mul] using this
  have hp := hpair x y
  rw [← hv] at hp
  have hyq : ‖y‖ ^ q ≤ ‖x‖ ^ q := Real.rpow_le_rpow (norm_nonneg _) hy hq0.le
  have hKq : 0 ≤ K ^ q := Real.rpow_nonneg hK _
  have hfin : ‖aeval T (Pa α 1) x‖ ^ q ≤ (K * ‖x‖) ^ q := by
    rw [Real.mul_rpow hK (norm_nonneg _)]
    calc ‖aeval T (Pa α 1) x‖ ^ q ≤ ((1 / 2) * ‖u‖ + (1 / 2) * ‖v‖) ^ q :=
          Real.rpow_le_rpow (norm_nonneg _) h1 hq0.le
      _ ≤ (1 / 2) * ‖u‖ ^ q + (1 / 2) * ‖v‖ ^ q := hconv
      _ ≤ (1 / 2) * (K ^ q * (‖x‖ ^ q + ‖y‖ ^ q)) := by linarith
      _ ≤ K ^ q * ‖x‖ ^ q := by nlinarith
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hK (norm_nonneg _)) hq0).mp hfin

/-- The contraction step, `p = ∞`. -/
theorem key_le_top {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (α : ℂ)
    (T : X →L[ℂ] X) (hT : ‖T‖ ≤ 1) (K : ℝ) (hK : 0 ≤ K)
    (hpair : ∀ x y : X, ‖(2 : ℂ) • x + α • y‖ ≤ K * max ‖x‖ ‖y‖ ∧ ‖(-α) • x + (2 : ℂ) • y‖ ≤ K * max ‖x‖ ‖y‖) :
    ‖aeval T (Pa α 1)‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  set y := T x
  have hy : ‖y‖ ≤ ‖x‖ := (T.le_opNorm x).trans (by nlinarith [norm_nonneg x])
  have hv : ‖α • x - (2 : ℂ) • y‖ = ‖(-α) • x + (2 : ℂ) • y‖ := by
    rw [← norm_neg]; congr 1; simp only [neg_sub, neg_smul]; abel
  have hTv : ‖T (α • x - (2 : ℂ) • y)‖ ≤ ‖α • x - (2 : ℂ) • y‖ :=
    (T.le_opNorm _).trans (by nlinarith [norm_nonneg (α • x - (2 : ℂ) • y)])
  obtain ⟨h1, h2⟩ := hpair x y
  have hmax : max ‖x‖ ‖y‖ = ‖x‖ := max_eq_left hy
  rw [hmax] at h1 h2
  have hTv' : ‖T (α • x - (2 : ℂ) • y)‖ ≤ K * ‖x‖ := hTv.trans (by rw [hv]; exact h2)
  rw [aeval_Pa_one_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul]
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [this]
  linarith



/-- `P(z) = c₀ P̃(ζz)` with `P̃ = Pa α 1 = 1 + αz - z²`, `α = c₁/(c₀ζ)`, when `ζ² = -c₂/c₀` (any `ℂ`-algebra). -/
theorem aeval_quad_eq {R : Type*} [Ring R] [Algebra ℂ R] (r : R) (c₀ c₁ c₂ ζ : ℂ) (hc₀ : c₀ ≠ 0) (hζ0 : ζ ≠ 0)
    (hζ : ζ ^ 2 = -c₂ / c₀) :
    aeval r (C c₀ + C c₁ * X + C c₂ * X ^ 2) = c₀ • aeval (ζ • r) (Pa (c₁ / (c₀ * ζ)) 1) := by
  have e1 : aeval r (C c₀ + C c₁ * X + C c₂ * X ^ 2) = c₀ • (1 : R) + c₁ • r + c₂ • r ^ 2 := by
    simp [Algebra.algebraMap_eq_smul_one]
  have e2 : aeval (ζ • r) (Pa (c₁ / (c₀ * ζ)) 1) = (1 : R) + (c₁ / (c₀ * ζ) * ζ) • r - (ζ ^ 2) • r ^ 2 := by
    simp [Pa, Algebra.algebraMap_eq_smul_one, smul_smul]
    rw [_root_.smul_pow, mul_comm ζ]
  have h1 : c₀ * (c₁ / (c₀ * ζ) * ζ) = c₁ := by field_simp
  have h2 : c₀ * ζ ^ 2 = -c₂ := by rw [hζ]; field_simp
  rw [e1, e2, smul_sub, smul_add, smul_smul, smul_smul, h1, h2, neg_smul, sub_neg_eq_add]

/-- The entries of `P̃(J) = 2I + αJ`. -/
theorem aeval_Jmat_Pa_one_entries (α : ℂ) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1) 0 0 = 2 ∧ aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1) 0 1 = α ∧
      aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1) 1 0 = -α ∧
        aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1) 1 1 = 2 := by
  rw [Matsaev.aeval_Jmat_Pa_proved]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Jmat] <;> norm_num

theorem one_le_toReal (hptop : p ≠ ⊤) : 1 ≤ p.toReal := by
  have h := ENNReal.toReal_mono hptop (Fact.out : (1 : ℝ≥0∞) ≤ p)
  simpa using h

/-- The key inequality on every `L^p(μ)`, `1 ≤ p ≤ ∞`: `‖P̃(T)‖ ≤ ‖P̃(J)‖` for every contraction `T`. -/
theorem key_Lp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (α : ℂ) (T : Lp ℂ p μ →L[ℂ] Lp ℂ p μ)
    (hT : ‖T‖ ≤ 1) : ‖aeval T (Pa α 1)‖ ≤ matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) := by
  obtain ⟨e00, e01, e10, e11⟩ := aeval_Jmat_Pa_one_entries α
  by_cases hptop : p = ⊤
  · subst hptop
    refine key_le_top α T hT _ (matNorm_nonneg _ _) fun x y => ⟨?_, ?_⟩
    · have h := pair_le_Lp_top (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) x y 0
      rwa [e00, e01] at h
    · have h := pair_le_Lp_top (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) x y 1
      rwa [e10, e11] at h
  · refine key_le p.toReal (one_le_toReal p hptop) α T hT _ (matNorm_nonneg _ _) fun x y => ?_
    have h := pair_le_Lp p hptop (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) x y
    rwa [e00, e01, e10, e11] at h

/-- The key inequality on `ℓ^p(ℕ)`, `1 ≤ p ≤ ∞`. -/
theorem key_lp (α : ℂ) (T : lp (fun _ : ℕ => ℂ) p →L[ℂ] lp (fun _ : ℕ => ℂ) p) (hT : ‖T‖ ≤ 1) :
    ‖aeval T (Pa α 1)‖ ≤ matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) := by
  obtain ⟨e00, e01, e10, e11⟩ := aeval_Jmat_Pa_one_entries α
  by_cases hptop : p = ⊤
  · subst hptop
    refine key_le_top α T hT _ (matNorm_nonneg _ _) fun x y => ⟨?_, ?_⟩
    · have h := pair_le_lp_top (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) x y 0
      rwa [e00, e01] at h
    · have h := pair_le_lp_top (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) x y 1
      rwa [e10, e11] at h
  · refine key_le p.toReal (one_le_toReal p hptop) α T hT _ (matNorm_nonneg _ _) fun x y => ?_
    have h := pair_le_lp p hptop (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1)) x y
    rwa [e00, e01, e10, e11] at h

/-- `S e₀ = e₁`. -/
theorem shiftOp_single_zero : shiftOp p ℂ (lp.single p 0 (1 : ℂ)) = lp.single p 1 (1 : ℂ) := by
  ext n
  change shiftLin p ℂ (lp.single p 0 (1 : ℂ)) n = _
  cases n with
  | zero => simp [shiftLin_apply_zero]
  | succ k =>
    rw [shiftLin_apply_succ, lp.single_apply, lp.single_apply]
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]

/-- `‖c S‖ ≥ |c|` (test on `e₀`). -/
theorem norm_le_norm_smul_shift (c : ℂ) : ‖c‖ ≤ ‖c • shiftOp p ℂ‖ := by
  have hp0 : 0 < p := zero_lt_one.trans_le Fact.out
  have h := (c • shiftOp p ℂ).le_opNorm (lp.single p 0 (1 : ℂ))
  rw [smul_apply, shiftOp_single_zero, norm_smul, lp.norm_single hp0, lp.norm_single hp0,
    norm_one, mul_one, mul_one] at h
  exact h

/-- **Theorem B** (`thm:B`): for `P(z) = c₀ + c₁z + c₂z²` with `|c₀| = |c₂|`, `‖P(T)‖ ≤ ‖P(S)‖_p` for every
`1 ≤ p ≤ ∞` and every contraction `T` of every `L^p` space. -/
theorem theorem_B_proved (c₀ c₁ c₂ : ℂ) (hc : ‖c₀‖ = ‖c₂‖) (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
    (T : Lp ℂ p μ →L[ℂ] Lp ℂ p μ) (hT : ‖T‖ ≤ 1) :
    ‖aeval T (C c₀ + C c₁ * X + C c₂ * X ^ 2)‖ ≤ shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2) := by
  by_cases hc₀ : c₀ = 0
  · -- degree at most one
    have hc₂ : c₂ = 0 := by rw [hc₀, norm_zero] at hc; exact norm_eq_zero.mp hc.symm
    subst hc₀; subst hc₂
    have hP : (C 0 + C c₁ * X + C 0 * X ^ 2 : ℂ[X]) = C c₁ * X := by simp
    rw [shiftNorm, hP]
    simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    calc ‖c₁ • T‖ ≤ ‖c₁‖ * ‖T‖ := (norm_smul c₁ T).le
      _ ≤ ‖c₁‖ := by nlinarith [norm_nonneg c₁]
      _ ≤ ‖c₁ • shiftOp p ℂ‖ := norm_le_norm_smul_shift p c₁
  · -- `P(z) = c₀ P̃(ζz)`
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-c₂ / c₀) (by norm_num : 0 < 2)
    have hnζ : ‖ζ‖ = 1 := by
      have h := congrArg norm hζ
      rw [norm_pow, norm_div, norm_neg, ← hc, div_self (norm_ne_zero_iff.mpr hc₀)] at h
      have h0 : 0 ≤ ‖ζ‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖ζ‖ - 1), sq_nonneg (‖ζ‖ + 1)]
    have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hnζ; exact zero_ne_one hnζ
    set α := c₁ / (c₀ * ζ)
    have hTζ : ‖ζ • T‖ ≤ 1 := by rw [norm_smul, hnζ, one_mul]; exact hT
    rw [shiftNorm, aeval_quad_eq T c₀ c₁ c₂ ζ hc₀ hζ0 hζ, aeval_quad_eq (shiftOp p ℂ) c₀ c₁ c₂ ζ hc₀ hζ0 hζ,
      norm_smul, norm_smul, norm_aeval_smul_shift p ζ hnζ]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (key_Lp p μ α (ζ • T) hTζ).trans (Matsaev.lemma_2_2_proved p (Pa α 1))



theorem norm_shiftOp_le : ‖shiftOp p ℂ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `‖c M‖ = |c| ‖M‖` for complex `2 × 2` matrices. -/
theorem matNorm_smul_complex (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) : matNorm p (c • M) = ‖c‖ * matNorm p M := by
  have h : matOp p (c • M) = c • matOp p M := by simp only [matOp, map_smul]
  rw [matNorm, matNorm, h, norm_smul]

/-- `‖P(μJ)‖_p ≤ ‖P(S)‖_p` for every `|μ| = 1` (Lemma 2.2 for `z ↦ P(μz)` and `‖P(μS)‖ = ‖P(S)‖`). -/
theorem matNorm_aeval_smul_Jmat_le (P : ℂ[X]) (μ : ℂ) (hμ : ‖μ‖ = 1) :
    matNorm p (aeval (μ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) P) ≤ shiftNorm p ℂ P := by
  have hJ : aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (C μ * X) = μ • Jmat := by
    simp [Algebra.algebraMap_eq_smul_one]
  have hS : aeval (shiftOp p ℂ) (C μ * X) = μ • shiftOp p ℂ := by
    simp [Algebra.algebraMap_eq_smul_one]
  have h := Matsaev.lemma_2_2_proved p (P.comp (C μ * X))
  rw [aeval_comp, hJ, shiftNorm, aeval_comp, hS, norm_aeval_smul_shift p μ hμ] at h
  exact h

/-- **Corollary 5.1** (`cor:exactB`): for `P(z) = c₀ + c₁z + c₂z²` with `|c₀| = |c₂| > 0`, `|ζ| = 1`, `ζ² = -c₂/c₀`
and `1 ≤ p ≤ ∞`: `‖P(S)‖_p = ‖P(ζ̄J)‖_p = max_{|μ|=1} ‖P(μJ)‖_p`. -/
theorem corollary_5_1_proved (c₀ c₁ c₂ ζ : ℂ) (hc : ‖c₀‖ = ‖c₂‖) (hpos : 0 < ‖c₀‖) (hζ1 : ‖ζ‖ = 1)
    (hζ : ζ ^ 2 = -c₂ / c₀) :
    shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2) =
        matNorm p (aeval ((starRingEnd ℂ) ζ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C c₀ + C c₁ * X + C c₂ * X ^ 2)) ∧
      IsGreatest {r : ℝ | ∃ μ : ℂ, ‖μ‖ = 1 ∧
          r = matNorm p (aeval (μ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C c₀ + C c₁ * X + C c₂ * X ^ 2))}
        (shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2)) := by
  have _hc := hc  -- the paper's hypothesis `|c₀| = |c₂|`; it also follows from `ζ² = -c₂/c₀`, `|ζ| = 1`
  have hc₀ : c₀ ≠ 0 := norm_pos_iff.mp hpos
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hζc : ‖(starRingEnd ℂ) ζ‖ = 1 := by rw [Complex.norm_conj, hζ1]
  have hζζ : ζ * (starRingEnd ℂ) ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ1]; simp
  set P : ℂ[X] := C c₀ + C c₁ * X + C c₂ * X ^ 2
  set α := c₁ / (c₀ * ζ)
  have hle : shiftNorm p ℂ P ≤ matNorm p (aeval ((starRingEnd ℂ) ζ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) P) := by
    have hJ : aeval ((starRingEnd ℂ) ζ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) P = c₀ • aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa α 1) := by
      rw [aeval_quad_eq _ c₀ c₁ c₂ ζ hc₀ hζ0 hζ, smul_smul, hζζ, one_smul]
    rw [shiftNorm, aeval_quad_eq (shiftOp p ℂ) c₀ c₁ c₂ ζ hc₀ hζ0 hζ, norm_smul, norm_aeval_smul_shift p ζ hζ1, hJ,
      matNorm_smul_complex]
    exact mul_le_mul_of_nonneg_left (key_lp p α (shiftOp p ℂ) (norm_shiftOp_le p)) (norm_nonneg _)
  have heq := le_antisymm hle (matNorm_aeval_smul_Jmat_le p P _ hζc)
  refine ⟨heq, ⟨⟨_, hζc, heq⟩, ?_⟩⟩
  rintro _ ⟨μ, hμ, rfl⟩
  exact matNorm_aeval_smul_Jmat_le p P μ hμ

end Matsaev.ThmB
