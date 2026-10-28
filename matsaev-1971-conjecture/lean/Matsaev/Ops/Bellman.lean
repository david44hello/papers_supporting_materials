/-
Matsaev/Ops/Bellman.lean — Lemma 3.1 (window Bellman bound) of the paper.
Paper short v2.00 (md5 a9b3c6be), Lemma 3.1 (`lem:bellman`).

Route (no density argument). For x ∈ ℓ^p(ℕ) (real, p < ∞) put y = P_a(S) x, so y_n = x_n + a x_{n-1} - B x_{n-2} with
x_{-1} = x_{-2} = 0, and g_n = G(x_{n-1}, x_{n-2}); then g_0 = G(0, 0) = 0 and g_{n+1} = G(x_n, x_{n-1}). Hypothesis (3.1)
at the window (x_n, x_{n-1}, x_{n-2}) reads |y_n|^p ≤ C^p |x_n|^p + g_n - g_{n+1}; summed over n < N it telescopes to
Σ_{n<N} |y_n|^p ≤ C^p Σ_{n<N} |x_n|^p - g_N. As N → ∞, x_N → 0 (the series Σ |x_n|^p converges) and G is continuous with
G(0, 0) = 0, so g_N → 0; hence Σ |y_n|^p ≤ C^p Σ |x_n|^p, i.e. ‖P_a(S) x‖ ≤ C ‖x‖.
-/
import Matsaev.Defs.Spaces

namespace Matsaev

open scoped ENNReal
open Filter Topology Polynomial

namespace Bellman

/-- `P_a(S) = 1 + a S - B S²` in the algebra of continuous linear maps on `ℓ^p(ℕ)`. -/
lemma aeval_Pa_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B : ℝ) :
    aeval (shiftOp p ℝ) (Pa a B) = 1 + a • shiftOp p ℝ - B • (shiftOp p ℝ * shiftOp p ℝ) := by
  simp [Pa, Algebra.algebraMap_eq_smul_one, pow_two]

/-- `P_a(S)` coordinate-wise: `(P_a(S) x)_n = x_n + a x_{n-1} - B x_{n-2}` (with zeros before index 0). -/
lemma aeval_Pa_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B : ℝ) (x : lp (fun _ : ℕ => ℝ) p) (n : ℕ) :
    (aeval (shiftOp p ℝ) (Pa a B) x) n = x n + a * shiftSeq (⇑x) n - B * shiftSeq (shiftSeq ⇑x) n := by
  rw [aeval_Pa_eq]
  rfl

/-- A real sequence whose `q`-th powers are summable (q > 0) tends to 0. -/
lemma tendsto_zero_of_summable_rpow {q : ℝ} (hq : 0 < q) {x : ℕ → ℝ} (hx : Summable fun n => |x n| ^ q) :
    Tendsto x atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => |x n| ^ q) atTop (𝓝 0) := hx.tendsto_atTop_zero
  have h2 : Tendsto (fun n => (|x n| ^ q) ^ q⁻¹) atTop (𝓝 ((0 : ℝ) ^ q⁻¹)) :=
    ((Real.continuousAt_rpow_const 0 q⁻¹ (Or.inr (inv_nonneg.mpr hq.le))).tendsto).comp h1
  rw [Real.zero_rpow (inv_ne_zero hq.ne')] at h2
  have h3 : (fun n => (|x n| ^ q) ^ q⁻¹) = fun n => |x n| := by
    funext n
    exact Real.rpow_rpow_inv (abs_nonneg _) hq.ne'
  rw [h3] at h2
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [Real.norm_eq_abs] using h2

/-- The telescoped window bound for a real sequence. -/
lemma tsum_window_le {q a B C : ℝ} (hq : 0 < q) {G : ℝ → ℝ → ℝ} (hG : Continuous (Function.uncurry G))
    (hG0 : G 0 0 = 0) (hF : ∀ u v w : ℝ, 0 ≤ bellmanF q a B C G u v w) (x : ℕ → ℝ)
    (hxs : Summable fun n => |x n| ^ q)
    (hys : Summable fun n => |x n + a * shiftSeq x n - B * shiftSeq (shiftSeq x) n| ^ q) :
    ∑' n, |x n + a * shiftSeq x n - B * shiftSeq (shiftSeq x) n| ^ q ≤ C ^ q * ∑' n, |x n| ^ q := by
  set y : ℕ → ℝ := fun n => x n + a * shiftSeq x n - B * shiftSeq (shiftSeq x) n with hy_def
  set g : ℕ → ℝ := fun n => G (shiftSeq x n) (shiftSeq (shiftSeq x) n) with hg_def
  have hstep : ∀ n, |y n| ^ q ≤ C ^ q * |x n| ^ q + (g n - g (n + 1)) := by
    intro n
    have h := hF (x n) (shiftSeq x n) (shiftSeq (shiftSeq x) n)
    have hg1 : g (n + 1) = G (x n) (shiftSeq x n) := rfl
    unfold bellmanF at h
    rw [hg1]
    simp only [hy_def, hg_def]
    linarith
  have hg0 : g 0 = 0 := by simp [hg_def, shiftSeq, hG0]
  have hpart : ∀ N, ∑ n ∈ Finset.range N, |y n| ^ q ≤ C ^ q * ∑ n ∈ Finset.range N, |x n| ^ q - g N := by
    intro N
    calc ∑ n ∈ Finset.range N, |y n| ^ q
        ≤ ∑ n ∈ Finset.range N, (C ^ q * |x n| ^ q + (g n - g (n + 1))) :=
          Finset.sum_le_sum fun n _ => hstep n
      _ = C ^ q * ∑ n ∈ Finset.range N, |x n| ^ q - g N := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub', hg0]
          ring
  have hx0 : Tendsto x atTop (𝓝 0) := tendsto_zero_of_summable_rpow hq hxs
  have h1 : Tendsto (shiftSeq x) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact hx0
  have h2 : Tendsto (shiftSeq (shiftSeq x)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact h1
  have hg : Tendsto g atTop (𝓝 0) := by
    have h := (hG.tendsto ((0 : ℝ), (0 : ℝ))).comp (h1.prodMk_nhds h2)
    simpa [Function.comp_def, Function.uncurry, hG0, hg_def] using h
  have hL : Tendsto (fun N => ∑ n ∈ Finset.range N, |y n| ^ q) atTop (𝓝 (∑' n, |y n| ^ q)) :=
    hys.hasSum.tendsto_sum_nat
  have hR : Tendsto (fun N => C ^ q * ∑ n ∈ Finset.range N, |x n| ^ q - g N) atTop
      (𝓝 (C ^ q * ∑' n, |x n| ^ q - 0)) :=
    (hxs.hasSum.tendsto_sum_nat.const_mul _).sub hg
  rw [sub_zero] at hR
  exact le_of_tendsto_of_tendsto' hL hR hpart

end Bellman

open Bellman

/-- Lemma 3.1 (`lem:bellman`, the Bellman-function bound). -/
theorem lemma_3_1_proved (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (a B C : ℝ) (hC : 0 ≤ C) (G : ℝ → ℝ → ℝ)
    (hG : Continuous (Function.uncurry G)) (hG0 : G 0 0 = 0)
    (hF : ∀ u v w : ℝ, 0 ≤ bellmanF p.toReal a B C G u v w) :
    shiftNorm p ℝ (Pa a B) ≤ C := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  unfold shiftNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  have hy : ⇑(aeval (shiftOp p ℝ) (Pa a B) x) =
      fun n => x n + a * shiftSeq (⇑x) n - B * shiftSeq (shiftSeq ⇑x) n :=
    funext (aeval_Pa_apply p a B x)
  have hxs : Summable fun n => |x n| ^ p.toReal := by
    simpa [Real.norm_eq_abs] using (lp.memℓp x).summable hq
  have hys : Summable fun n => |x n + a * shiftSeq (⇑x) n - B * shiftSeq (shiftSeq ⇑x) n| ^ p.toReal := by
    have h := (lp.memℓp (aeval (shiftOp p ℝ) (Pa a B) x)).summable hq
    rw [hy] at h
    simpa [Real.norm_eq_abs] using h
  apply lp.norm_le_of_tsum_le hq (mul_nonneg hC (norm_nonneg x))
  rw [Real.mul_rpow hC (norm_nonneg x), lp.norm_rpow_eq_tsum hq x, hy]
  simpa [Real.norm_eq_abs] using tsum_window_le hq hG hG0 hF (⇑x) hxs hys

end Matsaev
