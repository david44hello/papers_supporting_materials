-- Matsaev/Ops/RC.lean — proves Lemma 2.1 (lem:RC): a real matrix, and P(S) for a real polynomial P, have the same norm on real and complex ℓ^p, 1 ≤ p < ∞.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
/-
Paper: short v2.00 (md5 a9b3c6be), Lemma 2.1 (`lem:RC`).
Targets: `lemma_2_1_matrix` and `lemma_2_1_shift` of `Matsaev/Paper/Statements.lean`, stated here verbatim as
`lemma_2_1_matrix_proved` and `lemma_2_1_shift_proved`.

Route (Marcinkiewicz–Zygmund). Put `q = p.toReal` and `c_q = ∫_0^{2π} |cos θ|^q dθ > 0`.
1. Scalar identity: `∫_0^{2π} |cos θ · Re z + sin θ · Im z|^q dθ = c_q |z|^q` (write `z = |z| e^{iα}`; periodicity).
2. Summing it over coordinates: for complex `x`, with the real vector `x_θ = cos θ · Re x + sin θ · Im x`,
   `∫_0^{2π} ‖x_θ‖^q dθ = c_q ‖x‖^q` (finite sum for matrices; `integral_tsum_of_summable_integral_norm` for `ℓ^p(ℕ)`).
3. A real operator `T` commutes with `Re`, `Im` and the real embedding, so `(T x)_θ = T (x_θ)` and
   `c_q ‖T x‖^q = ∫ ‖T x_θ‖^q ≤ ‖T‖_ℝ^q ∫ ‖x_θ‖^q = c_q ‖T‖_ℝ^q ‖x‖^q`; the embedding gives the other inequality
   (`opNorm_eq_of_re_im`, an abstract statement used for both targets).
-/
import Mathlib
import Matsaev.Defs.Spaces

namespace Matsaev

open scoped ENNReal
open Polynomial Real MeasureTheory

namespace RC

/-! ### The averaging constant and the scalar identity -/

/-- The Marcinkiewicz–Zygmund constant `c_q = ∫_0^{2π} |cos θ|^q dθ`. -/
noncomputable def cq (q : ℝ) : ℝ := ∫ θ in (0 : ℝ)..2 * π, |Real.cos θ| ^ q

lemma continuous_abs_rpow {q : ℝ} (hq : 0 < q) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun θ => |f θ| ^ q :=
  hf.abs.rpow_const fun _ => Or.inr hq.le

lemma cq_pos {q : ℝ} (hq : 0 < q) : 0 < cq q := by
  have hcont := continuous_abs_rpow hq Real.continuous_cos
  have h1 : 0 < ∫ θ in (0 : ℝ)..π / 2, |Real.cos θ| ^ q := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) (fun θ hθ => ?_)
      (by positivity)
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    exact Real.rpow_pos_of_pos (abs_pos.2 hcos.ne') q
  have h2 : 0 ≤ ∫ θ in π / 2..2 * π, |Real.cos θ| ^ q :=
    intervalIntegral.integral_nonneg (by linarith [Real.pi_pos]) fun θ _ => by positivity
  unfold cq
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 (π / 2))
    (hcont.intervalIntegrable (π / 2) (2 * π))]
  linarith

lemma cos_mul_re_add_sin_mul_im (z : ℂ) (θ : ℝ) :
    Real.cos θ * z.re + Real.sin θ * z.im = ‖z‖ * Real.cos (θ - Complex.arg z) := by
  rw [Real.cos_sub, ← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z]
  ring

lemma continuous_cos_mul_add_sin_mul (a b : ℝ) : Continuous fun θ : ℝ => Real.cos θ * a + Real.sin θ * b :=
  (Real.continuous_cos.mul continuous_const).add (Real.continuous_sin.mul continuous_const)

/-- Step 1: `∫_0^{2π} |Re(e^{-iθ} z)|^q dθ = c_q |z|^q`, with `Re(e^{-iθ} z) = cos θ · Re z + sin θ · Im z`. -/
lemma integral_abs_rpow_eq {q : ℝ} (z : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, |Real.cos θ * z.re + Real.sin θ * z.im| ^ q = cq q * ‖z‖ ^ q := by
  have hper : Function.Periodic (fun θ => |Real.cos θ| ^ q) (2 * π) := fun θ => by
    simp only [Real.cos_add_two_pi]
  have hpt : ∀ θ : ℝ, |Real.cos θ * z.re + Real.sin θ * z.im| ^ q =
      ‖z‖ ^ q * |Real.cos (θ - Complex.arg z)| ^ q := fun θ => by
    rw [cos_mul_re_add_sin_mul_im, abs_mul, abs_of_nonneg (norm_nonneg z),
      Real.mul_rpow (norm_nonneg z) (abs_nonneg _)]
  have hshift : ∫ θ in (0 : ℝ)..2 * π, |Real.cos (θ - Complex.arg z)| ^ q = cq q := by
    rw [intervalIntegral.integral_comp_sub_right (fun θ => |Real.cos θ| ^ q), zero_sub,
      show 2 * π - Complex.arg z = -Complex.arg z + 2 * π by ring]
    have := hper.intervalIntegral_add_eq (-Complex.arg z) 0
    simp only [zero_add] at this
    exact this
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, hshift, mul_comm]

/-! ### The abstract averaging argument -/

/-- If `fy ≤ M fx` pointwise and `∫ fx^q = c X^q`, `∫ fy^q = c Y^q` with `c > 0`, then `Y ≤ M X`. -/
lemma le_of_integral_rpow {q c M X Y : ℝ} (hq : 0 < q) (hc : 0 < c) (hM : 0 ≤ M) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    {fx fy : ℝ → ℝ} (hfx : Continuous fx) (hfy : Continuous fy) (hfx0 : ∀ θ, 0 ≤ fx θ)
    (hfy0 : ∀ θ, 0 ≤ fy θ) (hle : ∀ θ, fy θ ≤ M * fx θ)
    (hIX : ∫ θ in (0 : ℝ)..2 * π, fx θ ^ q = c * X ^ q) (hIY : ∫ θ in (0 : ℝ)..2 * π, fy θ ^ q = c * Y ^ q) :
    Y ≤ M * X := by
  have hint : ∀ f : ℝ → ℝ, Continuous f → IntervalIntegrable (fun θ => f θ ^ q) volume 0 (2 * π) :=
    fun f hf => (hf.rpow_const fun _ => Or.inr hq.le).intervalIntegrable _ _
  have hmono : ∫ θ in (0 : ℝ)..2 * π, fy θ ^ q ≤ ∫ θ in (0 : ℝ)..2 * π, (M * fx θ) ^ q :=
    intervalIntegral.integral_mono_on (by positivity) (hint fy hfy) (hint _ (continuous_const.mul hfx))
      fun θ _ => Real.rpow_le_rpow (hfy0 θ) (hle θ) hq.le
  have hscale : ∫ θ in (0 : ℝ)..2 * π, (M * fx θ) ^ q = M ^ q * (c * X ^ q) := by
    simp_rw [Real.mul_rpow hM (hfx0 _)]
    rw [intervalIntegral.integral_const_mul, hIX]
  have key : c * Y ^ q ≤ c * (M * X) ^ q :=
    calc c * Y ^ q = ∫ θ in (0 : ℝ)..2 * π, fy θ ^ q := hIY.symm
      _ ≤ ∫ θ in (0 : ℝ)..2 * π, (M * fx θ) ^ q := hmono
      _ = M ^ q * (c * X ^ q) := hscale
      _ = c * (M * X) ^ q := by rw [Real.mul_rpow hM hX]; ring
  rw [← Real.rpow_le_rpow_iff hY (mul_nonneg hM hX) hq]
  exact le_of_mul_le_mul_left key hc

/-- Step 3, abstractly: let `re, im : V → W` and `ofR : W → V` with `∫_0^{2π} ‖cos θ • re x + sin θ • im x‖^q = c_q ‖x‖^q`
and `‖ofR y‖ = ‖y‖`. If `TC` commutes with `re`, `im` (through `TR`) and `ofR`, then `‖TC‖ = ‖TR‖`. -/
theorem opNorm_eq_of_re_im {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {q : ℝ} (hq : 0 < q) (re im : V → W) (ofR : W → V)
    (hnorm : ∀ x, ∫ θ in (0 : ℝ)..2 * π, ‖Real.cos θ • re x + Real.sin θ • im x‖ ^ q = cq q * ‖x‖ ^ q)
    (hofR : ∀ y, ‖ofR y‖ = ‖y‖) (TC : V →L[ℂ] V) (TR : W →L[ℝ] W)
    (hre : ∀ x, re (TC x) = TR (re x)) (him : ∀ x, im (TC x) = TR (im x))
    (hofRT : ∀ y, TC (ofR y) = ofR (TR y)) : ‖TC‖ = ‖TR‖ := by
  have hcont : ∀ x, Continuous fun θ : ℝ => ‖Real.cos θ • re x + Real.sin θ • im x‖ := fun x =>
    ((Real.continuous_cos.smul continuous_const).add (Real.continuous_sin.smul continuous_const)).norm
  refine le_antisymm (TC.opNorm_le_bound (norm_nonneg TR) fun x => ?_)
    (TR.opNorm_le_bound (norm_nonneg TC) fun y => ?_)
  · refine le_of_integral_rpow hq (cq_pos hq) (norm_nonneg TR) (norm_nonneg x) (norm_nonneg _) (hcont x)
      (hcont (TC x)) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun θ => ?_) (hnorm x) (hnorm (TC x))
    have hlin : Real.cos θ • re (TC x) + Real.sin θ • im (TC x) = TR (Real.cos θ • re x + Real.sin θ • im x) := by
      rw [hre, him, map_add, map_smul, map_smul]
    rw [hlin]
    exact TR.le_opNorm _
  · rw [← hofR (TR y), ← hofRT, ← hofR y]
    exact TC.le_opNorm _

/-! ### Matrices: `ℓ^p_n = WithLp p (n → 𝕜)` -/

section Mat

variable {p : ℝ≥0∞} {n : Type} [Fintype n] [DecidableEq n]

/-- Coordinatewise real part `ℂ^n → ℝ^n`. -/
def reW (x : WithLp p (n → ℂ)) : WithLp p (n → ℝ) := WithLp.toLp p fun k => (x k).re

/-- Coordinatewise imaginary part `ℂ^n → ℝ^n`. -/
def imW (x : WithLp p (n → ℂ)) : WithLp p (n → ℝ) := WithLp.toLp p fun k => (x k).im

/-- The embedding `ℝ^n → ℂ^n`. -/
noncomputable def ofRealW (y : WithLp p (n → ℝ)) : WithLp p (n → ℂ) := WithLp.toLp p fun k => (y k : ℂ)

omit [DecidableEq n] in
lemma norm_rpow_eq_sumW {𝕜 : Type*} [RCLike 𝕜] [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : WithLp p (n → 𝕜)) :
    ‖x‖ ^ p.toReal = ∑ k, ‖x k‖ ^ p.toReal := by
  rw [PiLp.norm_eq_sum hp, one_div, Real.rpow_inv_rpow (Finset.sum_nonneg fun k _ => by positivity) hp.ne']

omit [DecidableEq n] in
lemma norm_ofRealW [Fact (1 ≤ p)] (hp : 0 < p.toReal) (y : WithLp p (n → ℝ)) : ‖ofRealW y‖ = ‖y‖ := by
  rw [PiLp.norm_eq_sum hp, PiLp.norm_eq_sum hp]
  simp [ofRealW, Complex.norm_real]

omit [DecidableEq n] in
/-- Step 2 for `ℓ^p_n`: `∫_0^{2π} ‖x_θ‖^q dθ = c_q ‖x‖^q`. -/
lemma integral_norm_rpowW [Fact (1 ≤ p)] (hp : 0 < p.toReal) (x : WithLp p (n → ℂ)) :
    ∫ θ in (0 : ℝ)..2 * π, ‖Real.cos θ • reW x + Real.sin θ • imW x‖ ^ p.toReal = cq p.toReal * ‖x‖ ^ p.toReal := by
  have happ : ∀ (θ : ℝ) (k : n), (Real.cos θ • reW x + Real.sin θ • imW x) k =
      Real.cos θ * (x k).re + Real.sin θ * (x k).im := fun _ _ => rfl
  simp_rw [norm_rpow_eq_sumW hp, happ, Real.norm_eq_abs]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (continuous_abs_rpow hp (continuous_cos_mul_add_sin_mul _ _)).intervalIntegrable _ _]
  simp_rw [integral_abs_rpow_eq, Finset.mul_sum]

lemma matOp_apply {𝕜 : Type*} [RCLike 𝕜] [Fact (1 ≤ p)] (A : Matrix n n 𝕜) (x : WithLp p (n → 𝕜)) (k : n) :
    matOp p A x k = ∑ j, A k j * x j := by
  simp [matOp, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]

lemma reW_matOp [Fact (1 ≤ p)] (A : Matrix n n ℝ) (x : WithLp p (n → ℂ)) :
    reW (matOp p (A.map (algebraMap ℝ ℂ)) x) = matOp p A (reW x) := by
  ext k
  simp [reW, matOp_apply, Complex.re_sum, Complex.coe_algebraMap]

lemma imW_matOp [Fact (1 ≤ p)] (A : Matrix n n ℝ) (x : WithLp p (n → ℂ)) :
    imW (matOp p (A.map (algebraMap ℝ ℂ)) x) = matOp p A (imW x) := by
  ext k
  simp [imW, matOp_apply, Complex.im_sum, Complex.coe_algebraMap]

lemma matOp_ofRealW [Fact (1 ≤ p)] (A : Matrix n n ℝ) (y : WithLp p (n → ℝ)) :
    matOp p (A.map (algebraMap ℝ ℂ)) (ofRealW y) = ofRealW (matOp p A y) := by
  ext k
  simp [ofRealW, matOp_apply, Complex.coe_algebraMap]

end Mat

/-! ### Sequences: `ℓ^p(ℕ) = lp (fun _ : ℕ => 𝕜) p` -/

section Seq

variable {p : ℝ≥0∞}

lemma memℓp_of_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {f : ℕ → E} {g : ℕ → F}
    (hf : Memℓp f p) (h : ∀ k, ‖g k‖ ≤ ‖f k‖) : Memℓp g p := by
  rcases p.trichotomy with rfl | rfl | hp
  · rw [memℓp_zero_iff] at hf ⊢
    refine hf.subset fun k hk hfk => hk ?_
    have := h k
    rw [hfk, norm_zero] at this
    exact norm_le_zero_iff.1 this
  · rw [memℓp_infty_iff] at hf ⊢
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨k, rfl⟩; exact (h k).trans (hC ⟨k, rfl⟩)⟩
  · rw [memℓp_gen_iff hp] at hf ⊢
    exact hf.of_nonneg_of_le (fun k => by positivity) fun k => Real.rpow_le_rpow (norm_nonneg _) (h k) hp.le

/-- Coordinatewise real part `ℓ^p(ℕ, ℂ) → ℓ^p(ℕ, ℝ)`. -/
noncomputable def reL (x : lp (fun _ : ℕ => ℂ) p) : lp (fun _ : ℕ => ℝ) p :=
  ⟨fun k => (x k).re, memℓp_of_norm_le (lp.memℓp x) fun _ => (Real.norm_eq_abs _).trans_le (Complex.abs_re_le_norm _)⟩

/-- Coordinatewise imaginary part `ℓ^p(ℕ, ℂ) → ℓ^p(ℕ, ℝ)`. -/
noncomputable def imL (x : lp (fun _ : ℕ => ℂ) p) : lp (fun _ : ℕ => ℝ) p :=
  ⟨fun k => (x k).im, memℓp_of_norm_le (lp.memℓp x) fun _ => (Real.norm_eq_abs _).trans_le (Complex.abs_im_le_norm _)⟩

/-- The embedding `ℓ^p(ℕ, ℝ) → ℓ^p(ℕ, ℂ)`. -/
noncomputable def ofRealL (y : lp (fun _ : ℕ => ℝ) p) : lp (fun _ : ℕ => ℂ) p :=
  ⟨fun k => (y k : ℂ), memℓp_of_norm_le (lp.memℓp y) fun _ => (Complex.norm_real _).le⟩

@[simp] lemma reL_apply (x : lp (fun _ : ℕ => ℂ) p) (k : ℕ) : reL x k = (x k).re := rfl
@[simp] lemma imL_apply (x : lp (fun _ : ℕ => ℂ) p) (k : ℕ) : imL x k = (x k).im := rfl
@[simp] lemma ofRealL_apply (y : lp (fun _ : ℕ => ℝ) p) (k : ℕ) : ofRealL y k = (y k : ℂ) := rfl

variable [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
lemma norm_ofRealL (hp : 0 < p.toReal) (y : lp (fun _ : ℕ => ℝ) p) : ‖ofRealL y‖ = ‖y‖ := by
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  simp [Complex.norm_real]

omit [Fact (1 ≤ p)] in
/-- Step 2 for `ℓ^p(ℕ)`: `∫_0^{2π} ‖x_θ‖^q dθ = c_q ‖x‖^q` (exchange of `∫` and `∑'`). -/
lemma integral_norm_rpowL (hp : 0 < p.toReal) (x : lp (fun _ : ℕ => ℂ) p) :
    ∫ θ in (0 : ℝ)..2 * π, ‖Real.cos θ • reL x + Real.sin θ • imL x‖ ^ p.toReal =
      cq p.toReal * ‖x‖ ^ p.toReal := by
  have happ : ∀ (θ : ℝ) (k : ℕ), (Real.cos θ • reL x + Real.sin θ • imL x) k =
      Real.cos θ * (x k).re + Real.sin θ * (x k).im := fun _ _ => rfl
  simp_rw [lp.norm_rpow_eq_tsum hp, happ, Real.norm_eq_abs]
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  have hint : ∀ k, Integrable (fun θ => |Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal)
      (volume.restrict (Set.Ioc 0 (2 * π))) := fun k =>
    ((continuous_abs_rpow hp (continuous_cos_mul_add_sin_mul _ _)).intervalIntegrable 0 (2 * π)).1
  have hI : ∀ k, ∫ θ in Set.Ioc 0 (2 * π), |Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal =
      cq p.toReal * ‖x k‖ ^ p.toReal := fun k => by
    rw [← intervalIntegral.integral_of_le h2pi]
    exact integral_abs_rpow_eq (x k)
  have hsum : Summable fun k =>
      ∫ θ in Set.Ioc 0 (2 * π), ‖|Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal‖ := by
    have hnn : ∀ k, ∫ θ in Set.Ioc 0 (2 * π), ‖|Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal‖ =
        cq p.toReal * ‖x k‖ ^ p.toReal := fun k => by
      rw [← hI k]
      congr 1
      funext θ
      exact Real.norm_of_nonneg (by positivity)
    simp_rw [hnn]
    exact ((lp.memℓp x).summable hp).mul_left _
  calc ∫ θ in (0 : ℝ)..2 * π, ∑' k, |Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal
      = ∫ θ in Set.Ioc 0 (2 * π), ∑' k, |Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal :=
        intervalIntegral.integral_of_le h2pi
    _ = ∑' k, ∫ θ in Set.Ioc 0 (2 * π), |Real.cos θ * (x k).re + Real.sin θ * (x k).im| ^ p.toReal :=
        (integral_tsum_of_summable_integral_norm hint hsum).symm
    _ = ∑' k, cq p.toReal * ‖x k‖ ^ p.toReal := tsum_congr hI
    _ = cq p.toReal * ∑' k, ‖x k‖ ^ p.toReal := tsum_mul_left

lemma shiftOp_apply_zero' {𝕜 : Type*} [RCLike 𝕜] (x : lp (fun _ : ℕ => 𝕜) p) : shiftOp p 𝕜 x 0 = 0 := rfl

lemma shiftOp_apply_succ' {𝕜 : Type*} [RCLike 𝕜] (x : lp (fun _ : ℕ => 𝕜) p) (k : ℕ) :
    shiftOp p 𝕜 x (k + 1) = x k := rfl

/-- A map commuting with `S` commutes with every power `S^m`. -/
lemma shiftOp_pow_comm {𝕜₁ 𝕜₂ : Type*} [RCLike 𝕜₁] [RCLike 𝕜₂]
    (L : lp (fun _ : ℕ => 𝕜₁) p → lp (fun _ : ℕ => 𝕜₂) p) (hS : ∀ x, L (shiftOp p 𝕜₁ x) = shiftOp p 𝕜₂ (L x))
    (m : ℕ) (x : lp (fun _ : ℕ => 𝕜₁) p) : L ((shiftOp p 𝕜₁ ^ m) x) = (shiftOp p 𝕜₂ ^ m) (L x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, ih, hS]

/-- An additive, real-homogeneous map commuting with `S` commutes with `P(S)` for every real polynomial `P`. -/
lemma aeval_shiftOp_comm {𝕜₁ 𝕜₂ : Type*} [RCLike 𝕜₁] [RCLike 𝕜₂]
    (L : lp (fun _ : ℕ => 𝕜₁) p → lp (fun _ : ℕ => 𝕜₂) p) (hadd : ∀ x y, L (x + y) = L x + L y)
    (hsmul : ∀ (r : ℝ) x, L (algebraMap ℝ 𝕜₁ r • x) = algebraMap ℝ 𝕜₂ r • L x)
    (hS : ∀ x, L (shiftOp p 𝕜₁ x) = shiftOp p 𝕜₂ (L x)) (P : ℝ[X]) (x : lp (fun _ : ℕ => 𝕜₁) p) :
    L (aeval (shiftOp p 𝕜₁) (P.map (algebraMap ℝ 𝕜₁)) x) =
      aeval (shiftOp p 𝕜₂) (P.map (algebraMap ℝ 𝕜₂)) (L x) := by
  induction P using Polynomial.induction_on' generalizing x with
  | add P Q hP hQ => simp only [Polynomial.map_add, map_add, add_apply, hadd, hP, hQ]
  | monomial m r =>
    simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, mul_apply_eq_comp,
      ContinuousLinearMap.algebraMap_apply, hsmul, shiftOp_pow_comm L hS]

lemma reL_shiftOp (x : lp (fun _ : ℕ => ℂ) p) : reL (shiftOp p ℂ x) = shiftOp p ℝ (reL x) := by
  refine lp.ext (funext fun k => ?_)
  cases k with
  | zero => simp [shiftOp_apply_zero']
  | succ k => simp [shiftOp_apply_succ']

lemma imL_shiftOp (x : lp (fun _ : ℕ => ℂ) p) : imL (shiftOp p ℂ x) = shiftOp p ℝ (imL x) := by
  refine lp.ext (funext fun k => ?_)
  cases k with
  | zero => simp [shiftOp_apply_zero']
  | succ k => simp [shiftOp_apply_succ']

lemma ofRealL_shiftOp (y : lp (fun _ : ℕ => ℝ) p) : ofRealL (shiftOp p ℝ y) = shiftOp p ℂ (ofRealL y) := by
  refine lp.ext (funext fun k => ?_)
  cases k with
  | zero => simp [shiftOp_apply_zero']
  | succ k => simp [shiftOp_apply_succ']

lemma reL_aeval (P : ℝ[X]) (x : lp (fun _ : ℕ => ℂ) p) :
    reL (aeval (shiftOp p ℂ) (P.map (algebraMap ℝ ℂ)) x) = aeval (shiftOp p ℝ) P (reL x) := by
  have h := aeval_shiftOp_comm reL (fun x y => lp.ext (funext fun k => Complex.add_re _ _))
    (fun r x => lp.ext (funext fun k => by
      simp only [reL_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp [Complex.coe_algebraMap]))
    reL_shiftOp P x
  simpa using h

lemma imL_aeval (P : ℝ[X]) (x : lp (fun _ : ℕ => ℂ) p) :
    imL (aeval (shiftOp p ℂ) (P.map (algebraMap ℝ ℂ)) x) = aeval (shiftOp p ℝ) P (imL x) := by
  have h := aeval_shiftOp_comm imL (fun x y => lp.ext (funext fun k => Complex.add_im _ _))
    (fun r x => lp.ext (funext fun k => by
      simp only [imL_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp [Complex.coe_algebraMap]))
    imL_shiftOp P x
  simpa using h

lemma aeval_ofRealL (P : ℝ[X]) (y : lp (fun _ : ℕ => ℝ) p) :
    aeval (shiftOp p ℂ) (P.map (algebraMap ℝ ℂ)) (ofRealL y) = ofRealL (aeval (shiftOp p ℝ) P y) := by
  have h := aeval_shiftOp_comm ofRealL (fun x y => lp.ext (funext fun k => Complex.ofReal_add _ _))
    (fun r x => lp.ext (funext fun k => by
      simp only [ofRealL_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp [Complex.coe_algebraMap]))
    ofRealL_shiftOp P y
  simpa using h.symm

end Seq

lemma toReal_pos_of_ne_top (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) : 0 < p.toReal :=
  ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hptop

end RC

/-- **Lemma 2.1** (`lem:RC`), matrices: a real matrix has the same norm on the real and on the complex
`ℓ^p_n`, `1 ≤ p < ∞`. -/
theorem lemma_2_1_matrix_proved (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : matNorm p (A.map (algebraMap ℝ ℂ)) = matNorm p A := by
  have hp := RC.toReal_pos_of_ne_top p hptop
  have h := RC.opNorm_eq_of_re_im (V := WithLp p (n → ℂ)) (W := WithLp p (n → ℝ)) hp RC.reW RC.imW RC.ofRealW
    (RC.integral_norm_rpowW hp) (RC.norm_ofRealW hp)
    (matOp p (A.map (algebraMap ℝ ℂ))) (matOp p A) (RC.reW_matOp A) (RC.imW_matOp A) (RC.matOp_ofRealW A)
  exact h

/-- **Lemma 2.1** (`lem:RC`), convolution operators: for a real polynomial `P`, `P(S)` has the same norm on
the real and on the complex `ℓ^p(ℕ)`, `1 ≤ p < ∞`. -/
theorem lemma_2_1_shift_proved (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (P : ℝ[X]) :
    shiftNorm p ℂ (P.map (algebraMap ℝ ℂ)) = shiftNorm p ℝ P := by
  have hp := RC.toReal_pos_of_ne_top p hptop
  have h := RC.opNorm_eq_of_re_im (V := lp (fun _ : ℕ => ℂ) p) (W := lp (fun _ : ℕ => ℝ) p) hp RC.reL RC.imL
    RC.ofRealL (RC.integral_norm_rpowL hp) (RC.norm_ofRealL hp)
    (aeval (shiftOp p ℂ) (P.map (algebraMap ℝ ℂ))) (aeval (shiftOp p ℝ) P) (RC.reL_aeval P) (RC.imL_aeval P)
    (RC.aeval_ofRealL P)
  exact h

end Matsaev
