-- Matsaev/Angle/Basic.lean — the angle library (plan R1-R3): θ_* exists (IsThetaStar), facts on N, q, W_γ, Rot, matNorm.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Angle.Defs
import Matsaev.Bridge.Basic
import Matsaev.Scalar.N1

namespace Matsaev.Angle

open Real Set Filter Topology
open scoped ENNReal Matrix

/-! ## `φ` and `|y|^q` -/

lemma phi_eq_mul (q y : ℝ) : phi q y = |y| ^ (q - 2) * y := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · rw [phi, sign_neg h, abs_of_neg h, show q - 1 = (q - 2) + 1 by ring,
      rpow_add_one (by linarith : -y ≠ 0)]
    simp
  · simp [phi]
  · rw [phi, sign_pos h, abs_of_pos h, show q - 1 = (q - 2) + 1 by ring, rpow_add_one h.ne']
    simp

lemma phi_zero (q : ℝ) : phi q 0 = 0 := by simp [phi]

/-- `d/dy |y|^q = q φ(y)` for `q > 1`. -/
lemma hasDerivAt_absRpow {q : ℝ} (hq : 1 < q) (y : ℝ) :
    HasDerivAt (fun y : ℝ => |y| ^ q) (q * phi q y) y := by
  rw [phi_eq_mul, ← mul_assoc]
  exact hasDerivAt_abs_rpow y hq

lemma continuous_phi {q : ℝ} (hq : 1 < q) : Continuous (phi q) := by
  have h1 : Continuous fun y : ℝ => y ^ (q - 1) := continuous_rpow_const (by linarith)
  have h2 : Continuous fun y : ℝ => -(-y) ^ (q - 1) := (h1.comp continuous_neg).neg
  have heq : phi q = fun y => if 0 ≤ y then y ^ (q - 1) else -(-y) ^ (q - 1) := by
    funext y
    rcases lt_trichotomy y 0 with h | rfl | h
    · simp [phi, sign_neg h, abs_of_neg h, not_le.mpr h]
    · simp [phi, zero_rpow (by linarith : q - 1 ≠ 0)]
    · simp [phi, sign_pos h, abs_of_pos h, h.le]
  rw [heq]
  refine Continuous.if_le h1 h2 continuous_const continuous_id fun y hy => ?_
  subst hy
  simp [zero_rpow (by linarith : q - 1 ≠ 0)]

/-- `φ'(y) = (q-1)|y|^(q-2)` for `q > 2` (also at `y = 0`, where both sides are `0`). -/
lemma hasDerivAt_phi {q : ℝ} (hq : 2 < q) (y : ℝ) :
    HasDerivAt (phi q) ((q - 1) * |y| ^ (q - 2)) y := by
  rcases lt_trichotomy y 0 with h | rfl | h
  · have hev : (fun x : ℝ => -(-x) ^ (q - 1)) =ᶠ[𝓝 y] phi q := by
      filter_upwards [Iio_mem_nhds h] with x hx
      rw [phi, sign_neg (show x < 0 from hx), abs_of_neg (show x < 0 from hx)]
      simp
    have hd : HasDerivAt (fun x : ℝ => -(-x) ^ (q - 1)) (-((q - 1) * (-y) ^ (q - 1 - 1) * (-1))) y :=
      ((hasDerivAt_rpow_const (Or.inl (neg_ne_zero.mpr h.ne))).comp y (hasDerivAt_neg y)).neg
    refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    rw [abs_of_neg h, show q - 1 - 1 = q - 2 by ring]
    ring
  · have h0 : |(0 : ℝ)| ^ (q - 2) = 0 := by rw [abs_zero, zero_rpow (by linarith)]
    rw [h0, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    have ht : Tendsto (fun x : ℝ => |x| ^ (q - 2)) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => |x| ^ (q - 2) :=
        (continuous_rpow_const (by linarith)).comp continuous_abs
      simpa [zero_rpow (by linarith : q - 2 ≠ 0)] using hc.tendsto 0
    have hO := ((Asymptotics.isLittleO_one_iff ℝ).mpr ht).mul_isBigO
      (Asymptotics.isBigO_refl (fun x : ℝ => x) (𝓝 0))
    simpa [phi_eq_mul, phi_zero] using hO
  · have hev : (fun x : ℝ => x ^ (q - 1)) =ᶠ[𝓝 y] phi q := by
      filter_upwards [Ioi_mem_nhds h] with x hx
      rw [phi, sign_pos (show 0 < x from hx), abs_of_pos (show 0 < x from hx)]
      simp
    have hd := hasDerivAt_rpow_const (p := q - 1) (Or.inl h.ne')
    refine (hd.congr_of_eventuallyEq hev.symm).congr_deriv ?_
    rw [abs_of_pos h, show q - 1 - 1 = q - 2 by ring]

/-! ## `N(θ)` and `q(θ)` -/

theorem Nang_pos (q θ : ℝ) (hq : 0 < q) : 0 < Nang q θ := by
  unfold Nang
  have hc0 : 0 ≤ |Real.cos θ| ^ q := rpow_nonneg (abs_nonneg _) q
  have hs0 : 0 ≤ |Real.sin θ| ^ q := rpow_nonneg (abs_nonneg _) q
  rcases eq_or_ne (Real.cos θ) 0 with hc | hc
  · have hs : Real.sin θ ≠ 0 := by
      intro hs
      have := sin_sq_add_cos_sq θ
      rw [hs, hc] at this
      norm_num at this
    have := rpow_pos_of_pos (abs_pos.mpr hs) q
    linarith
  · have := rpow_pos_of_pos (abs_pos.mpr hc) q
    linarith

theorem Nang_periodic (q : ℝ) : Function.Periodic (Nang q) (π / 2) := by
  intro θ
  simp only [Nang, cos_add_pi_div_two, sin_add_pi_div_two, abs_neg]
  ring

theorem qang_periodic (q : ℝ) : Function.Periodic (qang q) (π / 2) := by
  intro θ
  simp only [qang, cos_add_pi_div_two, sin_add_pi_div_two]
  calc Qf q (-Real.sin θ) (Real.cos θ) = Qf q (-Real.sin θ) (-(-Real.cos θ)) := by rw [neg_neg]
    _ = Qf q (Real.sin θ) (-Real.cos θ) := Qf_neg _ _ _
    _ = Qf q (Real.cos θ) (Real.sin θ) := Qf_J _ _ _

lemma continuous_Nang {q : ℝ} (hq : 0 < q) : Continuous (Nang q) := by
  have hc : Continuous fun θ => |Real.cos θ| ^ q :=
    (continuous_abs.comp continuous_cos).rpow_const fun _ => Or.inr hq.le
  have hs : Continuous fun θ => |Real.sin θ| ^ q :=
    (continuous_abs.comp continuous_sin).rpow_const fun _ => Or.inr hq.le
  exact hc.add hs

/-- `q(θ) · N(θ)` is the numerator of `Q(e(θ))`. -/
lemma qang_mul_Nang {q : ℝ} (hq : 0 < q) (θ : ℝ) :
    qang q θ * Nang q θ = phi q (Real.cos θ) * Real.sin θ - phi q (Real.sin θ) * Real.cos θ :=
  div_mul_cancel₀ _ (Nang_pos q θ hq).ne'

theorem continuous_qang (q : ℝ) (hq : 1 < q) : Continuous (qang q) := by
  have hφ := continuous_phi hq
  have heq : qang q = fun θ =>
      (phi q (Real.cos θ) * Real.sin θ - phi q (Real.sin θ) * Real.cos θ) / Nang q θ := rfl
  rw [heq]
  exact (((hφ.comp continuous_cos).mul continuous_sin).sub ((hφ.comp continuous_sin).mul continuous_cos)).div
    (continuous_Nang (by linarith)) fun θ => (Nang_pos q θ (by linarith)).ne'

theorem hasDerivAt_Nang (q : ℝ) (hq : 1 < q) (θ : ℝ) :
    HasDerivAt (Nang q) (-(q * qang q θ * Nang q θ)) θ := by
  have hc := (hasDerivAt_absRpow hq (Real.cos θ)).comp θ (hasDerivAt_cos θ)
  have hs := (hasDerivAt_absRpow hq (Real.sin θ)).comp θ (hasDerivAt_sin θ)
  refine (hc.add hs).congr_deriv ?_
  rw [mul_assoc q (qang q θ), qang_mul_Nang (by linarith)]
  ring

theorem log_Nang_sub (q : ℝ) (hq : 1 < q) (γ θ : ℝ) :
    Real.log (Nang q (θ - γ)) - Real.log (Nang q θ) = Wmov q γ θ := by
  have hderiv : ∀ x ∈ uIcc (θ - γ) θ,
      HasDerivAt (fun τ => Real.log (Nang q τ)) (-(q * qang q x)) x := by
    intro x _
    have hN := (Nang_pos q x (by linarith)).ne'
    refine ((hasDerivAt_Nang q hq x).log hN).congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun τ => -(q * qang q τ)) MeasureTheory.volume (θ - γ) θ :=
    (continuous_const.mul (continuous_qang q hq)).neg.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hFTC
  unfold Wmov
  linarith

/-! ## Rotations and `matNorm` -/

theorem rot_mulVec_ev (γ θ : ℝ) : Rot γ *ᵥ ev θ = ev (θ - γ) := by
  rw [Rot, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ev, Jmat_mulVec]
  ext i
  fin_cases i <;> simp [ev, cos_sub, sin_sub] <;> ring

theorem aeval_Jmat_Pa_eq_rot (a B : ℝ) (hB : 0 < 1 + B) :
    Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) =
      Real.sqrt ((1 + B) ^ 2 + a ^ 2) • Rot (Real.arctan (a / (1 + B))) := by
  have hs : 0 < Real.sqrt (1 + (a / (1 + B)) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt ((1 + B) ^ 2 + a ^ 2) = (1 + B) * Real.sqrt (1 + (a / (1 + B)) ^ 2) := by
    rw [show (1 + B) ^ 2 + a ^ 2 = (1 + B) ^ 2 * (1 + (a / (1 + B)) ^ 2) by field_simp,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB.le]
  rw [aeval_Jmat_Pa_proved, Rot, Real.cos_arctan, Real.sin_arctan, hsq, smul_add, smul_smul, smul_smul]
  congr 2
  · field_simp
  · field_simp

/-- `N(θ) = ‖e(θ)‖_p^p`. -/
lemma Nang_eq_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (θ : ℝ) :
    Nang p.toReal θ = ‖WithLp.toLp p (ev θ)‖ ^ p.toReal := by
  rw [ev, norm_toLp_fin2_rpow p hptop]
  rfl

lemma rpow_norm_mulVec_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (A : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    ‖WithLp.toLp p (A *ᵥ x)‖ ^ p.toReal ≤ matNorm p A ^ p.toReal * ‖WithLp.toLp p x‖ ^ p.toReal := by
  rw [← mul_rpow (matNorm_nonneg p A) (norm_nonneg _)]
  exact rpow_le_rpow (norm_nonneg _) (norm_mulVec_le_matNorm p A x) ENNReal.toReal_nonneg

/-- Polar coordinates: a nonzero vector of `ℝ²` is `r • e(θ)` with `r ≠ 0`. -/
lemma exists_polar (x : Fin 2 → ℝ) (hx : x ≠ 0) : ∃ r θ : ℝ, r ≠ 0 ∧ x = r • ev θ := by
  have hz : (⟨x 0, x 1⟩ : ℂ) ≠ 0 := by
    intro h
    apply hx
    have h0 : x 0 = 0 := congrArg Complex.re h
    have h1 : x 1 = 0 := congrArg Complex.im h
    ext i
    fin_cases i <;> simp [h0, h1]
  refine ⟨‖(⟨x 0, x 1⟩ : ℂ)‖, Complex.arg ⟨x 0, x 1⟩, norm_ne_zero_iff.mpr hz, ?_⟩
  ext i
  fin_cases i
  · simp [ev, Complex.norm_mul_cos_arg]
  · simp [ev, Complex.norm_mul_sin_arg]

theorem rot_norm_char (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (γ : ℝ) :
    (∀ θ : ℝ, Nang p.toReal (θ - γ) ≤ matNorm p (Rot γ) ^ p.toReal * Nang p.toReal θ) ∧
    ∃ θ : ℝ, Nang p.toReal (θ - γ) = matNorm p (Rot γ) ^ p.toReal * Nang p.toReal θ := by
  refine ⟨fun θ => ?_, ?_⟩
  · rw [Nang_eq_norm p hptop, Nang_eq_norm p hptop, ← rot_mulVec_ev]
    exact rpow_norm_mulVec_le p _ _
  · obtain ⟨x, hx1, hxA⟩ := exists_eq_matNorm p (Rot γ)
    have hx : x ≠ 0 := by
      rintro rfl
      simp at hx1
    obtain ⟨r, θ, -, rfl⟩ := exists_polar x hx
    refine ⟨θ, ?_⟩
    rw [Nang_eq_norm p hptop, Nang_eq_norm p hptop, ← rot_mulVec_ev]
    rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul] at hxA
    rw [WithLp.toLp_smul, norm_smul] at hx1
    have key : ‖WithLp.toLp p (Rot γ *ᵥ ev θ)‖ = matNorm p (Rot γ) * ‖WithLp.toLp p (ev θ)‖ := by
      calc ‖WithLp.toLp p (Rot γ *ᵥ ev θ)‖
          = ‖WithLp.toLp p (Rot γ *ᵥ ev θ)‖ * (‖r‖ * ‖WithLp.toLp p (ev θ)‖) := by rw [hx1, mul_one]
        _ = (‖r‖ * ‖WithLp.toLp p (Rot γ *ᵥ ev θ)‖) * ‖WithLp.toLp p (ev θ)‖ := by ring
        _ = matNorm p (Rot γ) * ‖WithLp.toLp p (ev θ)‖ := by rw [hxA]
    rw [key, mul_rpow (matNorm_nonneg _ _) (norm_nonneg _)]

theorem matNorm_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    matNorm p (r • A) = |r| * matNorm p A := by
  have h : matOp p (r • A) = r • matOp p A := by
    simp only [matOp, map_smul]
  rw [matNorm, matNorm, h, norm_smul, Real.norm_eq_abs]

theorem sigmaAng_nonneg (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (a B θ : ℝ) :
    0 ≤ SigmaAng p.toReal a B (matNorm p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ := by
  have hmv : Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ev θ =
      ![(1 + B) * Real.cos θ + a * Real.sin θ, (1 + B) * Real.sin θ - a * Real.cos θ] := by
    rw [aeval_Jmat_Pa_proved, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ev,
      Jmat_mulVec]
    ext i
    fin_cases i <;> simp [sub_eq_add_neg]
  have h := rpow_norm_mulVec_le p (Polynomial.aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) (ev θ)
  rw [hmv, norm_toLp_fin2_rpow p hptop, ← Nang_eq_norm p hptop] at h
  unfold SigmaAng
  linarith

/-! ## `q(θ)` through `tan`: `q(θ) = Q(1, tan θ)` for `cos θ > 0` -/

lemma Qf_neg_right (p u v : ℝ) : Qf p u (-v) = -Qf p u v := by
  unfold Qf
  rw [phi_neg, abs_neg]
  ring

lemma qang_neg (q θ : ℝ) : qang q (-θ) = -qang q θ := by
  simp only [qang, cos_neg, sin_neg, Qf_neg_right]

lemma cos_sin_ne (θ : ℝ) : (Real.cos θ, Real.sin θ) ≠ (0, 0) := by
  intro h
  simp only [Prod.mk.injEq] at h
  have := sin_sq_add_cos_sq θ
  rw [h.1, h.2] at this
  norm_num at this

lemma qang_eq_Qf_tan {q θ : ℝ} (hq : 1 < q) (hc : 0 < Real.cos θ) : qang q θ = Qf q 1 (Real.tan θ) := by
  unfold qang
  rw [← Qf_homog q hq (Real.cos θ) 1 (Real.tan θ) hc.ne', mul_one, tan_eq_sin_div_cos,
    mul_div_cancel₀ _ hc.ne']

lemma qang_eq_dfun_tan {q θ : ℝ} (hq : 1 < q) (h0 : 0 < θ) (h1 : θ < π / 2) :
    qang q θ = dfun q (Real.tan θ) := by
  rw [qang_eq_Qf_tan hq (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h1⟩),
    Qf_one q _ (tan_pos_of_pos_of_lt_pi_div_two h0 h1)]

lemma Qf_one_eq (q s : ℝ) : Qf q 1 s = (s - phi q s) / (1 + |s| ^ q) := by
  have h1 : phi q 1 = 1 := by simp [phi]
  rw [Qf, h1, abs_one, one_rpow, one_mul, mul_one]

/-- The derivative of `s ↦ Q(1, s)`. -/
noncomputable def dQ1 (q s : ℝ) : ℝ :=
  ((1 - (q - 1) * |s| ^ (q - 2)) * (1 + |s| ^ q) - (s - phi q s) * (q * phi q s)) / (1 + |s| ^ q) ^ 2

lemma hasDerivAt_Qf_one {q : ℝ} (hq : 2 < q) (s : ℝ) : HasDerivAt (fun s => Qf q 1 s) (dQ1 q s) s := by
  have hnum : HasDerivAt (fun s => s - phi q s) (1 - (q - 1) * |s| ^ (q - 2)) s :=
    (hasDerivAt_id' s).sub (hasDerivAt_phi hq s)
  have hden : HasDerivAt (fun s => 1 + |s| ^ q) (q * phi q s) s :=
    (hasDerivAt_absRpow (by linarith) s).const_add 1
  have hne : 1 + |s| ^ q ≠ 0 := by positivity
  rw [show (fun s => Qf q 1 s) = fun s => (s - phi q s) / (1 + |s| ^ q) from funext (Qf_one_eq q)]
  exact hnum.div hden hne

lemma dQ1_neg (q s : ℝ) : dQ1 q (-s) = dQ1 q s := by
  unfold dQ1
  rw [abs_neg, phi_neg]
  ring

lemma dQ1_zero {q : ℝ} (hq : 2 < q) : dQ1 q 0 = 1 := by
  unfold dQ1
  rw [phi_zero, abs_zero, zero_rpow (by linarith), zero_rpow (by linarith)]
  norm_num

lemma dQ1_eq_deriv_dfun {q s : ℝ} (hq : 2 < q) (hs : 0 < s) : deriv (dfun q) s = dQ1 q s := by
  have hev : (fun s => Qf q 1 s) =ᶠ[𝓝 s] dfun q := by
    filter_upwards [Ioi_mem_nhds hs] with x hx using Qf_one q x hx
  exact ((hasDerivAt_Qf_one hq s).congr_of_eventuallyEq hev.symm).deriv

lemma dQ1_one_ne {q : ℝ} (hq : 2 < q) : dQ1 q 1 ≠ 0 := by
  rw [← dQ1_eq_deriv_dfun hq one_pos, (hasDerivAt_dfun (p := q) one_pos).deriv, gN1_one, one_rpow]
  exact div_ne_zero (by linarith) (by norm_num)

lemma hasDerivAt_qang_of_cos_pos {q θ : ℝ} (hq : 2 < q) (hc : 0 < Real.cos θ) :
    HasDerivAt (qang q) (dQ1 q (Real.tan θ) * (1 / Real.cos θ ^ 2)) θ := by
  have hev : qang q =ᶠ[𝓝 θ] fun x => Qf q 1 (Real.tan x) := by
    filter_upwards [(continuous_cos.tendsto θ).eventually (lt_mem_nhds hc)] with x hx
    exact qang_eq_Qf_tan (by linarith) hx
  exact ((hasDerivAt_Qf_one hq (Real.tan θ)).comp θ (hasDerivAt_tan hc.ne')).congr_of_eventuallyEq hev

lemma deriv_qang_of_cos_pos {q θ : ℝ} (hq : 2 < q) (hc : 0 < Real.cos θ) :
    deriv (qang q) θ = dQ1 q (Real.tan θ) * (1 / Real.cos θ ^ 2) :=
  (hasDerivAt_qang_of_cos_pos hq hc).deriv

/-! ## Reduction to the fundamental domain `[-π/4, π/4)` -/

lemma exists_reduce (θ : ℝ) : ∃ n : ℤ, θ - n * (π / 2) ∈ Ico (-(π / 4)) (π / 4) := by
  have hπ : 0 < π / 2 := by positivity
  refine ⟨⌊(θ + π / 4) / (π / 2)⌋, ?_, ?_⟩
  · have h := Int.floor_le ((θ + π / 4) / (π / 2))
    rw [le_div_iff₀ hπ] at h
    linarith
  · have h := Int.lt_floor_add_one ((θ + π / 4) / (π / 2))
    rw [div_lt_iff₀ hπ] at h
    nlinarith

lemma cos_pos_of_mem_Ico {θ : ℝ} (hθ : θ ∈ Ico (-(π / 4)) (π / 4)) : 0 < Real.cos θ :=
  cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2, pi_pos]⟩

lemma qang_eq_sub_int (q : ℝ) (n : ℤ) : qang q = fun x => qang q (x - n * (π / 2)) :=
  funext fun _ => ((qang_periodic q).sub_int_mul_eq n).symm

lemma differentiableAt_qang {q : ℝ} (hq : 2 < q) (θ : ℝ) : DifferentiableAt ℝ (qang q) θ := by
  obtain ⟨n, hn⟩ := exists_reduce θ
  have hd := (hasDerivAt_qang_of_cos_pos hq (cos_pos_of_mem_Ico hn)).differentiableAt
  rw [qang_eq_sub_int q n]
  exact hd.comp θ (differentiableAt_id.sub_const _)

lemma deriv_qang_sub_int (q θ : ℝ) (n : ℤ) : deriv (qang q) (θ - n * (π / 2)) = deriv (qang q) θ := by
  conv_rhs => rw [qang_eq_sub_int q n]
  rw [deriv_comp_sub_const]

/-! ## The maximum angle `θ_* = arctan t_*` -/

section ThetaStar

variable {q t : ℝ} (hq : 2 < q) (ht : t ∈ Ioo (0 : ℝ) 1)
  (hcrit : ∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun q) s = 0 ↔ s = t)
include hq ht hcrit

lemma deriv_qang_arctan : deriv (qang q) (arctan t) = 0 := by
  rw [deriv_qang_of_cos_pos hq (cos_arctan_pos t), tan_arctan, ← dQ1_eq_deriv_dfun hq ht.1,
    (hcrit t ht).mpr rfl, zero_mul]

lemma deriv_qang_neg_arctan : deriv (qang q) (-arctan t) = 0 := by
  rw [deriv_qang_of_cos_pos hq (by rw [cos_neg]; exact cos_arctan_pos t), tan_neg, tan_arctan, dQ1_neg,
    ← dQ1_eq_deriv_dfun hq ht.1, (hcrit t ht).mpr rfl, zero_mul]

omit ht in
/-- On `[-π/4, π/4)` the critical points of `q` are `±θ_*`. -/
lemma eq_of_deriv_qang_eq_zero {θ : ℝ} (hθ : θ ∈ Ico (-(π / 4)) (π / 4)) (h0 : deriv (qang q) θ = 0) :
    θ = arctan t ∨ θ = -arctan t := by
  have hlo : -(π / 2) < θ := by linarith [hθ.1, pi_pos]
  have hhi : θ < π / 2 := by linarith [hθ.2, pi_pos]
  have hc : 0 < Real.cos θ := cos_pos_of_mem_Ico hθ
  rw [deriv_qang_of_cos_pos hq hc] at h0
  have hz : dQ1 q (Real.tan θ) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exfalso
      have : 0 < 1 / Real.cos θ ^ 2 := by positivity
      linarith
  have htan1 : Real.tan θ < 1 := by
    have h := strictMonoOn_tan ⟨hlo, hhi⟩ ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ hθ.2
    rwa [tan_pi_div_four] at h
  have htan2 : -1 ≤ Real.tan θ := by
    have h := strictMonoOn_tan.monotoneOn ⟨by linarith [pi_pos], by linarith [pi_pos]⟩ ⟨hlo, hhi⟩ hθ.1
    rwa [tan_neg, tan_pi_div_four] at h
  have harc : θ = arctan (Real.tan θ) := (arctan_tan hlo hhi).symm
  rcases lt_trichotomy (Real.tan θ) 0 with hneg | hzero | hpos
  · right
    rw [← dQ1_neg] at hz
    have hpos' : 0 < -Real.tan θ := by linarith
    have hlt : -Real.tan θ < 1 := by
      rcases (show -Real.tan θ ≤ 1 by linarith).lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hz) (dQ1_one_ne hq)
    rw [← dQ1_eq_deriv_dfun hq hpos'] at hz
    have h := (hcrit _ ⟨hpos', hlt⟩).mp hz
    rw [harc, ← h, arctan_neg, neg_neg]
  · exfalso
    rw [hzero, dQ1_zero hq] at hz
    exact one_ne_zero hz
  · left
    rw [← dQ1_eq_deriv_dfun hq hpos] at hz
    rw [harc, (hcrit _ ⟨hpos, htan1⟩).mp hz]

lemma crit_iff_aux (θ : ℝ) :
    deriv (qang q) θ = 0 ↔ ∃ k : ℤ, θ = arctan t + k * (π / 2) ∨ θ = -arctan t + k * (π / 2) := by
  constructor
  · intro h0
    obtain ⟨n, hn⟩ := exists_reduce θ
    rw [← deriv_qang_sub_int q θ n] at h0
    rcases eq_of_deriv_qang_eq_zero hq hcrit hn h0 with h | h
    · exact ⟨n, Or.inl (by linarith)⟩
    · exact ⟨n, Or.inr (by linarith)⟩
  · rintro ⟨k, h | h⟩
    · rw [← deriv_qang_sub_int q θ k, h, add_sub_cancel_right]
      exact deriv_qang_arctan hq ht hcrit
    · rw [← deriv_qang_sub_int q θ k, h, add_sub_cancel_right]
      exact deriv_qang_neg_arctan hq ht hcrit

end ThetaStar

/-! ## Strict concavity of `q` near `θ_*` -/

lemma contDiffAt_dfun {q s : ℝ} (hs : 0 < s) : ContDiffAt ℝ 2 (dfun q) s := by
  have h1 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ (q - 1)) s := contDiffAt_rpow_const_of_ne hs.ne'
  have h2 : ContDiffAt ℝ 2 (fun x : ℝ => x ^ q) s := contDiffAt_rpow_const_of_ne hs.ne'
  have hden : 1 + s ^ q ≠ 0 := by positivity
  exact (contDiffAt_id.sub h1).div (contDiffAt_const.add h2) hden

lemma contDiffOn_qang {q : ℝ} (hq : 1 < q) : ContDiffOn ℝ 2 (qang q) (Ioo 0 (π / 2)) := by
  intro θ hθ
  have hc : Real.cos θ ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩).ne'
  have hcomp : ContDiffAt ℝ 2 (fun x => dfun q (Real.tan x)) θ :=
    (contDiffAt_dfun (tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2)).comp θ (contDiffAt_tan.mpr hc)
  refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with x hx
  exact qang_eq_dfun_tan hq hx.1 hx.2

lemma differentiableAt_deriv_dfun {q s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ (deriv (dfun q)) s := by
  have hOn : ContDiffOn ℝ 2 (dfun q) (Ioi 0) := fun x hx => (contDiffAt_dfun hx).contDiffWithinAt
  have h1 : ContDiffOn ℝ 1 (deriv (dfun q)) (Ioi 0) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).mp hOn).2.2
  exact (h1.differentiableOn one_ne_zero).differentiableAt (Ioi_mem_nhds hs)

/-- `q''(θ_*) = d''(t_*) sec⁴ θ_* < 0`. -/
lemma deriv2_qang_arctan_neg {q t : ℝ} (hq : 2 < q) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcrit : ∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun q) s = 0 ↔ s = t) (hd2 : deriv (deriv (dfun q)) t < 0) :
    deriv (deriv (qang q)) (arctan t) < 0 := by
  have hθ0 : 0 < arctan t := by rw [← arctan_zero]; exact arctan_strictMono ht.1
  have hθ1 : arctan t < π / 2 := arctan_lt_pi_div_two t
  have hc : 0 < Real.cos (arctan t) := cos_arctan_pos t
  -- `q' = (d' ∘ tan) · sec²` near `θ_*`
  have hev : deriv (qang q) =ᶠ[𝓝 (arctan t)]
      fun θ => deriv (dfun q) (Real.tan θ) * (1 / Real.cos θ ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show arctan t ∈ Ioo 0 (π / 2) from ⟨hθ0, hθ1⟩)] with x hx
    rw [deriv_qang_of_cos_pos hq (cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], hx.2⟩),
      dQ1_eq_deriv_dfun hq (tan_pos_of_pos_of_lt_pi_div_two hx.1 hx.2)]
  rw [hev.deriv_eq]
  have hD : HasDerivAt (deriv (dfun q)) (deriv (deriv (dfun q)) (Real.tan (arctan t))) (Real.tan (arctan t)) := by
    rw [tan_arctan]; exact (differentiableAt_deriv_dfun ht.1).hasDerivAt
  have hS : DifferentiableAt ℝ (fun θ => 1 / Real.cos θ ^ 2) (arctan t) :=
    (differentiableAt_const _).div ((differentiableAt_cos).pow 2) (by positivity)
  have hprod : HasDerivAt (fun θ => deriv (dfun q) (Real.tan θ) * (1 / Real.cos θ ^ 2)) _ (arctan t) :=
    (hD.comp (arctan t) (hasDerivAt_tan hc.ne')).mul hS.hasDerivAt
  rw [hprod.deriv, Function.comp_apply, tan_arctan, (hcrit t ht).mpr rfl, zero_mul, add_zero]
  have : 0 < 1 / Real.cos (arctan t) ^ 2 := by positivity
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hd2 this) this

lemma concave_near_aux {q t : ℝ} (hq : 2 < q) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcrit : ∀ s ∈ Ioo (0 : ℝ) 1, deriv (dfun q) s = 0 ↔ s = t) (hd2 : deriv (deriv (dfun q)) t < 0) :
    ∃ ρ₀ m : ℝ, 0 < ρ₀ ∧ 0 < m ∧ ∀ θ ∈ Set.Icc (arctan t - ρ₀) (arctan t + ρ₀),
      DifferentiableAt ℝ (deriv (qang q)) θ ∧ deriv (deriv (qang q)) θ ≤ -m := by
  set v := deriv (deriv (qang q)) (arctan t) with hv
  have hvneg : v < 0 := deriv2_qang_arctan_neg hq ht hcrit hd2
  have hU : Ioo 0 (π / 2) ∈ 𝓝 (arctan t) := isOpen_Ioo.mem_nhds
    ⟨by rw [← arctan_zero]; exact arctan_strictMono ht.1, arctan_lt_pi_div_two t⟩
  have h1 : ContDiffOn ℝ 1 (deriv (qang q)) (Ioo 0 (π / 2)) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).mp (contDiffOn_qang (by linarith))).2.2
  have hcont : ContinuousAt (deriv (deriv (qang q))) (arctan t) :=
    (h1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).continuousAt hU
  have hlt : ∀ᶠ θ in 𝓝 (arctan t), θ ∈ Ioo 0 (π / 2) ∧ deriv (deriv (qang q)) θ < v / 2 :=
    (show ∀ᶠ θ in 𝓝 (arctan t), θ ∈ Ioo 0 (π / 2) from hU).and
      (hcont.preimage_mem_nhds (Iio_mem_nhds (by linarith)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hlt
  refine ⟨ε / 2, -(v / 2), by linarith, by linarith, fun θ hθ => ?_⟩
  have hdist : dist θ (arctan t) < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2]
  obtain ⟨hθU, hθv⟩ := hball hdist
  refine ⟨(h1.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hθU), ?_⟩
  rw [neg_neg]
  exact hθv.le

/-! ## `IsThetaStar` -/

theorem exists_isThetaStar (q : ℝ) (hq : 2 < q) : ∃ θs : ℝ, IsThetaStar q θs := by
  obtain ⟨t, ht, hcrit, hd2, hdpos, hle, hDstar, heq, -⟩ := lemma_3_3_proved q hq
  have hq1 : 1 < q := by linarith
  have hsa : Real.sin (arctan t) = t * Real.cos (arctan t) := by
    have h := tan_arctan t
    rwa [tan_eq_sin_div_cos, div_eq_iff (cos_arctan_pos t).ne'] at h
  have heq_at : qang q (arctan t) = Dstar q := by
    rw [qang_eq_Qf_tan hq1 (cos_arctan_pos t), tan_arctan, Qf_one q t ht.1, hDstar]
  refine ⟨arctan t, ⟨?_, ?_⟩, hDstar ▸ hdpos, fun θ => hDstar ▸ hle _ _ (cos_sin_ne θ), heq_at, ?_,
    differentiableAt_qang hq, crit_iff_aux hq ht hcrit, ?_, concave_near_aux hq ht hcrit hd2⟩
  · rw [← arctan_zero]; exact arctan_strictMono ht.1
  · rw [← arctan_one]; exact arctan_strictMono ht.2
  · intro θ
    constructor
    · intro h
      rw [hDstar] at h
      obtain ⟨r, -, hr⟩ := (heq _ _ (cos_sin_ne θ)).mp h
      rcases hr with hr | hr <;> simp only [Prod.mk.injEq] at hr <;> obtain ⟨hc, hs⟩ := hr
      · have h0 : Real.sin (θ - arctan t) = 0 := by rw [sin_sub, hc, hs, hsa]; ring
        obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h0
        refine ⟨2 * n, ?_⟩
        push_cast
        linear_combination -hn
      · have h0 : Real.cos (θ - arctan t) = 0 := by rw [cos_sub, hc, hs, hsa]; ring
        obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp h0
        refine ⟨2 * k + 1, ?_⟩
        push_cast
        linear_combination hk
    · rintro ⟨k, rfl⟩
      rw [(qang_periodic q).int_mul k (arctan t)]
      exact heq_at
  · intro k
    rw [(qang_periodic q).int_mul k (-arctan t), qang_neg, heq_at]

end Matsaev.Angle
