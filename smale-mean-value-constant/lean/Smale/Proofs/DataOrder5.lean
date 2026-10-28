/-
Smale/Proofs/DataOrder5.lean — `sec5_order5`: `Q'` has a zero of order 5 at `z = 1`, and `(WB)'` of our pair has a zero
of order 5 at `w₁ = φ_{-b}(1)` on the unit circle. Near `w₁`, `W B = κ Q∘φ_b` (κ ≠ 0), so `(WB)' = κ Q'(φ_b) φ_b'`;
`φ_b(w₁) = 1` and `φ_b'(w₁) ≠ 0`, and `Q' = (z - 1)⁵ V` with `V(1) ≠ 0`.
-/
import Smale.Proofs.DataSec5

namespace Smale.Exact

open Polynomial Complex ComplexConjugate Filter Topology

/-- `w₁ = φ_{-b}(1)`. -/
noncomputable def w1 : ℂ := diskAut (-bD) 1

theorem norm_bD_lt : ‖bD‖ < 1 := data_D.1 bD (by simp)
theorem norm_a1D_lt : ‖a1D‖ < 1 := data_D.1 a1D (by simp)
theorem norm_a2D_lt : ‖a2D‖ < 1 := data_D.1 a2D (by simp)

theorem one_sub_conj_mul_ne {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) : 1 - conj a * z ≠ 0 := by
  intro h
  have h1 : conj a * z = 1 := by linear_combination -h
  have h2 : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg a)
      _ < 1 := by rw [mul_one]; exact ha
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

theorem one_sub_bconjb_ne : (1 : ℂ) - bD * conj bD ≠ 0 := by
  rw [mul_comm]; exact one_sub_conj_mul_ne norm_bD_lt norm_bD_lt.le

theorem w1_eq : w1 = (1 - bD) / (1 - conj bD) := by
  simp only [w1, diskAut, map_neg]; ring

theorem one_sub_conj_bD_ne : (1 : ℂ) - conj bD ≠ 0 := by
  simpa using one_sub_conj_mul_ne (z := 1) norm_bD_lt (by simp)

theorem norm_w1 : ‖w1‖ = 1 := by
  have hc : ‖(1 : ℂ) - conj bD‖ = ‖1 - bD‖ := by rw [← Complex.norm_conj (1 - bD), map_sub, map_one]
  have hne : ‖(1 : ℂ) - conj bD‖ ≠ 0 := norm_ne_zero_iff.mpr one_sub_conj_bD_ne
  rw [w1_eq, norm_div, ← hc, div_self hne]

theorem den_w1_ne : 1 + conj bD * w1 ≠ 0 := by
  rw [w1_eq]
  have h := one_sub_conj_bD_ne
  intro h0
  apply one_sub_bconjb_ne
  field_simp at h0
  linear_combination h0

theorem diskAut_w1 : diskAut bD w1 = 1 := by
  have h := den_w1_ne
  rw [diskAut, div_eq_one_iff_eq h, w1_eq]
  have h1 := one_sub_conj_bD_ne
  field_simp
  ring

theorem hasDerivAt_diskAut_explicit (b w : ℂ) (hw : 1 + conj b * w ≠ 0) :
    HasDerivAt (diskAut b) ((1 - b * conj b) / (1 + conj b * w) ^ 2) w := by
  have h1 : HasDerivAt (fun w => w + b) 1 w := (hasDerivAt_id w).add_const b
  have h2 : HasDerivAt (fun w => 1 + conj b * w) (conj b) w := by
    simpa using ((hasDerivAt_id w).const_mul (conj b)).const_add 1
  have e : diskAut b = fun w => (w + b) / (1 + conj b * w) := rfl
  rw [e]
  convert h1.div h2 hw using 2
  ring

theorem analyticAt_diskAut (b w : ℂ) (hw : 1 + conj b * w ≠ 0) : AnalyticAt ℂ (diskAut b) w := by
  have e : diskAut b = fun w => (w + b) / (1 + conj b * w) := rfl
  rw [e]
  exact (analyticAt_id.add analyticAt_const).div (analyticAt_const.add (analyticAt_const.mul analyticAt_id)) hw

/-- The constant `κ = (|η|/η)/N` of Lemma 3.1 for our pair. -/
noncomputable def kappa : ℂ := ((‖etaOf [a1D, a2D] bD‖ : ℂ) / etaOf [a1D, a2D] bD) / NOf Qdata [a1D, a2D] bD

theorem eta_ne : etaOf [a1D, a2D] bD ≠ 0 := by
  have hb1 : bD - a1D ≠ 0 := sub_ne_zero.mpr (fun h => by
    have := data_D.2.1; simp [h] at this)
  have hb2 : bD - a2D ≠ 0 := sub_ne_zero.mpr (fun h => by
    have := data_D.2.1; simp [h] at this)
  simp only [etaOf, blaschkeFactor, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact mul_ne_zero (div_ne_zero hb1 (one_sub_conj_mul_ne norm_a1D_lt norm_bD_lt.le))
    (div_ne_zero hb2 (one_sub_conj_mul_ne norm_a2D_lt norm_bD_lt.le))

theorem Hder_b_ne : Hdata.derivative.eval bD ≠ 0 := by
  have h : peval (pderiv hGQ) bGQ ≠ GQ.zero := by decide +kernel
  rw [Hdata_eq, ← toPoly_pderiv, bD_eq, eval_toPoly]
  exact (GQ.toC_eq_zero_iff _).not.mpr h

theorem kappa_ne : kappa ≠ 0 := by
  have hN : NOf Qdata [a1D, a2D] bD ≠ 0 := by
    rw [NOf]
    refine mul_ne_zero ?_ Hder_b_ne
    have : ‖bD‖ ^ 2 < 1 := by nlinarith [norm_bD_lt, norm_nonneg bD]
    intro h
    have h' : ((1 - ‖bD‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    rw [Complex.ofReal_eq_zero] at h'
    linarith
  have heta := eta_ne
  have hn : (‖etaOf [a1D, a2D] bD‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr heta
  exact div_ne_zero (div_ne_zero hn heta) hN

theorem WB_eq (w : ℂ) (h1 : 1 - conj a1D * diskAut bD w ≠ 0) (h2 : 1 - conj a2D * diskAut bD w ≠ 0) :
    WOf Qdata [a1D, a2D] bD w * BOf [a1D, a2D] bD w = kappa * Qdata.eval (diskAut bD w) := by
  have hid := congrArg (eval (diskAut bD w)) Hdata_mul_zeros
  simp only [eval_mul, zerosPoly, reflPoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, eval_sub,
    eval_X, eval_C, eval_one, mul_one] at hid
  have key : Hdata.eval (diskAut bD w) * ((diskAut bD w - a1D) / (1 - conj a1D * diskAut bD w) *
      ((diskAut bD w - a2D) / (1 - conj a2D * diskAut bD w))) = Qdata.eval (diskAut bD w) := by
    have hD : (1 - conj a1D * diskAut bD w) * (1 - conj a2D * diskAut bD w) ≠ 0 := mul_ne_zero h1 h2
    rw [div_mul_div_comm, ← mul_div_assoc, div_eq_iff hD]
    linear_combination hid
  calc WOf Qdata [a1D, a2D] bD w * BOf [a1D, a2D] bD w
      = ((‖etaOf [a1D, a2D] bD‖ : ℂ) / etaOf [a1D, a2D] bD) / NOf Qdata [a1D, a2D] bD *
          (Hdata.eval (diskAut bD w) * ((diskAut bD w - a1D) / (1 - conj a1D * diskAut bD w) *
            ((diskAut bD w - a2D) / (1 - conj a2D * diskAut bD w)))) := by
        simp only [WOf, BOf, blaschkeFactor, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [show Hpoly Qdata [a1D, a2D] = Hdata from rfl]
        ring
    _ = kappa * Qdata.eval (diskAut bD w) := by rw [key, kappa]

theorem WB_eventually : (fun w => WOf Qdata [a1D, a2D] bD w * BOf [a1D, a2D] bD w) =ᶠ[𝓝 w1]
    fun w => kappa * Qdata.eval (diskAut bD w) := by
  have hc : ContinuousAt (diskAut bD) w1 := (hasDerivAt_diskAut_explicit bD w1 den_w1_ne).continuousAt
  have c1 : ContinuousAt (fun w => 1 - conj a1D * diskAut bD w) w1 := continuousAt_const.sub (continuousAt_const.mul hc)
  have c2 : ContinuousAt (fun w => 1 - conj a2D * diskAut bD w) w1 := continuousAt_const.sub (continuousAt_const.mul hc)
  have e1 : ∀ᶠ w in 𝓝 w1, 1 - conj a1D * diskAut bD w ≠ 0 := by
    refine c1.eventually_ne ?_
    show 1 - conj a1D * diskAut bD w1 ≠ 0
    rw [diskAut_w1]; exact one_sub_conj_mul_ne norm_a1D_lt (by simp)
  have e2 : ∀ᶠ w in 𝓝 w1, 1 - conj a2D * diskAut bD w ≠ 0 := by
    refine c2.eventually_ne ?_
    show 1 - conj a2D * diskAut bD w1 ≠ 0
    rw [diskAut_w1]; exact one_sub_conj_mul_ne norm_a2D_lt (by simp)
  filter_upwards [e1, e2] with w h1 h2 using WB_eq w h1 h2

/-- `(WB)'` near `w₁`, as an explicit product. -/
noncomputable def dWB (w : ℂ) : ℂ :=
  (kappa * ((1 - bD * conj bD) / (1 + conj bD * w) ^ 2)) * Qdata.derivative.eval (diskAut bD w)

theorem deriv_WB_eventually :
    deriv (fun w => WOf Qdata [a1D, a2D] bD w * BOf [a1D, a2D] bD w) =ᶠ[𝓝 w1] dWB := by
  have hden : ∀ᶠ w in 𝓝 w1, 1 + conj bD * w ≠ 0 :=
    (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne den_w1_ne
  filter_upwards [WB_eventually.deriv, hden] with w hw hd
  rw [hw]
  have h : HasDerivAt (fun w => kappa * Qdata.eval (diskAut bD w))
      (kappa * (Qdata.derivative.eval (diskAut bD w) * ((1 - bD * conj bD) / (1 + conj bD * w) ^ 2))) w :=
    ((Qdata.hasDerivAt (diskAut bD w)).comp w (hasDerivAt_diskAut_explicit bD w hd)).const_mul kappa
  rw [h.deriv, dWB]; ring

theorem Vdata_one_ne : Vdata.eval 1 ≠ 0 := by
  have h : peval vGQ one ≠ GQ.zero := by decide +kernel
  rw [Vdata_eq, ← toC_one, eval_toPoly]
  exact (GQ.toC_eq_zero_iff _).not.mpr h

theorem order_Qderiv : analyticOrderAt (fun z => Qdata.derivative.eval z) 1 = 5 := by
  show analyticOrderAt (fun z => Qdata.derivative.eval z) 1 = ((5 : ℕ) : ℕ∞)
  rw [(Qdata.derivative.differentiable.analyticAt 1).analyticOrderAt_eq_natCast]
  refine ⟨fun z => Vdata.eval z, Vdata.differentiable.analyticAt 1, Vdata_one_ne, Eventually.of_forall fun z => ?_⟩
  rw [Qdata_derivative_eq_V, eval_mul, eval_pow, eval_sub, eval_X, eval_one, smul_eq_mul]

theorem order_dWB : analyticOrderAt dWB w1 = 5 := by
  have hφ := analyticAt_diskAut bD w1 den_w1_ne
  have hφ' : deriv (diskAut bD) w1 ≠ 0 := by
    rw [(hasDerivAt_diskAut_explicit bD w1 den_w1_ne).deriv]
    exact div_ne_zero one_sub_bconjb_ne (pow_ne_zero 2 den_w1_ne)
  have hf : AnalyticAt ℂ (fun w => kappa * ((1 - bD * conj bD) / (1 + conj bD * w) ^ 2)) w1 :=
    analyticAt_const.mul (analyticAt_const.div ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).pow 2)
      (pow_ne_zero 2 den_w1_ne))
  have hg : AnalyticAt ℂ ((fun z => Qdata.derivative.eval z) ∘ diskAut bD) w1 :=
    (Qdata.derivative.differentiable.analyticAt _).comp hφ
  have e : dWB = (fun w => kappa * ((1 - bD * conj bD) / (1 + conj bD * w) ^ 2)) *
      ((fun z => Qdata.derivative.eval z) ∘ diskAut bD) := by
    funext w; simp [dWB]
  rw [e, analyticOrderAt_mul hf hg, analyticOrderAt_comp_of_deriv_ne_zero hφ hφ', diskAut_w1, order_Qderiv]
  have h0 : analyticOrderAt (fun w => kappa * ((1 - bD * conj bD) / (1 + conj bD * w) ^ 2)) w1 = 0 := by
    rw [analyticOrderAt_eq_zero]
    right
    exact mul_ne_zero kappa_ne (div_ne_zero one_sub_bconjb_ne (pow_ne_zero 2 den_w1_ne))
  rw [h0, zero_add]

theorem rootMultiplicity_Qderiv : Qdata.derivative.rootMultiplicity 1 = 5 := by
  have hV : Vdata ≠ 0 := fun h => Vdata_one_ne (by rw [h, eval_zero])
  rw [Qdata_derivative_eq_V, mul_comm, show (X - 1 : ℂ[X]) = X - C 1 by rw [map_one],
    rootMultiplicity_mul_X_sub_C_pow hV, rootMultiplicity_eq_zero (show ¬ Vdata.IsRoot 1 from Vdata_one_ne), zero_add]

/-- `sec5_order5`, proved. -/
theorem sec5_order5_proved :
    Qdata.derivative.rootMultiplicity 1 = 5 ∧ ‖diskAut (-bD) 1‖ = 1 ∧ diskAut bD (diskAut (-bD) 1) = 1 ∧
      deriv (fun z => WOf Qdata [a1D, a2D] bD z * BOf [a1D, a2D] bD z) (diskAut (-bD) 1) = 0 ∧
      analyticOrderAt (deriv (fun z => WOf Qdata [a1D, a2D] bD z * BOf [a1D, a2D] bD z)) (diskAut (-bD) 1) = 5 := by
  have hd := deriv_WB_eventually
  refine ⟨rootMultiplicity_Qderiv, norm_w1, diskAut_w1, ?_, ?_⟩
  · rw [show diskAut (-bD) 1 = w1 from rfl, hd.eq_of_nhds, dWB, diskAut_w1]
    have : Qdata.derivative.eval 1 = 0 := by
      rw [Qdata_derivative_eq_V]; simp
    rw [this, mul_zero]
  · rw [show diskAut (-bD) 1 = w1 from rfl, analyticOrderAt_congr hd, order_dWB]

end Smale.Exact
