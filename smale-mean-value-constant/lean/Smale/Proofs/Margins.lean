/-
Smale/Proofs/Margins.lean — Remark 5.2 and the control of paper 009 (posted v1.90, tex l.433-442), proved from the
certificates SchurCertR.lean (Schur–Cohn for H'(r w), r = 1.00001141) and RoucheCert.lean (two Rouché certificates):
the zero of H' nearest to the circle has modulus 1.00001141…; at c = 0.9231 a zero of P_c has modulus between
1 + 7.02·10⁻⁶ and 1 + 7.03·10⁻⁶; for H(sz) the polynomials P_{±1} still have no zero in the closed disk, P_{0.9231} has
a zero in the open disk, and so (Lemma 4.1's count, Lemma 4.3's common zero) the resultant of (R) vanishes at some
c ∈ [-1, 1]; check (D) fails for H(sz).
-/
import Smale.Proofs.RoucheCert
import Smale.Proofs.SchurCertR
import Smale.Proofs.Schur
import Smale.Proofs.Count
import Smale.Proofs.Lem43
import Smale.Proofs.Star
import Smale.Proofs.Dieudonne
import Smale.Proofs.Parity
import Smale.Proofs.DataSec5
import Smale.Defs.Control

namespace Smale

open Polynomial Complex Metric ComplexConjugate

/-! ### H' -/

theorem Hder_eq : Hdata.derivative = Exact.toPoly (Exact.pderiv Exact.hGQ) := by
  rw [Exact.Hdata_eq, Exact.toPoly_pderiv]

theorem Hdata_natDegree_eq : Hdata.natDegree = 18 := Exact.sec5_Q_proved.2.2.2.2.2.2.2.2.2

theorem Hder_natDegree_le : Hdata.derivative.natDegree ≤ 17 := by
  have h := natDegree_derivative_le Hdata
  rw [Hdata_natDegree_eq] at h
  omega

/-- Remark 5.2 (tex l.434-435), the Schur–Cohn half: `H'` has no zero with `|z| ≤ 1.00001141`. -/
theorem Hder_ne_zero_of_le (z : ℂ) (hz : ‖z‖ ≤ 1.00001141) : Hdata.derivative.eval z ≠ 0 := by
  set r : ℚ := 100001141 / 100000000 with hr
  have hrC : (Exact.GQ.ofQ r).toC = ((1.00001141 : ℝ) : ℂ) := by
    rw [Exact.GQ.toC_ofQ, hr]; push_cast; norm_num
  have hf : Exact.toPoly (Exact.pcomp (Exact.pderiv Exact.hGQ) [Exact.GQ.zero, Exact.GQ.ofQ r]) =
      Hdata.derivative.comp (C ((1.00001141 : ℝ) : ℂ) * X) := by
    rw [Exact.toPoly_pcomp, Exact.toPoly_scale, hrC, ← Hder_eq]
  have hdeg : (Hdata.derivative.comp (C ((1.00001141 : ℝ) : ℂ) * X)).natDegree ≤ 17 := by
    refine natDegree_comp_le.trans ?_
    calc Hdata.derivative.natDegree * (C ((1.00001141 : ℝ) : ℂ) * X).natDegree ≤ 17 * 1 :=
          Nat.mul_le_mul Hder_natDegree_le ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      _ = 17 := by norm_num
  have hδ := Exact.hr_deltas
  rw [hf] at hδ
  have hnz := lem_4_2_b_proved _ 17 (by norm_num) hdeg hδ
  have hr0 : ((1.00001141 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hw : z / ((1.00001141 : ℝ) : ℂ) ∈ closedDisk := by
    rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [div_le_one (by norm_num)]; exact hz
  have h := hnz _ hw
  rwa [eval_comp, eval_mul, eval_C, eval_X, mul_div_cancel₀ z hr0] at h

/-- Remark 5.2, the Rouché half: `H'` has a zero `z` with `|z - zH| < 10⁻¹⁴`, hence `|z| < 1.00001142`. -/
theorem Hder_root_lt : ∃ z : ℂ, Hdata.derivative.eval z = 0 ∧ ‖z‖ < 1.00001142 := by
  have hT : ∀ u : ℂ, Hdata.derivative.eval (Exact.zH.toC + u) = (Exact.toPoly Exact.tH).eval u := by
    intro u
    rw [← Exact.toPoly_eq_of_peq Exact.tH_eq, Exact.eval_pcomp_shift, ← Hder_eq]
  obtain ⟨z, hz, hnear⟩ := Exact.exists_root_of_cert Exact.tH Exact.uH Exact.lH Exact.rRadius
    (by decide +kernel) (by decide +kernel) Exact.cH_l Exact.cH_us Exact.cH_sum _ _ hT
  have hzH := Exact.GQ.norm_le_of_nsq (by norm_num) Exact.cH_z.2
  refine ⟨z, hz, ?_⟩
  calc ‖z‖ = ‖(z - Exact.zH.toC) + Exact.zH.toC‖ := by ring_nf
    _ ≤ ‖z - Exact.zH.toC‖ + ‖Exact.zH.toC‖ := norm_add_le _ _
    _ < (Exact.rRadius : ℝ) + ‖Exact.zH.toC‖ := by linarith
    _ ≤ (Exact.rRadius : ℝ) + ((25000285389 / 25000000000 : ℚ) : ℝ) := by linarith
    _ < 1.00001142 := by norm_num [Exact.rRadius]

/-- Remark 5.2 (tex l.434-435): the zero of `H'` nearest to the circle has modulus `1.00001141…`. -/
theorem rem_5_2_Hprime_proved :
    ∃ z : ℂ, Hdata.derivative.eval z = 0 ∧ 1.00001141 ≤ ‖z‖ ∧ ‖z‖ < 1.00001142 ∧
      ∀ w : ℂ, Hdata.derivative.eval w = 0 → |‖z‖ - 1| ≤ |‖w‖ - 1| := by
  obtain ⟨z₁, hz₁, hz₁lt⟩ := Hder_root_lt
  have hne : Hdata.derivative ≠ 0 := fun h => Hder_ne_zero_of_le 0 (by norm_num) (by rw [h, eval_zero])
  have hmem : z₁ ∈ Hdata.derivative.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hne]; exact hz₁
  obtain ⟨z, hzS, hzmin⟩ := Hdata.derivative.roots.toFinset.exists_min_image (fun w => ‖w‖) ⟨z₁, hmem⟩
  rw [Multiset.mem_toFinset, mem_roots hne] at hzS
  have hlow : ∀ w : ℂ, Hdata.derivative.eval w = 0 → 1.00001141 < ‖w‖ := fun w hw =>
    lt_of_not_ge fun h => Hder_ne_zero_of_le w h hw
  refine ⟨z, hzS, (hlow z hzS).le, lt_of_le_of_lt (hzmin z₁ hmem) hz₁lt, fun w hw => ?_⟩
  have hzw : ‖z‖ ≤ ‖w‖ := hzmin w (by rw [Multiset.mem_toFinset, mem_roots hne]; exact hw)
  have h1 := hlow z hzS
  have h2 := hlow w hw
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
  linarith

/-! ### P_c at c = 0.9231 -/

theorem dieudonne_c0_eq :
    dieudonne Hdata 18 0.9231 = Exact.toPoly (Exact.pdieu Exact.hGQ 18 (9231 / 10000 : ℚ)) := by
  rw [← Exact.dieudonne_toPoly, ← Exact.Hdata_eq]; norm_num

/-- tex l.435-436 at `c = 0.9231`: `P_c` has a zero `z` with `1 + 7.02·10⁻⁶ < |z| < 1 + 7.03·10⁻⁶`. -/
theorem P_c0_root :
    ∃ z : ℂ, (dieudonne Hdata 18 0.9231).eval z = 0 ∧ 1.00000702 < ‖z‖ ∧ ‖z‖ < 1.00000703 := by
  have hT : ∀ u : ℂ, (dieudonne Hdata 18 0.9231).eval (Exact.zC.toC + u) = (Exact.toPoly Exact.tC).eval u := by
    intro u
    rw [← Exact.toPoly_eq_of_peq Exact.tC_eq, Exact.eval_pcomp_shift, dieudonne_c0_eq]
  obtain ⟨z, hz, hnear⟩ := Exact.exists_root_of_cert Exact.tC Exact.uC Exact.lC Exact.rRadius
    (by decide +kernel) (by decide +kernel) Exact.cC_l Exact.cC_us Exact.cC_sum _ _ hT
  have hzu := Exact.GQ.norm_le_of_nsq (by norm_num) Exact.cC_z.2
  have hzl := Exact.GQ.le_norm_of_nsq (by norm_num) Exact.cC_z.1
  refine ⟨z, hz, ?_, ?_⟩
  · have h : ‖Exact.zC.toC‖ ≤ ‖z‖ + ‖z - Exact.zC.toC‖ := by
      calc ‖Exact.zC.toC‖ = ‖z - (z - Exact.zC.toC)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖z - Exact.zC.toC‖ := norm_sub_le _ _
    have : (1.00000702 : ℝ) + Exact.rRadius < ((6250043931 / 6250000000 : ℚ) : ℝ) := by
      norm_num [Exact.rRadius]
    linarith
  · calc ‖z‖ = ‖(z - Exact.zC.toC) + Exact.zC.toC‖ := by ring_nf
      _ ≤ ‖z - Exact.zC.toC‖ + ‖Exact.zC.toC‖ := norm_add_le _ _
      _ < (Exact.rRadius : ℝ) + ((100000702897 / 100000000000 : ℚ) : ℝ) := by linarith
      _ < 1.00000703 := by norm_num [Exact.rRadius]

/-! ### The control `H(sz)` -/

theorem sCtrl_ne_zero : sCtrl ≠ 0 := by norm_num [sCtrl]

theorem norm_sCtrl : ‖sCtrl‖ = 1250009 / 1250000 := by
  rw [sCtrl, show (1250009 / 1250000 : ℂ) = ((1250009 / 1250000 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num)]

/-- The Dieudonné polynomials of `H(sz)` are `s P_c(sw)` (any `H`, `n`, `s`). -/
theorem dieudonne_comp_scale (H : ℂ[X]) (n : ℕ) (s : ℂ) (c : ℝ) (w : ℂ) :
    (dieudonne (H.comp (C s * X)) n c).eval w = s * (dieudonne H n c).eval (s * w) := by
  rw [eval_dieudonne, eval_dieudonne, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [comp_C_mul_X_coeff]
  ring

theorem Hctrl_natDegree_le : Hctrl.natDegree ≤ 18 := by
  refine natDegree_comp_le.trans ?_
  calc Hdata.natDegree * (C sCtrl * X).natDegree ≤ 18 * 1 :=
        Nat.mul_le_mul Hdata_natDegree_eq.le ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    _ = 18 := by norm_num

/-- `(H(sz))'(w) = s H'(sw)`. -/
theorem Hctrl_derivative_eval (w : ℂ) : Hctrl.derivative.eval w = sCtrl * Hdata.derivative.eval (sCtrl * w) := by
  rw [Hctrl, derivative_comp, eval_mul, eval_comp, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
    mul_one, eval_C, eval_mul, eval_C, eval_X, mul_comm]

/-- For `H(sz)` the derivative still has no zero in the closed disk (`s ≤ 1.00001141`). -/
theorem Hctrl_derivative_ne_zero (w : ℂ) (hw : w ∈ closedDisk) : Hctrl.derivative.eval w ≠ 0 := by
  rw [Hctrl_derivative_eval]
  refine mul_ne_zero sCtrl_ne_zero (Hder_ne_zero_of_le _ ?_)
  rw [norm_mul, norm_sCtrl]
  have hw1 : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.1 hw
  nlinarith [norm_nonneg w]

/-- tex l.440-441 ("but not the margin at `c = ±1`"): for `H(sz)`, `P_1` and `P_{-1}` have no zero in `𝔻̄`. -/
theorem ctrl_pm_one_proved (w : ℂ) (hw : w ∈ closedDisk) :
    (dieudonne Hctrl 18 1).eval w ≠ 0 ∧ (dieudonne Hctrl 18 (-1)).eval w ≠ 0 := by
  obtain ⟨h1, h2⟩ := rem_5_2_P_pm_one_proved Hctrl 18 Hctrl_natDegree_le w
  refine ⟨h1 ▸ Hctrl_derivative_ne_zero w hw, h2 ▸ Hctrl_derivative_ne_zero (-w) ?_⟩
  rw [mem_closedBall_zero_iff, norm_neg]; exact mem_closedBall_zero_iff.1 hw

/-- tex l.440-441 at `c = 0.9231` ("`s - 1` exceeds the margin"): the zero `z` of `P_c` gives the zero `z/s` of the
Dieudonné polynomial of `H(sz)`, inside `𝔻`. -/
theorem ctrl_zero_inside :
    ∃ w : ℂ, (dieudonne Hctrl 18 0.9231).eval w = 0 ∧ ‖w‖ < 1 := by
  obtain ⟨z, hz, -, hzlt⟩ := P_c0_root
  refine ⟨z / sCtrl, ?_, ?_⟩
  · rw [Hctrl, dieudonne_comp_scale, mul_div_cancel₀ z sCtrl_ne_zero, hz, mul_zero]
  · rw [norm_div, norm_sCtrl, div_lt_one (by norm_num)]
    linarith

/-- The control (tex l.441-442): "for these data the resultant in (R) has a zero in `[-1, 1]`". -/
theorem ctrl_R_fails_proved :
    ∃ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 ∧ resultant (dieudonne Hctrl 18 c) (dieudonneStar Hctrl 18 c) 17 17 = 0 := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hcirc : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 →
      (dieudonne Hctrl Hctrl.natDegree c).eval w ≠ 0 := by
    intro c hc w hw h0
    rw [← dieudonne_eq_natDegree _ 18 Hctrl_natDegree_le c] at h0
    exact hno c hc (lem_4_3_common_zero_proved Hctrl 18 (by norm_num) c w hw h0).2
  have hc0 : (0.9231 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hcount := lem_4_1_count_proved Hctrl Hctrl_derivative_ne_zero hcirc 0.9231 hc0
  rw [dieudonne_one Hctrl _ le_rfl] at hcount
  -- the right side is 0: `H(sz)'` has no zero in `𝔻`
  have hR0 : zerosInDisk Hctrl.derivative = 0 := by
    unfold zerosInDisk zerosInBall
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro w hw hlt
    have hne : Hctrl.derivative ≠ 0 := fun h => by simp [h] at hw
    exact Hctrl_derivative_ne_zero w (ball_subset_closedBall (by rw [mem_ball_zero_iff]; simpa using hlt))
      ((mem_roots hne).1 hw)
  -- the left side is positive: the zero inside `𝔻`
  obtain ⟨w, hw0, hw1⟩ := ctrl_zero_inside
  rw [dieudonne_eq_natDegree _ 18 Hctrl_natDegree_le] at hw0
  have hP0 : dieudonne Hctrl Hctrl.natDegree 0.9231 ≠ 0 := by
    intro h
    have h0 := dieudonne_eval_zero Hctrl Hctrl.natDegree ?_ 0.9231
    · rw [h, eval_zero] at h0
      have hd := Hctrl_derivative_ne_zero 0 (by simp)
      rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_derivative, ← h0] at hd
      simp at hd
    · by_contra hlt
      have : Hctrl.natDegree = 0 := by omega
      have hd := Hctrl_derivative_ne_zero 0 (by simp)
      rw [eq_C_of_natDegree_eq_zero this, derivative_C, eval_zero] at hd
      exact hd rfl
  have hpos : 0 < zerosInDisk (dieudonne Hctrl Hctrl.natDegree 0.9231) := by
    unfold zerosInDisk zerosInBall
    refine Multiset.card_pos_iff_exists_mem.2 ⟨w, Multiset.mem_filter.2 ⟨(mem_roots hP0).2 hw0, by simpa using hw1⟩⟩
  omega

/-- tex l.442: "check (D) fails too, since `H(sz)` no longer matches `Q`". -/
theorem ctrl_D_fails_proved : Hctrl * zerosPoly [a1D, a2D] ≠ Qdata * reflPoly [a1D, a2D] := by
  have hHQ := Exact.sec5_Q_proved.2.2.2.2.2.2.2.2.1
  intro h
  have hzp : zerosPoly [a1D, a2D] ≠ 0 := by
    simp only [zerosPoly, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  have heq : Hctrl = Hdata := mul_right_cancel₀ hzp (h.trans hHQ.symm)
  have hc := congrArg (fun p => p.coeff 18) heq
  simp only [Hctrl, comp_C_mul_X_coeff] at hc
  have hlc : Hdata.coeff 18 ≠ 0 := by
    have hne : Hdata ≠ 0 := by
      intro h0; have := Hdata_natDegree_eq; rw [h0, natDegree_zero] at this; exact absurd this (by norm_num)
    rw [← Hdata_natDegree_eq]; exact leadingCoeff_ne_zero.2 hne
  have hs : sCtrl ^ 18 = 1 := mul_left_cancel₀ hlc (hc.trans (mul_one _).symm)
  norm_num [sCtrl] at hs

end Smale
