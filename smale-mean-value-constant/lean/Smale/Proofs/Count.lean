/-
Smale/Proofs/Count.lean — Lemma 4.1, the step of the proof (tex l.251-253): if no `P_c` with `c ∈ [-1, 1]` has a
zero on the circle, the number of zeros of `P_c` in `𝔻` is the same for all `c`. By the argument principle for
polynomials (`Smale/Proofs/ArgPrinciple.lean`) this number is `(2πi)⁻¹ ∮ P_c'/P_c`, a continuous function of `c`; a
continuous function on `[-1, 1]` with values in ℕ is constant (it would take a half-integer value in between).
-/
import Smale.Proofs.ArgPrinciple
import Smale.Proofs.Dieudonne

namespace Smale

open Polynomial Complex Metric Set

theorem eval_derivative_dieudonne (H : ℂ[X]) (n : ℕ) (c : ℝ) (w : ℂ) :
    (dieudonne H n c).derivative.eval w =
      ∑ l ∈ Finset.range n, H.coeff (l + 1) * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ) * l * w ^ (l - 1) := by
  simp only [dieudonne, derivative_sum, derivative_C_mul_X_pow, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem continuous_eval_dieudonne (H : ℂ[X]) (n : ℕ) {Y : Type*} [TopologicalSpace Y] {c : Y → ℝ} {w : Y → ℂ}
    (hc : Continuous c) (hw : Continuous w) : Continuous fun y => (dieudonne H n (c y)).eval (w y) := by
  simp only [eval_dieudonne]
  exact continuous_finsetSum _ fun l _ =>
    (continuous_const.mul (continuous_ofReal.comp ((Chebyshev.U ℝ (l : ℤ)).continuous.comp hc))).mul (hw.pow l)

theorem continuous_eval_derivative_dieudonne (H : ℂ[X]) (n : ℕ) {Y : Type*} [TopologicalSpace Y] {c : Y → ℝ}
    {w : Y → ℂ} (hc : Continuous c) (hw : Continuous w) :
    Continuous fun y => (dieudonne H n (c y)).derivative.eval (w y) := by
  simp only [eval_derivative_dieudonne]
  exact continuous_finsetSum _ fun l _ =>
    ((continuous_const.mul (continuous_ofReal.comp ((Chebyshev.U ℝ (l : ℤ)).continuous.comp hc))).mul
      continuous_const).mul (hw.pow (l - 1))

/-- `c ↦ ∮ P_c'/P_c` is continuous on `[-1, 1]` when no `P_c` vanishes on the circle. -/
theorem continuousOn_circleIntegral_dieudonne (H : ℂ[X]) (n : ℕ)
    (hcirc : ∀ c : ℝ, c ∈ Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 → (dieudonne H n c).eval w ≠ 0) :
    ContinuousOn (fun c : ℝ => circleIntegral
      (fun w => (dieudonne H n c).derivative.eval w / (dieudonne H n c).eval w) 0 1) (Icc (-1 : ℝ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun p : Icc (-1 : ℝ) 1 × ℝ => (p.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have hw : Continuous fun p : Icc (-1 : ℝ) 1 × ℝ => circleMap 0 1 p.2 :=
    (continuous_circleMap 0 1).comp continuous_snd
  have hden : ∀ p : Icc (-1 : ℝ) 1 × ℝ, (dieudonne H n p.1).eval (circleMap 0 1 p.2) ≠ 0 := fun p =>
    hcirc p.1 p.1.2 _ (by rw [norm_circleMap_zero, abs_one])
  have hint : Continuous (Function.uncurry fun (x : Icc (-1 : ℝ) 1) (θ : ℝ) =>
      deriv (circleMap 0 1) θ • ((dieudonne H n x).derivative.eval (circleMap 0 1 θ) /
        (dieudonne H n x).eval (circleMap 0 1 θ))) := by
    simp only [Function.uncurry_def, deriv_circleMap, smul_eq_mul]
    exact (hw.mul continuous_const).mul ((continuous_eval_derivative_dieudonne H n hc hw).div
      (continuous_eval_dieudonne H n hc hw) hden)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hint 0 (2 * Real.pi)

/-- Between two different naturals there is a half-integer. -/
theorem exists_half_mem_uIcc {a b : ℕ} (hab : a ≠ b) : ∃ m : ℕ, (m : ℝ) + 1 / 2 ∈ uIcc (a : ℝ) b := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · refine ⟨a, ?_⟩
    rw [uIcc_of_le (by exact_mod_cast h.le)]
    have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    constructor <;> linarith
  · refine ⟨b, ?_⟩
    rw [uIcc_of_ge (by exact_mod_cast h.le)]
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    constructor <;> linarith

theorem natCast_ne_half (m k : ℕ) : (k : ℝ) ≠ m + 1 / 2 := fun h => by
  have h2 : (2 * k : ℝ) = 2 * m + 1 := by linarith
  have h3 : 2 * k = 2 * m + 1 := by exact_mod_cast h2
  omega

/-- Lemma 4.1, the step of the proof (tex l.248-250), exactly the Statements type. -/
theorem lem_4_1_count_proved (H : ℂ[X]) (_hH' : ∀ w ∈ closedDisk, H.derivative.eval w ≠ 0)
    (hcirc : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 → (dieudonne H H.natDegree c).eval w ≠ 0) :
    ∀ c ∈ Set.Icc (-1 : ℝ) 1,
      zerosInDisk (dieudonne H H.natDegree c) = zerosInDisk (dieudonne H H.natDegree 1) := by
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  let g : ℝ → ℝ := fun c => (zerosInDisk (dieudonne H H.natDegree c) : ℝ)
  have hg : EqOn g (fun c => (circleIntegral (fun w => (dieudonne H H.natDegree c).derivative.eval w /
      (dieudonne H H.natDegree c).eval w) 0 1 / (2 * Real.pi * I)).re) (Icc (-1 : ℝ) 1) := by
    intro c hc
    show (zerosInDisk (dieudonne H H.natDegree c) : ℝ) = _
    dsimp only
    rw [circleIntegral_logDeriv _ (hcirc c hc), mul_div_cancel_left₀ _ h2pi, natCast_re]
  have hcont : ContinuousOn g (Icc (-1 : ℝ) 1) :=
    (continuous_re.comp_continuousOn
      ((continuousOn_circleIntegral_dieudonne H H.natDegree hcirc).div_const _)).congr hg
  intro c hc
  by_contra hne
  have h1 : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  obtain ⟨m, hm⟩ := exists_half_mem_uIcc hne
  obtain ⟨c', -, hc'⟩ := intermediate_value_uIcc (hcont.mono (uIcc_subset_Icc hc h1)) hm
  exact natCast_ne_half m _ hc'

/-- Lemma 4.1 (tex l.244-252), from the paper's extension of Dieudonné's criterion (the claim `sec4_dieudonne_any`,
taken as the hypothesis `hany` with exactly its Statements type): the count of zeros of `P_c` in `𝔻` is that of
`P₁ = H'`, which is `0`, so no `P_c` has a zero in `𝔻`. -/
theorem lem_4_1_of
    (hany : ∀ H : ℂ[X], (∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) →
      IsUnivalentOn (fun z => H.eval z) disk)
    (H : ℂ[X]) (hH' : ∀ w ∈ closedDisk, H.derivative.eval w ≠ 0)
    (hcirc : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 → (dieudonne H H.natDegree c).eval w ≠ 0) :
    IsUnivalentOn (fun z => H.eval z) disk := by
  apply hany H
  intro c hc w hw h0
  have hcount := lem_4_1_count_proved H hH' hcirc c hc
  rw [dieudonne_one H _ le_rfl] at hcount
  have hH0 : zerosInDisk H.derivative = 0 := by
    rw [zerosInDisk_eq, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro x hx hxlt
    exact hH' x (mem_closedBall_zero_iff.2 hxlt.le) (mem_roots'.1 hx).2
  rw [hH0, zerosInDisk_eq, Multiset.card_eq_zero, Multiset.filter_eq_nil] at hcount
  exact hcount w ((mem_roots (ne_zero_of_circle (hcirc c hc))).2 h0) (mem_ball_zero_iff.1 hw)

end Smale
