/-
Matsaev/Assembly/Qexp.lean — two claims of Sections 1 and 3: `‖P_0(J)‖_p = ‖P_0(S)‖_p = 1 + B` for `P_0(z) = 1 - Bz²`
(Idea of the proof of Theorem A) and eq. `eq:Qexp`, `‖P_a(J)ξ‖_p^p = (1+B)^p‖ξ‖_p^p(1 + pa/(1+B) Q(ξ)) + O(a²)‖ξ‖_p^p`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

eq:Qexp: a global Taylor bound for `|y|^q`, `q > 2` (`abs_rpow_taylor`, two mean value steps, `φ' = (q-1)|y|^(q-2)`), applied
to both coordinates of `P_a(J)ξ = ((1+B)u + av, (1+B)v - au)`, with `O(a²)` made explicit: `K = 2q(q-1)(2+B)^(q-2)`, `|a| ≤ 1`.
-/
import Matsaev.Angle.Basic
import Matsaev.SJ.PowLib
import Matsaev.ThmB.Basic

namespace Matsaev.Qexp

open Matsaev Matsaev.Angle Set
open scoped ENNReal
open Polynomial

variable {q : ℝ}

/-- `|s| ≤ |x| + |h|` on the segment from `x` to `x + t h`, `0 ≤ t ≤ 1`. -/
lemma abs_le_of_mem_seg {x h t s : ℝ} (ht : t ∈ uIcc (0 : ℝ) 1) (hs : s ∈ uIcc x (x + t * h)) : |s| ≤ |x| + |h| := by
  rw [uIcc_of_le zero_le_one] at ht
  have hth : |t * h| ≤ |h| := by
    rw [abs_mul, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_left (abs_nonneg h) ht.2
  have h1 := neg_abs_le (t * h)
  have h2 := le_abs_self (t * h)
  rw [mem_uIcc] at hs
  rw [abs_le]
  constructor
  · rcases hs with hs | hs <;> linarith [neg_abs_le x, le_abs_self x]
  · rcases hs with hs | hs <;> linarith [neg_abs_le x, le_abs_self x]

/-- Global Taylor bound for `|y|^q`, `q > 2`: `||x+h|^q - |x|^q - qφ(x)h| ≤ q(q-1)(|x|+|h|)^(q-2) h²`. -/
lemma abs_rpow_taylor (hq : 2 < q) (x h : ℝ) :
    |(|x + h| ^ q - |x| ^ q - q * phi q x * h)| ≤ q * ((q - 1) * (|x| + |h|) ^ (q - 2)) * h ^ 2 := by
  set M := (q - 1) * (|x| + |h|) ^ (q - 2) with hMdef
  have hq1 : 0 ≤ q - 1 := by linarith
  have hq2 : 0 ≤ q - 2 := by linarith
  have hM : 0 ≤ M := mul_nonneg hq1 (Real.rpow_nonneg (by positivity) _)
  have hφ : ∀ t ∈ uIcc (0 : ℝ) 1, |phi q (x + t * h) - phi q x| ≤ M * |t * h| := by
    intro t ht
    have := SJ.mvt_abs (f := phi q) (f' := fun s => (q - 1) * |s| ^ (q - 2)) (a := x) (b := x + t * h) (C := M)
      (fun s _ => hasDerivAt_phi hq s) (fun s hs => by
        rw [abs_of_nonneg (mul_nonneg hq1 (Real.rpow_nonneg (abs_nonneg s) _))]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg s) (abs_le_of_mem_seg ht hs) hq2) hq1)
    simpa using this
  have hf : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => |x + t * h| ^ q - t * (q * phi q x * h))
      (q * phi q (x + t * h) * h - q * phi q x * h) t := by
    intro t _
    have h1 : HasDerivAt (fun t => |x + t * h| ^ q) (q * phi q (x + t * h) * h) t := by
      have := (hasDerivAt_absRpow (q := q) (by linarith) (x + t * h)).comp t
        (((hasDerivAt_id' t).mul_const h).const_add x)
      convert this using 1
      · funext s
        simp only [Function.comp_apply]
      · ring
    have h2 : HasDerivAt (fun t => t * (q * phi q x * h)) (1 * (q * phi q x * h)) t :=
      (hasDerivAt_id' t).mul_const _
    convert h1.sub h2 using 1
    ring
  have hC : ∀ t ∈ uIcc (0 : ℝ) 1, |q * phi q (x + t * h) * h - q * phi q x * h| ≤ q * M * h ^ 2 := by
    intro t ht
    have ht' := ht
    rw [uIcc_of_le zero_le_one] at ht'
    have hth : |t * h| ≤ |h| := by
      rw [abs_mul, abs_of_nonneg ht'.1]
      exact mul_le_of_le_one_left (abs_nonneg h) ht'.2
    rw [show q * phi q (x + t * h) * h - q * phi q x * h = q * h * (phi q (x + t * h) - phi q x) by ring,
      abs_mul, abs_mul, abs_of_pos (by linarith : 0 < q)]
    calc q * |h| * |phi q (x + t * h) - phi q x| ≤ q * |h| * (M * |t * h|) :=
          mul_le_mul_of_nonneg_left (hφ t ht) (by positivity)
      _ ≤ q * |h| * (M * |h|) := by gcongr
      _ = q * M * h ^ 2 := by rw [← sq_abs h]; ring
  have := SJ.mvt_abs hf hC
  simp only [zero_mul, add_zero, one_mul, sub_zero, abs_one, mul_one] at this
  rw [show |x + h| ^ q - |x| ^ q - q * phi q x * h = |x + h| ^ q - 1 * (q * phi q x * h) - |x| ^ q by ring]
  simpa [hMdef, mul_assoc] using this

/-- `φ(cy) = c^(q-1) φ(y)` for `c > 0`. -/
lemma phi_mul_pos {c : ℝ} (hc : 0 < c) (y : ℝ) : phi q (c * y) = c ^ (q - 1) * phi q y := by
  unfold phi
  rw [sign_mul, sign_pos hc, one_mul, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg y)]
  ring

/-- The `O(a²)` term of one coordinate: for `|X| ≤ (1+B)m`, `|H| ≤ |a|m`, `|a| ≤ 1`:
`(|X| + |H|)^(q-2) H² ≤ (2+B)^(q-2) a² m^q`. -/
lemma rem_le (hq : 2 < q) {B a m X H : ℝ} (hB : 0 < B) (ha : |a| ≤ 1) (hm : 0 ≤ m) (hX : |X| ≤ (1 + B) * m)
    (hH : |H| ≤ |a| * m) : (|X| + |H|) ^ (q - 2) * H ^ 2 ≤ (2 + B) ^ (q - 2) * a ^ 2 * m ^ q := by
  have hsum : |X| + |H| ≤ (2 + B) * m := by nlinarith [abs_nonneg a]
  have h1 : (|X| + |H|) ^ (q - 2) ≤ (2 + B) ^ (q - 2) * m ^ (q - 2) := by
    rw [← Real.mul_rpow (by linarith) hm]
    exact Real.rpow_le_rpow (by positivity) hsum (by linarith)
  have h2 : H ^ 2 ≤ a ^ 2 * m ^ 2 := by
    rw [← sq_abs H, ← sq_abs a, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg H) hH 2
  have hmq : m ^ (q - 2) * m ^ 2 = m ^ q := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_add' hm (by norm_num; linarith)]
    norm_num
  calc (|X| + |H|) ^ (q - 2) * H ^ 2 ≤ ((2 + B) ^ (q - 2) * m ^ (q - 2)) * (a ^ 2 * m ^ 2) :=
        mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    _ = (2 + B) ^ (q - 2) * a ^ 2 * (m ^ (q - 2) * m ^ 2) := by ring
    _ = (2 + B) ^ (q - 2) * a ^ 2 * m ^ q := by rw [hmq]

/-- **eq. `eq:Qexp`**, coordinates: for `q > 2`, `B > 0`, `|a| ≤ 1` and `ξ = (u, v)`,
`|‖P_a(J)ξ‖_q^q - (1+B)^q‖ξ‖_q^q(1 + qa/(1+B) Q(ξ))| ≤ K a² ‖ξ‖_q^q` with `K = 2q(q-1)(2+B)^(q-2)`. -/
theorem qexp (hq : 2 < q) (B : ℝ) (hB : 0 < B) (a : ℝ) (ha : |a| ≤ 1) (u v : ℝ) :
    |(|(1 + B) * u + a * v| ^ q + |(1 + B) * v - a * u| ^ q) -
        (1 + B) ^ q * (|u| ^ q + |v| ^ q) * (1 + q * a / (1 + B) * Qf q u v)| ≤
      2 * q * (q - 1) * (2 + B) ^ (q - 2) * a ^ 2 * (|u| ^ q + |v| ^ q) := by
  have hB1 : 0 < 1 + B := by linarith
  have hq0 : 0 < q := by linarith
  set m := max |u| |v| with hmdef
  have hm : 0 ≤ m := le_max_of_le_left (abs_nonneg u)
  have hmq : m ^ q ≤ |u| ^ q + |v| ^ q := by
    rcases max_choice |u| |v| with h | h <;> rw [hmdef, h]
    · linarith [Real.rpow_nonneg (abs_nonneg v) q]
    · linarith [Real.rpow_nonneg (abs_nonneg u) q]
  have T1 := abs_rpow_taylor hq ((1 + B) * u) (a * v)
  have T2 := abs_rpow_taylor hq ((1 + B) * v) (-(a * u))
  have R1 := rem_le hq hB ha hm (X := (1 + B) * u) (H := a * v)
    (by rw [abs_mul, abs_of_pos hB1]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hB1.le)
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg a))
  have R2 := rem_le hq hB ha hm (X := (1 + B) * v) (H := -(a * u))
    (by rw [abs_mul, abs_of_pos hB1]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) hB1.le)
    (by rw [abs_neg, abs_mul]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg a))
  -- the first-order term
  have hpow : ∀ y : ℝ, |(1 + B) * y| ^ q = (1 + B) ^ q * |y| ^ q := fun y => by
    rw [abs_mul, abs_of_pos hB1, Real.mul_rpow hB1.le (abs_nonneg y)]
  have hfirst : (1 + B) ^ q * (|u| ^ q + |v| ^ q) * (1 + q * a / (1 + B) * Qf q u v) =
      |(1 + B) * u| ^ q + |(1 + B) * v| ^ q +
        (q * phi q ((1 + B) * u) * (a * v) + q * phi q ((1 + B) * v) * (-(a * u))) := by
    rw [hpow, hpow, phi_mul_pos hB1, phi_mul_pos hB1]
    have hq1 : (1 + B) ^ q = (1 + B) * (1 + B) ^ (q - 1) := by
      rw [Real.rpow_sub_one hB1.ne']
      field_simp
    rcases eq_or_ne (|u| ^ q + |v| ^ q) 0 with hN | hN
    · have hu : u = 0 := by
        have := Real.rpow_nonneg (abs_nonneg v) q
        have h0 : |u| ^ q = 0 := by linarith [Real.rpow_nonneg (abs_nonneg u) q]
        exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg u) hq0.ne').mp h0)
      have hv : v = 0 := by
        have h0 : |v| ^ q = 0 := by
          linarith [Real.rpow_nonneg (abs_nonneg u) q, Real.rpow_nonneg (abs_nonneg v) q]
        exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg v) hq0.ne').mp h0)
      subst hu hv
      simp [phi_zero, Real.zero_rpow hq0.ne']
    · have hQ : (|u| ^ q + |v| ^ q) * Qf q u v = phi q u * v - phi q v * u := by
        unfold Qf; field_simp
      have hL : (1 + B) ^ q * (|u| ^ q + |v| ^ q) * (1 + q * a / (1 + B) * Qf q u v) =
          (1 + B) ^ q * (|u| ^ q + |v| ^ q) + q * a * (1 + B) ^ (q - 1) * ((|u| ^ q + |v| ^ q) * Qf q u v) := by
        rw [hq1]
        field_simp
      rw [hL, hQ]
      ring
  rw [hfirst, show (1 + B) * v - a * u = (1 + B) * v + -(a * u) from sub_eq_add_neg _ _]
  have e : |(1 + B) * u + a * v| ^ q + |(1 + B) * v + -(a * u)| ^ q -
      (|(1 + B) * u| ^ q + |(1 + B) * v| ^ q +
        (q * phi q ((1 + B) * u) * (a * v) + q * phi q ((1 + B) * v) * (-(a * u)))) =
      (|(1 + B) * u + a * v| ^ q - |(1 + B) * u| ^ q - q * phi q ((1 + B) * u) * (a * v)) +
      (|(1 + B) * v + -(a * u)| ^ q - |(1 + B) * v| ^ q - q * phi q ((1 + B) * v) * (-(a * u))) := by
    ring
  rw [e]
  have hK : 0 ≤ q * (q - 1) := by nlinarith
  calc _ ≤ |(|(1 + B) * u + a * v| ^ q - |(1 + B) * u| ^ q - q * phi q ((1 + B) * u) * (a * v))| +
        |(|(1 + B) * v + -(a * u)| ^ q - |(1 + B) * v| ^ q - q * phi q ((1 + B) * v) * (-(a * u)))| := abs_add_le _ _
    _ ≤ q * (q - 1) * ((2 + B) ^ (q - 2) * a ^ 2 * m ^ q) + q * (q - 1) * ((2 + B) ^ (q - 2) * a ^ 2 * m ^ q) := by
        gcongr
        · calc _ ≤ _ := T1
            _ = q * (q - 1) * ((|(1 + B) * u| + |a * v|) ^ (q - 2) * (a * v) ^ 2) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left R1 hK
        · calc _ ≤ _ := T2
            _ = q * (q - 1) * ((|(1 + B) * v| + |-(a * u)|) ^ (q - 2) * (-(a * u)) ^ 2) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left R2 hK
    _ = 2 * q * (q - 1) * (2 + B) ^ (q - 2) * a ^ 2 * m ^ q := by ring
    _ ≤ 2 * q * (q - 1) * (2 + B) ^ (q - 2) * a ^ 2 * (|u| ^ q + |v| ^ q) := by
        have hK2 : 0 ≤ 2 * q * (q - 1) * (2 + B) ^ (q - 2) * a ^ 2 :=
          mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Real.rpow_nonneg (by linarith) _))
            (sq_nonneg a)
        exact mul_le_mul_of_nonneg_left hmq hK2

/-- `‖P_0(J)‖_p = ‖P_0(S)‖_p = 1 + B` for `P_0(z) = 1 - Bz²`, `B > 0`, `1 ≤ p ≤ ∞` (real spaces). -/
theorem p0_norms (p : ℝ≥0∞) [Fact (1 ≤ p)] (B : ℝ) (hB : 0 < B) :
    matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B)) = 1 + B ∧ shiftNorm p ℝ (Pa 0 B) = 1 + B := by
  have hJ : matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B)) = 1 + B := by
    rw [aeval_Jmat_Pa_proved, zero_smul, add_zero, matNorm_smul, abs_of_pos (by linarith)]
    have h1 : matNorm p (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      rw [matNorm]
      have : matOp p (1 : Matrix (Fin 2) (Fin 2) ℝ) = ContinuousLinearMap.id ℝ _ := by
        ext x i
        simp [matOp]
      rw [this, ContinuousLinearMap.norm_id]
    rw [h1, mul_one]
  refine ⟨hJ, le_antisymm ?_ (hJ ▸ Matsaev.lemma_2_2_proved p (Pa 0 B))⟩
  have hS1 : ‖shiftOp p ℝ‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hS : aeval (shiftOp p ℝ) (Pa 0 B) = 1 - B • shiftOp p ℝ ^ 2 := by
    simp [Pa, Algebra.algebraMap_eq_smul_one]
  rw [shiftNorm, hS]
  calc ‖1 - B • shiftOp p ℝ ^ 2‖ ≤ ‖(1 : lp (fun _ : ℕ => ℝ) p →L[ℝ] lp (fun _ : ℕ => ℝ) p)‖ +
        ‖B • shiftOp p ℝ ^ 2‖ := norm_sub_le _ _
    _ ≤ 1 + B * 1 := by
        gcongr
        · exact ContinuousLinearMap.norm_id_le
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hB]
          gcongr
          calc ‖shiftOp p ℝ ^ 2‖ ≤ ‖shiftOp p ℝ‖ ^ 2 := norm_pow_le' _ (by norm_num)
            _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hS1
    _ = 1 + B := by ring

end Matsaev.Qexp
