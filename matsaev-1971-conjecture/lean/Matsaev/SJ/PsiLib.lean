-- Matsaev/SJ/PsiLib.lean — global estimates for ψ(x) = |x|^q and φ(x) = sign(x)|x|^(q-1) used by Steps F-I of Theorem 3.6.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Angle.Basic

/-!
All bounds hold for every real `x, y, h` (no smallness, no distance from `0`). `max |x| |y| ^ (q - 2)` is `Real.rpow`
of a nonnegative base; for `q = 2` it is `1` (also when the base is `0`).
Available from `Matsaev.Angle.Basic` (namespace `Matsaev.Angle`): `phi_eq_mul` (`φ(y) = |y|^(q-2) y`),
`hasDerivAt_absRpow` (`1 < q`: `(|y|^q)' = q φ(y)`), `hasDerivAt_phi` (`2 < q`: `φ'(y) = (q-1)|y|^(q-2)`), `continuous_phi`.

Method: every bound is the mean value inequality on the segment `uIcc a b` (`abs_sub_le_of_deriv_le`), with the
derivative bounded through `|t| ≤ M` for all `t` on a segment whose endpoints lie in `[-M, M]`.
-/

namespace Matsaev.SJ

open Real

/-! ## Helpers -/

/-- A shifted point `t + c` of the segment between `a` and `b` stays in `[-M, M]` if `a + c` and `b + c` do. -/
lemma abs_add_le_of_mem_uIcc {a b t M : ℝ} (c : ℝ) (ht : t ∈ Set.uIcc a b) (ha : |a + c| ≤ M)
    (hb : |b + c| ≤ M) : |t + c| ≤ M := by
  rw [Set.mem_uIcc] at ht
  rw [abs_le] at ha hb ⊢
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Every point of the segment between `a` and `b` lies in `[-M, M]` if `a` and `b` do. -/
lemma abs_le_of_mem_uIcc {a b t M : ℝ} (ht : t ∈ Set.uIcc a b) (ha : |a| ≤ M) (hb : |b| ≤ M) : |t| ≤ M := by
  simpa using abs_add_le_of_mem_uIcc 0 ht (by simpa using ha) (by simpa using hb)

lemma abs_le_max_of_mem_uIcc {a b t : ℝ} (ht : t ∈ Set.uIcc a b) : |t| ≤ max |a| |b| :=
  abs_le_of_mem_uIcc ht (le_max_left _ _) (le_max_right _ _)

/-- Mean value inequality on the segment between `a` and `b`. -/
lemma abs_sub_le_of_deriv_le {f f' : ℝ → ℝ} {C a b : ℝ}
    (hf : ∀ t ∈ Set.uIcc a b, HasDerivAt f (f' t) t) (hC : ∀ t ∈ Set.uIcc a b, |f' t| ≤ C) :
    |f a - f b| ≤ C * |a - b| := by
  have key := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hf t ht).hasDerivWithinAt) (fun t ht => by rw [Real.norm_eq_abs]; exact hC t ht)
    Set.right_mem_uIcc Set.left_mem_uIcc
  simpa only [Real.norm_eq_abs] using key

/-- `q |φ(u) - φ(v)| ≤ q (q-1) M^(q-2) |u - v|` when `|u|, |v| ≤ M` (from `phi_sub_le`, proved below). -/
lemma mul_phi_sub_le {q M u v : ℝ} (hq : 2 ≤ q) (hphi : |phi q u - phi q v| ≤ (q - 1) * (max |u| |v|) ^ (q - 2) * |u - v|)
    (hu : |u| ≤ M) (hv : |v| ≤ M) {L : ℝ} (hL : |u - v| ≤ L) :
    |q * phi q u - q * phi q v| ≤ q * (q - 1) * M ^ (q - 2) * L := by
  have hpow : (max |u| |v|) ^ (q - 2) ≤ M ^ (q - 2) :=
    rpow_le_rpow (le_max_of_le_left (abs_nonneg u)) (max_le hu hv) (by linarith)
  have hM : 0 ≤ (q - 1) * M ^ (q - 2) := mul_nonneg (by linarith) (rpow_nonneg ((abs_nonneg u).trans hu) _)
  have hb : |phi q u - phi q v| ≤ (q - 1) * M ^ (q - 2) * L :=
    hphi.trans (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by linarith)) hL (abs_nonneg _) hM)
  calc |q * phi q u - q * phi q v| = q * |phi q u - phi q v| := by
        rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q)]
    _ ≤ q * ((q - 1) * M ^ (q - 2) * L) := mul_le_mul_of_nonneg_left hb (by linarith)
    _ = q * (q - 1) * M ^ (q - 2) * L := by ring

/-! ## The five bounds -/

/-- `|φ(x)| = |x|^(q-1)`. -/
theorem abs_phi_eq {q : ℝ} (hq : 1 < q) (x : ℝ) : |phi q x| = |x| ^ (q - 1) := by
  rw [Angle.phi_eq_mul, abs_mul, abs_of_nonneg (rpow_nonneg (abs_nonneg x) _),
    ← rpow_add_one' (abs_nonneg x) (by linarith : q - 2 + 1 ≠ 0)]
  congr 1
  ring

/-- First-order bound for `ψ = |·|^q`. -/
theorem abs_rpow_sub_le {q : ℝ} (hq : 1 ≤ q) (x y : ℝ) :
    |(|x| ^ q - |y| ^ q)| ≤ q * (max |x| |y|) ^ (q - 1) * |x - y| := by
  rcases hq.eq_or_lt with rfl | hq1
  · simpa using abs_abs_sub_abs_le_abs_sub x y
  · refine abs_sub_le_of_deriv_le (f := fun t => |t| ^ q) (fun t _ => Angle.hasDerivAt_absRpow hq1 t) ?_
    intro t ht
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q), abs_phi_eq hq1]
    exact mul_le_mul_of_nonneg_left
      (rpow_le_rpow (abs_nonneg t) (abs_le_max_of_mem_uIcc ht) (by linarith)) (by linarith)

/-- First-order bound for `φ`. -/
theorem phi_sub_le {q : ℝ} (hq : 2 ≤ q) (x y : ℝ) :
    |phi q x - phi q y| ≤ (q - 1) * (max |x| |y|) ^ (q - 2) * |x - y| := by
  rcases hq.eq_or_lt with rfl | hq2
  · have h2 : ∀ t, phi 2 t = t := fun t => by rw [Angle.phi_eq_mul]; norm_num
    norm_num [h2]
  · refine abs_sub_le_of_deriv_le (fun t _ => Angle.hasDerivAt_phi hq2 t) ?_
    intro t ht
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q - 1), abs_of_nonneg (rpow_nonneg (abs_nonneg t) _)]
    exact mul_le_mul_of_nonneg_left
      (rpow_le_rpow (abs_nonneg t) (abs_le_max_of_mem_uIcc ht) (by linarith)) (by linarith)

/-- Second-order (Taylor) bound for `ψ`: `ψ(x + h) = ψ(x) + q φ(x) h + O(h²)`. -/
theorem abs_rpow_taylor_le {q : ℝ} (hq : 2 ≤ q) (x h : ℝ) :
    |(|x + h| ^ q - |x| ^ q - q * phi q x * h)| ≤ q * (q - 1) * (max |x| |x + h|) ^ (q - 2) * h ^ 2 := by
  have hq1 : 1 < q := by linarith
  set M := max |x| |x + h| with hM
  -- `g(t) = |x + t|^q - q φ(x) t` on the segment between `h` and `0`.
  have hderiv : ∀ t ∈ Set.uIcc h 0, HasDerivAt (fun t => |x + t| ^ q - q * phi q x * t)
      (q * phi q (x + t) - q * phi q x) t := fun t _ =>
    (((Angle.hasDerivAt_absRpow hq1 (x + t)).comp_const_add x t).sub
      ((hasDerivAt_id' t).const_mul (q * phi q x))).congr_deriv (by ring)
  have hbound : ∀ t ∈ Set.uIcc h 0, |q * phi q (x + t) - q * phi q x| ≤ q * (q - 1) * M ^ (q - 2) * |h| := by
    intro t ht
    have hxt : |x + t| ≤ M := by
      rw [add_comm]
      exact abs_add_le_of_mem_uIcc x ht (by rw [add_comm]; exact le_max_right _ _)
        (by rw [zero_add]; exact le_max_left _ _)
    have hth : |x + t - x| ≤ |h| := by
      rw [add_sub_cancel_left]
      exact abs_le_of_mem_uIcc ht le_rfl (by rw [abs_zero]; exact abs_nonneg h)
    exact mul_phi_sub_le hq (phi_sub_le hq _ _) hxt (le_max_left _ _) hth
  calc |(|x + h| ^ q - |x| ^ q - q * phi q x * h)|
      = |(fun t => |x + t| ^ q - q * phi q x * t) h - (fun t => |x + t| ^ q - q * phi q x * t) 0| := by
        congr 1
        simp only [add_zero, mul_zero, sub_zero]
        ring
    _ ≤ q * (q - 1) * M ^ (q - 2) * |h| * |h - 0| := abs_sub_le_of_deriv_le hderiv hbound
    _ = q * (q - 1) * M ^ (q - 2) * h ^ 2 := by rw [sub_zero, mul_assoc, abs_mul_abs_self, sq]

/-- Second difference of `ψ`: `[ψ(y + h) - ψ(y)] - [ψ(z + h) - ψ(z)] = O(|h| |y - z|)`. -/
theorem abs_rpow_second_diff_le {q : ℝ} (hq : 2 ≤ q) {M : ℝ} (y z h : ℝ) (hy : |y| ≤ M) (hz : |z| ≤ M)
    (hyh : |y + h| ≤ M) (hzh : |z + h| ≤ M) :
    |(|y + h| ^ q - |y| ^ q) - (|z + h| ^ q - |z| ^ q)| ≤ q * (q - 1) * M ^ (q - 2) * |h| * |y - z| := by
  have hq1 : 1 < q := by linarith
  -- `g(t) = |t + h|^q - |t|^q` on the segment between `y` and `z`.
  have hderiv : ∀ t ∈ Set.uIcc y z, HasDerivAt (fun t => |t + h| ^ q - |t| ^ q)
      (q * phi q (t + h) - q * phi q t) t := fun t _ =>
    ((Angle.hasDerivAt_absRpow hq1 (t + h)).comp_add_const t h).sub (Angle.hasDerivAt_absRpow hq1 t)
  have hbound : ∀ t ∈ Set.uIcc y z, |q * phi q (t + h) - q * phi q t| ≤ q * (q - 1) * M ^ (q - 2) * |h| := by
    intro t ht
    exact mul_phi_sub_le hq (phi_sub_le hq _ _) (abs_add_le_of_mem_uIcc h ht hyh hzh)
      (abs_le_of_mem_uIcc ht hy hz) (by rw [add_sub_cancel_left])
  exact abs_sub_le_of_deriv_le hderiv hbound

end Matsaev.SJ
