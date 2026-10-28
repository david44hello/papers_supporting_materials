-- Matsaev/SJ/PowLib.lean — estimates for φ and ψ = |·|^q AWAY FROM 0, and for (1 + h)^r near 1 (Steps F-I of Theorem 3.6).
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.Angle.Basic

/-!
Away from `0` the functions `φ(y) = sign(y)|y|^(q-1)` and `ψ(y) = |y|^q` are smooth, so their Taylor remainders are
controlled by their (bounded) higher derivatives. Each statement gives SOME constant `K` (it may depend on `q, m, M`).
The hypotheses keep every point used (`y`, `z`, the segment between them, and the shifts by `h`) at distance `≥ m/4`
from `0` and on ONE side of `0`, and inside `[-(M + m), M + m]`.
Available from `Matsaev.Angle.Basic` (namespace `Matsaev.Angle`): `phi_eq_mul`, `hasDerivAt_absRpow`
(`(|y|^q)' = q φ(y)`), `hasDerivAt_phi` (`2 < q`: `φ'(y) = (q-1)|y|^(q-2)`), `continuous_phi`.

Proof method: every bound is the mean value inequality (`mvt_abs`) on a segment that stays in `c ≤ |t| ≤ L`
with `c > 0`. There `|t|^s` is Lipschitz with constant `|s| (c^(s-1) + L^(s-1))` (`abs_rpow_lip`).
We use `c = m/4` and `L = |M| + m` (`seg_region`).
-/

namespace Matsaev.SJ

open Real Set
open Matsaev.Angle (hasDerivAt_phi hasDerivAt_absRpow)

/-! ## Helpers -/

/-- Mean value inequality on a segment, with absolute values. -/
lemma mvt_abs {f f' : ℝ → ℝ} {a b C : ℝ} (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (hC : ∀ t ∈ uIcc a b, |f' t| ≤ C) : |f b - f a| ≤ C * |b - a| := by
  have := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hf t ht).hasDerivWithinAt) (fun t ht => by rw [Real.norm_eq_abs]; exact hC t ht)
    left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using this

/-- For `0 < c ≤ x ≤ L`, `x ^ e ≤ c ^ e + L ^ e`, whatever the sign of `e`. -/
lemma rpow_le_add {c L x e : ℝ} (hc : 0 < c) (hcx : c ≤ x) (hxL : x ≤ L) :
    x ^ e ≤ c ^ e + L ^ e := by
  rcases le_total 0 e with he | he
  · have h1 := rpow_le_rpow (hc.le.trans hcx) hxL he
    have h2 := rpow_nonneg hc.le e
    linarith
  · have h1 := rpow_le_rpow_of_nonpos hc hcx he
    have h2 := rpow_nonneg (hc.le.trans (hcx.trans hxL)) e
    linarith

/-- A point of a segment that stays in `c ≤ |t|` (`c > 0`) is not `0`. -/
lemma ne_zero_of_seg {c L a b t : ℝ} (hc : 0 < c) (hseg : ∀ u ∈ uIcc a b, c ≤ |u| ∧ |u| ≤ L)
    (ht : t ∈ uIcc a b) : t ≠ 0 := by
  intro h0
  have := (hseg t ht).1
  rw [h0, abs_zero] at this
  linarith

/-- `|t|^s` is Lipschitz on a segment that stays in `c ≤ |t| ≤ L` (`c > 0`). -/
lemma abs_rpow_lip {s c L a b : ℝ} (hc : 0 < c) (hseg : ∀ t ∈ uIcc a b, c ≤ |t| ∧ |t| ≤ L) :
    |(|b| ^ s - |a| ^ s)| ≤ |s| * (c ^ (s - 1) + L ^ (s - 1)) * |b - a| := by
  apply mvt_abs (f := fun x => |x| ^ s) (f' := fun t => (SignType.sign t : ℝ) * s * |t| ^ (s - 1))
  · intro t ht
    have ht0 := ne_zero_of_seg hc hseg ht
    exact (hasDerivAt_abs ht0).rpow_const (Or.inl (abs_ne_zero.mpr ht0))
  · intro t ht
    have ht0 := ne_zero_of_seg hc hseg ht
    obtain ⟨h1, h2⟩ := hseg t ht
    have hsg : |(SignType.sign t : ℝ)| = 1 := by
      rcases lt_or_gt_of_ne ht0 with h | h
      · simp [sign_neg h]
      · simp [sign_pos h]
    rw [abs_mul, abs_mul, hsg, one_mul, abs_of_nonneg (rpow_nonneg (abs_nonneg t) _)]
    exact mul_le_mul_of_nonneg_left (rpow_le_add hc h1 h2) (abs_nonneg s)

/-- Taylor bound for `φ` on a segment `[y, y + h]` that stays in `c ≤ |t| ≤ L` (`c > 0`). -/
lemma phi_taylor_seg {q c L y h : ℝ} (hq : 2 < q) (hc : 0 < c)
    (hseg : ∀ t ∈ uIcc y (y + h), c ≤ |t| ∧ |t| ≤ L) :
    |phi q (y + h) - phi q y - (q - 1) * |y| ^ (q - 2) * h|
      ≤ (q - 1) * (q - 2) * (c ^ (q - 3) + L ^ (q - 3)) * h ^ 2 := by
  have hL : 0 ≤ L := (abs_nonneg y).trans (hseg y left_mem_uIcc).2
  have hK : 0 ≤ (q - 1) * (q - 2) * (c ^ (q - 3) + L ^ (q - 3)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (add_nonneg (rpow_nonneg hc.le _) (rpow_nonneg hL _))
  have hderiv : ∀ t ∈ uIcc y (y + h), HasDerivAt (fun t => phi q t - (q - 1) * |y| ^ (q - 2) * t)
      ((q - 1) * |t| ^ (q - 2) - (q - 1) * |y| ^ (q - 2)) t := fun t _ =>
    ((hasDerivAt_phi hq t).sub ((hasDerivAt_id' t).const_mul ((q - 1) * |y| ^ (q - 2)))).congr_deriv
      (by ring)
  have hbound : ∀ t ∈ uIcc y (y + h), |(q - 1) * |t| ^ (q - 2) - (q - 1) * |y| ^ (q - 2)|
      ≤ (q - 1) * (q - 2) * (c ^ (q - 3) + L ^ (q - 3)) * |h| := by
    intro t ht
    have hlip := abs_rpow_lip (s := q - 2) hc
      (fun u hu => hseg u (uIcc_subset_uIcc left_mem_uIcc ht hu))
    have hty : |t - y| ≤ |h| := by simpa using abs_sub_left_of_mem_uIcc ht
    rw [abs_of_pos (by linarith : (0 : ℝ) < q - 2), show q - 2 - 1 = q - 3 by ring] at hlip
    rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q - 1)]
    calc (q - 1) * |(|t| ^ (q - 2) - |y| ^ (q - 2))|
        ≤ (q - 1) * ((q - 2) * (c ^ (q - 3) + L ^ (q - 3)) * |t - y|) :=
          mul_le_mul_of_nonneg_left hlip (by linarith)
      _ = (q - 1) * (q - 2) * (c ^ (q - 3) + L ^ (q - 3)) * |t - y| := by ring
      _ ≤ (q - 1) * (q - 2) * (c ^ (q - 3) + L ^ (q - 3)) * |h| := mul_le_mul_of_nonneg_left hty hK
  have key := mvt_abs hderiv hbound
  rw [show phi q (y + h) - (q - 1) * |y| ^ (q - 2) * (y + h) - (phi q y - (q - 1) * |y| ^ (q - 2) * y)
      = phi q (y + h) - phi q y - (q - 1) * |y| ^ (q - 2) * h by ring, show y + h - y = h by ring] at key
  calc _ ≤ _ := key
    _ = _ := by rw [← sq_abs h]; ring

/-- The region of `phi_second_diff_bound` and `abs_rpow_third_bound`: for `t` between `y` and `z`, the
segment `[t, t + h]` stays in `m/4 ≤ |u| ≤ |M| + m`. -/
lemma seg_region {m M y z h t : ℝ} (hy : m ≤ |y|) (hyz : |y - z| ≤ m / 2) (hh : |h| ≤ m / 4)
    (hyM : |y| ≤ M) (ht : t ∈ uIcc y z) : ∀ u ∈ uIcc t (t + h), m / 4 ≤ |u| ∧ |u| ≤ |M| + m := by
  intro u hu
  have h1 : |t - y| ≤ |z - y| := abs_sub_left_of_mem_uIcc ht
  have h2 : |u - t| ≤ |h| := by simpa using abs_sub_left_of_mem_uIcc hu
  rw [abs_sub_comm z y] at h1
  have h3 := abs_sub_le u t y
  have h4 := abs_sub_abs_le_abs_sub y u
  have h5 := abs_sub_abs_le_abs_sub u y
  have h6 := le_abs_self M
  rw [abs_sub_comm y u] at h4
  constructor <;> linarith

/-- The common constant `(q-1)(q-2)((m/4)^(q-3) + (|M|+m)^(q-3))` is `≥ 0`. -/
lemma kconst_nonneg {q m M : ℝ} (hq : 2 < q) (hm : 0 < m) :
    0 ≤ (q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3)) :=
  mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-! ## The four targets -/

/-- Taylor bound for `φ` away from `0`: `φ(y + h) = φ(y) + (q-1)|y|^(q-2) h + O(h²)`. -/
theorem phi_taylor_bound {q : ℝ} (hq : 2 < q) {m M : ℝ} (hm : 0 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y h : ℝ, m ≤ |y| → |h| ≤ m / 2 → |y| ≤ M →
      |phi q (y + h) - phi q y - (q - 1) * |y| ^ (q - 2) * h| ≤ K * h ^ 2 := by
  refine ⟨(q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3)), kconst_nonneg hq hm, ?_⟩
  intro y h hy hh hyM
  apply phi_taylor_seg hq (by positivity)
  intro t ht
  have hty : |t - y| ≤ |h| := by simpa using abs_sub_left_of_mem_uIcc ht
  have h1 := abs_sub_abs_le_abs_sub y t
  have h2 := abs_sub_abs_le_abs_sub t y
  have h3 := le_abs_self M
  rw [abs_sub_comm y t] at h1
  constructor <;> linarith

/-- Second difference of `φ` away from `0`: `[φ(y + h) - φ(y)] - [φ(z + h) - φ(z)] = O(|h| |y - z|)`. -/
theorem phi_second_diff_bound {q : ℝ} (hq : 2 < q) {m M : ℝ} (hm : 0 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y z h : ℝ, m ≤ |y| → |y - z| ≤ m / 2 → |h| ≤ m / 4 → |y| ≤ M →
      |(phi q (y + h) - phi q y) - (phi q (z + h) - phi q z)| ≤ K * |h| * |y - z| := by
  refine ⟨(q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3)), kconst_nonneg hq hm, ?_⟩
  intro y z h hy hyz hh hyM
  have hderiv : ∀ t ∈ uIcc y z, HasDerivAt (fun t => phi q (t + h) - phi q t)
      ((q - 1) * |t + h| ^ (q - 2) - (q - 1) * |t| ^ (q - 2)) t := fun t _ =>
    (HasDerivAt.comp_add_const t h (hasDerivAt_phi hq (t + h))).sub (hasDerivAt_phi hq t)
  have hbound : ∀ t ∈ uIcc y z, |(q - 1) * |t + h| ^ (q - 2) - (q - 1) * |t| ^ (q - 2)|
      ≤ (q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3)) * |h| := by
    intro t ht
    have hlip := abs_rpow_lip (s := q - 2) (by positivity : (0 : ℝ) < m / 4) (seg_region hy hyz hh hyM ht)
    rw [abs_of_pos (by linarith : (0 : ℝ) < q - 2), show q - 2 - 1 = q - 3 by ring,
      show t + h - t = h by ring] at hlip
    rw [← mul_sub, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q - 1)]
    calc (q - 1) * |(|t + h| ^ (q - 2) - |t| ^ (q - 2))|
        ≤ (q - 1) * ((q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3)) * |h|) :=
          mul_le_mul_of_nonneg_left hlip (by linarith)
      _ = _ := by ring
  have key := mvt_abs hderiv hbound
  calc _ = |(phi q (z + h) - phi q z) - (phi q (y + h) - phi q y)| := abs_sub_comm _ _
    _ ≤ _ := key
    _ = _ := by rw [abs_sub_comm z y]

/-- Difference of two Taylor remainders of `ψ` away from `0`: with `R(y) = ψ(y + h) - ψ(y) - q φ(y) h`,
`R(y) - R(z) = O(h² |y - z|)`. -/
theorem abs_rpow_third_bound {q : ℝ} (hq : 2 < q) {m M : ℝ} (hm : 0 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y z h : ℝ, m ≤ |y| → |y - z| ≤ m / 2 → |h| ≤ m / 4 → |y| ≤ M →
      |(|y + h| ^ q - |y| ^ q - q * phi q y * h) - (|z + h| ^ q - |z| ^ q - q * phi q z * h)| ≤ K * h ^ 2 * |y - z| := by
  refine ⟨q * ((q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3))),
    mul_nonneg (by linarith) (kconst_nonneg hq hm), ?_⟩
  intro y z h hy hyz hh hyM
  have hq1 : 1 < q := by linarith
  have hderiv : ∀ t ∈ uIcc y z, HasDerivAt (fun t => |t + h| ^ q - |t| ^ q - q * phi q t * h)
      (q * phi q (t + h) - q * phi q t - q * ((q - 1) * |t| ^ (q - 2)) * h) t := fun t _ =>
    ((HasDerivAt.comp_add_const t h (hasDerivAt_absRpow hq1 (t + h))).sub (hasDerivAt_absRpow hq1 t)).sub
      (((hasDerivAt_phi hq t).const_mul q).mul_const h)
  have hbound : ∀ t ∈ uIcc y z, |q * phi q (t + h) - q * phi q t - q * ((q - 1) * |t| ^ (q - 2)) * h|
      ≤ q * ((q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3))) * h ^ 2 := by
    intro t ht
    have ht2 := phi_taylor_seg hq (by positivity : (0 : ℝ) < m / 4) (seg_region hy hyz hh hyM ht)
    calc |q * phi q (t + h) - q * phi q t - q * ((q - 1) * |t| ^ (q - 2)) * h|
        = q * |phi q (t + h) - phi q t - (q - 1) * |t| ^ (q - 2) * h| := by
          rw [← abs_of_pos (by linarith : (0 : ℝ) < q), ← abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q)]
          ring_nf
      _ ≤ q * ((q - 1) * (q - 2) * ((m / 4) ^ (q - 3) + (|M| + m) ^ (q - 3)) * h ^ 2) :=
          mul_le_mul_of_nonneg_left ht2 (by linarith)
      _ = _ := by ring
  have key := mvt_abs hderiv hbound
  calc _ = |(|z + h| ^ q - |z| ^ q - q * phi q z * h) - (|y + h| ^ q - |y| ^ q - q * phi q y * h)| :=
        abs_sub_comm _ _
    _ ≤ _ := key
    _ = _ := by rw [abs_sub_comm z y]

/-- Taylor bound for `t ↦ t ^ r` at `t = 1` (`r > 1`): `(1 + h)^r = 1 + r h + O(h²)` for `|h| ≤ 1/2`. -/
theorem rpow_taylor_one_bound {r : ℝ} (hr : 1 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, |h| ≤ 1 / 2 → |(1 + h) ^ r - 1 - r * h| ≤ K * h ^ 2 := by
  have hB : 0 ≤ (r - 1) * ((1 / 2 : ℝ) ^ (r - 2) + (3 / 2 : ℝ) ^ (r - 2)) :=
    mul_nonneg (by linarith) (by positivity)
  refine ⟨r * ((r - 1) * ((1 / 2 : ℝ) ^ (r - 2) + (3 / 2 : ℝ) ^ (r - 2))),
    mul_nonneg (by linarith) hB, ?_⟩
  intro h hh
  have hpos : ∀ t ∈ uIcc 1 (1 + h), 1 / 2 ≤ t ∧ t ≤ 3 / 2 := by
    intro t ht
    have h1 : |t - 1| ≤ |h| := by simpa using abs_sub_left_of_mem_uIcc ht
    have h2 := abs_le.mp (h1.trans hh)
    constructor <;> linarith
  have hseg : ∀ t ∈ uIcc 1 (1 + h), 1 / 2 ≤ |t| ∧ |t| ≤ 3 / 2 := by
    intro t ht
    obtain ⟨h1, h2⟩ := hpos t ht
    rw [abs_of_pos (by linarith)]
    exact ⟨h1, h2⟩
  have hderiv : ∀ t ∈ uIcc 1 (1 + h), HasDerivAt (fun t => t ^ r - r * t) (r * t ^ (r - 1) - r) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_zero_of_seg (by norm_num) hseg ht
    exact ((hasDerivAt_rpow_const (Or.inl ht0)).sub ((hasDerivAt_id' t).const_mul r)).congr_deriv (by ring)
  have hbound : ∀ t ∈ uIcc 1 (1 + h), |r * t ^ (r - 1) - r|
      ≤ r * ((r - 1) * ((1 / 2 : ℝ) ^ (r - 2) + (3 / 2 : ℝ) ^ (r - 2))) * |h| := by
    intro t ht
    have htpos : 0 < t := by linarith [(hpos t ht).1]
    have hlip := abs_rpow_lip (s := r - 1) (a := 1) (b := t) (by norm_num : (0 : ℝ) < 1 / 2)
      (fun u hu => hseg u (uIcc_subset_uIcc left_mem_uIcc ht hu))
    rw [abs_one, one_rpow, abs_of_pos htpos, abs_of_pos (by linarith : (0 : ℝ) < r - 1),
      show r - 1 - 1 = r - 2 by ring] at hlip
    have h1 : |t - 1| ≤ |h| := by simpa using abs_sub_left_of_mem_uIcc ht
    rw [show r * t ^ (r - 1) - r = r * (t ^ (r - 1) - 1) by ring, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < r), mul_assoc]
    refine mul_le_mul_of_nonneg_left (hlip.trans ?_) (by linarith)
    exact mul_le_mul_of_nonneg_left h1 hB
  have key := mvt_abs hderiv hbound
  rw [one_rpow, show (1 + h) ^ r - r * (1 + h) - (1 - r * 1) = (1 + h) ^ r - 1 - r * h by ring,
    show 1 + h - 1 = h by ring] at key
  calc _ ≤ _ := key
    _ = _ := by rw [← sq_abs h]; ring

end Matsaev.SJ
