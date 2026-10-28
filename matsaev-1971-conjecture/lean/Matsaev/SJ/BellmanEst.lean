-- Matsaev/SJ/BellmanEst.lean — Theorem 3.6 (`thm:SJ`), Step 6, Case 2: Δ to second order in ν, away from the axis u = 0.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.SJ.BellmanDefs
import Matsaev.SJ.PsiLib
import Matsaev.SJ.PowLib

/-!
`Δ(u, v, ν) - q ν n(u, v) = E₄ + E₁ + λ₁ E₂ + λ₂ E₃` (`A = 1 + B`, `ψ = |·|^q`):
* `E₄ = [ψ(Au + av) - ψ(Au + av - Bν)] - [ψ(Au) - ψ(Au - Bν)] - qBν(φ(Au + av) - φ(Au))`: a difference of two Taylor
  remainders of `ψ` at points `a v` apart, away from `0` (`abs_rpow_third_bound`): `O(a ν²)`;
* `E₁ = [ψ(x) - ψ(x + aν)]/2 + (a/2) q ν φ(x)`, `x = Av - au`: the Taylor remainder of `ψ` at step `aν` (`abs_rpow_taylor_le`): `O(a² ν²)`;
* `E₂ = k₁(v, -u + ν) - 1 + q u ν = [(1 + h)^(q/2) - 1 - (q/2) h] + (q/2) ν²`, `h = -2uν + ν²` (`rpow_taylor_one_bound`): `O(ν²)`;
* `E₃ = ψ(-u + ν) - ψ(u) + q φ(u) ν`: the Taylor remainder of `ψ` at `-u` (`abs_rpow_taylor_le`): `O(ν²)`.
-/

namespace Matsaev.SJ

open Real

/-- `φ` is odd. -/
private lemma phi_neg_est (q x : ℝ) : phi q (-x) = -phi q x := by
  unfold phi
  rw [Left.sign_neg, abs_neg, SignType.coe_neg]
  ring

/-- `E₄ = O(a ν²)`: two Taylor remainders of `ψ` at the points `Au` and `Au + av`, step `-Bν`, away from `0`. -/
lemma est_T4 {q B κ : ℝ} (hq : 2 < q) (hB : 0 < B) (hκ : 0 < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a u v ν : ℝ, 0 ≤ a → a ≤ (1 + B) * κ / 2 → κ ≤ |u| → |u| ≤ 1 → |v| ≤ 1 →
      |ν| ≤ (1 + B) * κ / (4 * B) →
      |((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
        - q * B * ν * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u))| ≤ K * a * ν ^ 2 := by
  have hA : 0 < 1 + B := by linarith
  obtain ⟨K, hK, hR⟩ := abs_rpow_third_bound hq (m := (1 + B) * κ) (M := 1 + B) (by positivity)
  refine ⟨K * B ^ 2, by positivity, fun a u v ν ha ha' hu hu1 hv hν => ?_⟩
  have hy : (1 + B) * κ ≤ |(1 + B) * u| := by
    rw [abs_mul, abs_of_pos hA]; exact mul_le_mul_of_nonneg_left hu hA.le
  have hyz : |(1 + B) * u - ((1 + B) * u + a * v)| = a * |v| := by
    rw [show (1 + B) * u - ((1 + B) * u + a * v) = -(a * v) by ring, abs_neg, abs_mul, abs_of_nonneg ha]
  have hyz' : |(1 + B) * u - ((1 + B) * u + a * v)| ≤ (1 + B) * κ / 2 := by
    rw [hyz]; nlinarith [abs_nonneg v]
  have hh : |-(B * ν)| ≤ (1 + B) * κ / 4 := by
    rw [abs_neg, abs_mul, abs_of_pos hB]
    have := mul_le_mul_of_nonneg_left hν hB.le
    rwa [show B * ((1 + B) * κ / (4 * B)) = (1 + B) * κ / 4 by field_simp] at this
  have hyM : |(1 + B) * u| ≤ 1 + B := by
    rw [abs_mul, abs_of_pos hA]; nlinarith
  have h := hR ((1 + B) * u) ((1 + B) * u + a * v) (-(B * ν)) hy hyz' hh hyM
  simp only [← sub_eq_add_neg] at h
  rw [hyz] at h
  have e : ((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
        - q * B * ν * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)) =
      (|(1 + B) * u - B * ν| ^ q - |(1 + B) * u| ^ q - q * phi q ((1 + B) * u) * -(B * ν)) -
        (|(1 + B) * u + a * v - B * ν| ^ q - |(1 + B) * u + a * v| ^ q - q * phi q ((1 + B) * u + a * v) * -(B * ν)) := by
    ring
  rw [e]
  calc _ ≤ K * (-(B * ν)) ^ 2 * (a * |v|) := h
    _ = K * B ^ 2 * ν ^ 2 * (a * |v|) := by ring
    _ ≤ K * B ^ 2 * ν ^ 2 * a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [abs_nonneg v]
    _ = K * B ^ 2 * a * ν ^ 2 := by ring

/-- `E₁ = O(a² ν²) ≤ O(a ν²)`: the Taylor remainder of `ψ` at `x = Av - au` with step `aν`. -/
lemma est_T1 {q B : ℝ} (hq : 2 < q) (hB : 0 < B) (a u v ν : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hν : |ν| ≤ 1) :
    |(|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2 + a / 2 * q * ν * phi q ((1 + B) * v - a * u)|
      ≤ q * (q - 1) * (1 + B + 2) ^ (q - 2) / 2 * a * ν ^ 2 := by
  set x := (1 + B) * v - a * u with hx
  have hT := abs_rpow_taylor_le hq.le x (a * ν)
  have hx1 : |x| ≤ 1 + B + 2 := by
    have h1 : |(1 + B) * v| ≤ 1 + B := by rw [abs_mul, abs_of_pos (by linarith)]; nlinarith
    have h2 : |a * u| ≤ 1 := by rw [abs_mul, abs_of_nonneg ha]; nlinarith [abs_nonneg u]
    calc |x| ≤ |(1 + B) * v| + |a * u| := abs_sub _ _
      _ ≤ 1 + B + 2 := by linarith
  have hx2 : |x + a * ν| ≤ 1 + B + 2 := by
    have h1 : |(1 + B) * v| ≤ 1 + B := by rw [abs_mul, abs_of_pos (by linarith)]; nlinarith
    have h2 : |a * u| ≤ 1 := by rw [abs_mul, abs_of_nonneg ha]; nlinarith [abs_nonneg u]
    have h3 : |a * ν| ≤ 1 := by rw [abs_mul, abs_of_nonneg ha]; nlinarith [abs_nonneg ν]
    calc |x + a * ν| ≤ |x| + |a * ν| := abs_add_le _ _
      _ ≤ |(1 + B) * v| + |a * u| + |a * ν| := by linarith [abs_sub ((1 + B) * v) (a * u)]
      _ ≤ 1 + B + 2 := by linarith
  have hM : (max |x| |x + a * ν|) ^ (q - 2) ≤ (1 + B + 2) ^ (q - 2) :=
    Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg x)) (max_le hx1 hx2) (by linarith)
  have e : (|x| ^ q - |x + a * ν| ^ q) / 2 + a / 2 * q * ν * phi q x =
      -((|x + a * ν| ^ q - |x| ^ q - q * phi q x * (a * ν)) / 2) := by ring
  rw [e, abs_neg, abs_div, abs_two]
  have hq1 : 0 ≤ q * (q - 1) := by nlinarith
  calc _ ≤ q * (q - 1) * (max |x| |x + a * ν|) ^ (q - 2) * (a * ν) ^ 2 / 2 := by linarith
    _ ≤ q * (q - 1) * (1 + B + 2) ^ (q - 2) * (a * ν) ^ 2 / 2 := by gcongr
    _ = q * (q - 1) * (1 + B + 2) ^ (q - 2) / 2 * (a * a) * ν ^ 2 := by ring
    _ ≤ q * (q - 1) * (1 + B + 2) ^ (q - 2) / 2 * a * ν ^ 2 := by
        have h0 : 0 ≤ q * (q - 1) * (1 + B + 2) ^ (q - 2) / 2 := by positivity
        have haa : a * a ≤ a := by nlinarith
        have := mul_le_mul_of_nonneg_left haa h0
        nlinarith [sq_nonneg ν]

/-- `E₂ = O(ν²)`: `k₁(v, -u + ν) = (1 + h)^(q/2)` with `h = -2uν + ν²` on the unit circle. -/
lemma est_T2 {q : ℝ} (hq : 2 < q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u v ν : ℝ, u ^ 2 + v ^ 2 = 1 → |ν| ≤ 1 / 5 → |k1 q v (-u + ν) - 1 + q * u * ν| ≤ K * ν ^ 2 := by
  obtain ⟨K, hK, hT⟩ := rpow_taylor_one_bound (r := q / 2) (by linarith)
  refine ⟨5 * K + q / 2, by positivity, fun u v ν huv hν => ?_⟩
  have hu : |u| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg v]
  set h := -2 * u * ν + ν ^ 2 with hh
  have hk : k1 q v (-u + ν) = (1 + h) ^ (q / 2) := by
    unfold k1; congr 1; rw [hh]; linear_combination huv
  have habs : |h| ≤ (2 + |ν|) * |ν| := by
    calc |h| ≤ |-2 * u * ν| + |ν ^ 2| := abs_add_le _ _
      _ = 2 * |u| * |ν| + |ν| * |ν| := by rw [abs_mul, abs_mul, abs_neg, abs_two, abs_pow, sq]
      _ ≤ 2 * 1 * |ν| + |ν| * |ν| := by gcongr
      _ = (2 + |ν|) * |ν| := by ring
  have hν0 := abs_nonneg ν
  have hh2 : |h| ≤ 1 / 2 := by nlinarith
  have hsq : h ^ 2 ≤ 5 * ν ^ 2 := by
    have h1 : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
    have h2 : ν ^ 2 = |ν| ^ 2 := (sq_abs ν).symm
    rw [h1, h2]
    have h3 : |h| ^ 2 ≤ ((2 + |ν|) * |ν|) ^ 2 := by gcongr
    have h4 : (2 + |ν|) ^ 2 ≤ 5 := by nlinarith
    calc |h| ^ 2 ≤ ((2 + |ν|) * |ν|) ^ 2 := h3
      _ = (2 + |ν|) ^ 2 * |ν| ^ 2 := by ring
      _ ≤ 5 * |ν| ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
  have e : k1 q v (-u + ν) - 1 + q * u * ν = ((1 + h) ^ (q / 2) - 1 - q / 2 * h) + q / 2 * ν ^ 2 := by
    rw [hk, hh]; ring
  rw [e]
  have hT' := hT h hh2
  calc _ ≤ |(1 + h) ^ (q / 2) - 1 - q / 2 * h| + |q / 2 * ν ^ 2| := abs_add_le _ _
    _ ≤ K * h ^ 2 + q / 2 * ν ^ 2 := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ q / 2 * ν ^ 2)]; linarith
    _ ≤ K * (5 * ν ^ 2) + q / 2 * ν ^ 2 := by gcongr
    _ = (5 * K + q / 2) * ν ^ 2 := by ring

/-- `E₃ = O(ν²)`: the Taylor remainder of `ψ` at `-u` with step `ν`. -/
lemma est_T3 {q : ℝ} (hq : 2 < q) (u ν : ℝ) (hu : |u| ≤ 1) (hν : |ν| ≤ 1) :
    |(|-u + ν| ^ q - |u| ^ q + q * phi q u * ν)| ≤ q * (q - 1) * 2 ^ (q - 2) * ν ^ 2 := by
  have hT := abs_rpow_taylor_le hq.le (-u) ν
  rw [abs_neg, phi_neg_est] at hT
  have hM : (max |u| |-u + ν|) ^ (q - 2) ≤ 2 ^ (q - 2) := by
    refine Real.rpow_le_rpow (le_max_of_le_left (abs_nonneg u)) (max_le (by linarith) ?_) (by linarith)
    calc |-u + ν| ≤ |-u| + |ν| := abs_add_le _ _
      _ ≤ 2 := by rw [abs_neg]; linarith
  have e : |-u + ν| ^ q - |u| ^ q + q * phi q u * ν = |-u + ν| ^ q - |u| ^ q - q * -phi q u * ν := by ring
  rw [e]
  have hq1 : 0 ≤ q * (q - 1) := by nlinarith
  calc _ ≤ q * (q - 1) * (max |u| |-u + ν|) ^ (q - 2) * ν ^ 2 := hT
    _ ≤ q * (q - 1) * 2 ^ (q - 2) * ν ^ 2 := by gcongr

/-- H1/H2 (Taylor in `ν`, Theorem 3.6, Step 6, Case 2): away from the axis `u = 0`, `Δ(u, v, ν) = q ν n(u, v) + O(a ν²)`. -/
theorem delta_second_order (q B Λ κ : ℝ) (hq : 2 < q) (hB : 0 < B) (hΛ : 0 ≤ Λ) (hκ : 0 < κ) :
    ∃ ν₃ a₃ K : ℝ, 0 < ν₃ ∧ 0 < a₃ ∧ 0 ≤ K ∧ ∀ a l1 l2 u v ν : ℝ, 0 < a → a ≤ a₃ → |l1| ≤ Λ * a → |l2| ≤ Λ * a →
      u ^ 2 + v ^ 2 = 1 → κ ≤ |u| → |ν| ≤ ν₃ →
      |DeltaUV q a B l1 l2 u v ν - q * ν * nUV q a B l1 l2 u v| ≤ K * a * ν ^ 2 := by
  have hA : 0 < 1 + B := by linarith
  obtain ⟨K4, hK4, h4⟩ := est_T4 hq hB hκ
  obtain ⟨K2, hK2, h2⟩ := est_T2 hq
  set c1 := q * (q - 1) * (1 + B + 2) ^ (q - 2) / 2 with hc1
  set c3 := q * (q - 1) * 2 ^ (q - 2) with hc3
  have hqq : 0 ≤ q * (q - 1) := by nlinarith
  have hc1n : 0 ≤ c1 := by positivity
  have hc3n : 0 ≤ c3 := by positivity
  refine ⟨min (1 / 5) ((1 + B) * κ / (4 * B)), min 1 ((1 + B) * κ / 2), K4 + c1 + Λ * K2 + Λ * c3,
    lt_min (by norm_num) (by positivity), lt_min one_pos (by positivity), by positivity, ?_⟩
  intro a l1 l2 u v ν ha ha3 hl1 hl2 huv hu hν
  have ha1 : a ≤ 1 := ha3.trans (min_le_left _ _)
  have ha2 : a ≤ (1 + B) * κ / 2 := ha3.trans (min_le_right _ _)
  have hν5 : |ν| ≤ 1 / 5 := hν.trans (min_le_left _ _)
  have hνB : |ν| ≤ (1 + B) * κ / (4 * B) := hν.trans (min_le_right _ _)
  have hν1 : |ν| ≤ 1 := by linarith
  have hu1 : |u| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg v]
  have hv1 : |v| ≤ 1 := by rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg u]
  have e4 := h4 a u v ν ha.le ha2 hu hu1 hv1 hνB
  have e1 : |(|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2 +
      a / 2 * q * ν * phi q ((1 + B) * v - a * u)| ≤ c1 * a * ν ^ 2 := est_T1 hq hB a u v ν ha.le ha1 hu1 hv1 hν1
  have e2 := h2 u v ν huv hν5
  have e3 := est_T3 hq u ν hu1 hν1
  have hsplit : DeltaUV q a B l1 l2 u v ν - q * ν * nUV q a B l1 l2 u v =
      (((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
        - q * B * ν * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)))
      + ((|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2 + a / 2 * q * ν * phi q ((1 + B) * v - a * u))
      + l1 * (k1 q v (-u + ν) - 1 + q * u * ν) + l2 * (|-u + ν| ^ q - |u| ^ q + q * phi q u * ν) := by
    unfold DeltaUV nUV R1; ring
  rw [hsplit]
  have hν2 : 0 ≤ ν ^ 2 := sq_nonneg ν
  have b2 : |l1 * (k1 q v (-u + ν) - 1 + q * u * ν)| ≤ Λ * a * (K2 * ν ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hl1 e2 (abs_nonneg _) (by positivity)
  have b3 : |l2 * (|-u + ν| ^ q - |u| ^ q + q * phi q u * ν)| ≤ Λ * a * (c3 * ν ^ 2) := by
    rw [abs_mul]; exact mul_le_mul hl2 e3 (abs_nonneg _) (by positivity)
  have t1 := abs_add_le
    ((((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
        - q * B * ν * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)))
      + ((|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2 + a / 2 * q * ν * phi q ((1 + B) * v - a * u))
      + l1 * (k1 q v (-u + ν) - 1 + q * u * ν)) (l2 * (|-u + ν| ^ q - |u| ^ q + q * phi q u * ν))
  have t2 := abs_add_le
    ((((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
        - q * B * ν * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)))
      + ((|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2 + a / 2 * q * ν * phi q ((1 + B) * v - a * u)))
    (l1 * (k1 q v (-u + ν) - 1 + q * u * ν))
  have t3 := abs_add_le
    (((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
        - q * B * ν * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)))
    ((|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2 + a / 2 * q * ν * phi q ((1 + B) * v - a * u))
  have e : (K4 + c1 + Λ * K2 + Λ * c3) * a * ν ^ 2 =
      K4 * a * ν ^ 2 + c1 * a * ν ^ 2 + Λ * a * (K2 * ν ^ 2) + Λ * a * (c3 * ν ^ 2) := by ring
  rw [e]
  linarith

end Matsaev.SJ
