-- Matsaev/SJ/BellmanLam.lean — Steps 4-5 of Theorem 3.6: |λ| ≤ Λa (the λ-system is O(a)), and the C¹ bound on Δ for every ν.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.SJ.BellmanDefs
import Matsaev.SJ.PsiLib
import Matsaev.SJ.PowLib

/-!
Tools: `Matsaev/SJ/PsiLib.lean` (`abs_phi_eq`, `abs_rpow_sub_le`, `phi_sub_le`, `abs_rpow_second_diff_le`: global bounds for
`ψ = |·|^q` and φ, valid for all reals).
-/

namespace Matsaev.SJ

open Real

/-! ## Helpers -/

/-- `|x - y| ≤ |x| + |y|`. -/
private lemma abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [sub_eq_add_neg, ← abs_neg y]
  exact abs_add_le x (-y)

/-- The arguments `A x ± a y` and `A x` lie in `[-(A + 1), A + 1]` for `|x|, |y| ≤ 1`, `0 ≤ a ≤ 1`. -/
private lemma abs_lin_le_one {A a x y : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |A * x + a * y| ≤ A + 1 ∧ |A * x - a * y| ≤ A + 1 ∧ |A * x| ≤ A + 1 := by
  have e1 := mul_le_of_le_one_right hA hx
  have e2 := mul_le_of_le_one_right ha hy
  refine ⟨(abs_add_le _ _).trans ?_, (abs_sub_le_add _ _).trans ?_, ?_⟩ <;>
    simp only [abs_mul, abs_of_nonneg hA, abs_of_nonneg ha] <;> linarith

/-- `|φ(x)| ≤ M^(q-1)` for `|x| ≤ M`. -/
private lemma abs_phi_le {q M x : ℝ} (hq : 1 < q) (hx : |x| ≤ M) : |phi q x| ≤ M ^ (q - 1) := by
  rw [abs_phi_eq hq]
  exact rpow_le_rpow (abs_nonneg x) hx (by linarith)

/-- `φ` is `(q-1) M^(q-2)`-Lipschitz on `[-M, M]`. -/
private lemma phi_sub_le_of_le {q M x y : ℝ} (hq : 2 ≤ q) (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |phi q x - phi q y| ≤ (q - 1) * M ^ (q - 2) * |x - y| := by
  have hpow : (max |x| |y|) ^ (q - 2) ≤ M ^ (q - 2) :=
    rpow_le_rpow (le_max_of_le_left (abs_nonneg x)) (max_le hx hy) (by linarith)
  exact (phi_sub_le hq x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith)) (abs_nonneg _))

/-- `X^s ≤ C^s W^t` from `0 ≤ X ≤ C W`, `W ≥ 1`, `0 ≤ s ≤ t`. -/
private lemma rpow_le_mul_rpow {X C W s t : ℝ} (hX : 0 ≤ X) (hC : 0 ≤ C) (hW : 1 ≤ W) (hXW : X ≤ C * W)
    (hs : 0 ≤ s) (hst : s ≤ t) : X ^ s ≤ C ^ s * W ^ t :=
  calc X ^ s ≤ (C * W) ^ s := rpow_le_rpow hX hXW hs
    _ = C ^ s * W ^ s := mul_rpow hC (by linarith)
    _ ≤ C ^ s * W ^ t := mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hW hst) (rpow_nonneg hC _)

/-- `|w + x/2 + y + z| ≤ |w| + |x|/2 + |y| + |z|` (the shape of `Δ`). -/
private lemma abs_add4_le (w x y z : ℝ) : |w + x / 2 + y + z| ≤ |w| + |x| / 2 + |y| + |z| := by
  have h1 := abs_add_le (w + x / 2 + y) z
  have h2 := abs_add_le (w + x / 2) y
  have h3 := abs_add_le w (x / 2)
  have h4 : |x / 2| = |x| / 2 := by rw [abs_div, abs_two]
  linarith

/-- On the unit circle `|u| ≤ 1`. -/
private lemma abs_le_one_of_sq_add {u v : ℝ} (huv : u ^ 2 + v ^ 2 = 1) : |u| ≤ 1 := by
  have := sq_abs u
  nlinarith [abs_nonneg u, sq_nonneg v]

/-! ## R₁, R₂ and λ -/

/-- `|R₁|, |R₂| ≤ K a` with `K = B (q-1) (2+B)^(q-2) + (2+B)^(q-1)/2`. -/
private lemma R_bound_explicit {q B a u v : ℝ} (hq : 2 < q) (hB : 0 < B) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |R1 q a B u v| ≤ (B * (q - 1) * (2 + B) ^ (q - 2) + (2 + B) ^ (q - 1) / 2) * a ∧
      |R2 q a B u v| ≤ (B * (q - 1) * (2 + B) ^ (q - 2) + (2 + B) ^ (q - 1) / 2) * a := by
  have hA : (0 : ℝ) ≤ 1 + B := by linarith
  have hM : (1 + B) + 1 = 2 + B := by ring
  obtain ⟨hu1, -, hu3⟩ := abs_lin_le_one hA ha ha1 hu hv
  obtain ⟨-, hv2, hv3⟩ := abs_lin_le_one hA ha ha1 hv hu
  rw [hM] at hu1 hu3 hv2 hv3
  have hc : 0 ≤ (q - 1) * (2 + B) ^ (q - 2) := mul_nonneg (by linarith) (rpow_nonneg (by linarith) _)
  -- the two differences of φ: the arguments differ by `a v` and by `-a u`
  have hd1 : |phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)| ≤ (q - 1) * (2 + B) ^ (q - 2) * a := by
    refine (phi_sub_le_of_le hq.le hu1 hu3).trans (mul_le_mul_of_nonneg_left ?_ hc)
    rw [show (1 + B) * u + a * v - (1 + B) * u = a * v by ring, abs_mul, abs_of_nonneg ha]
    exact mul_le_of_le_one_right ha hv
  have hd2 : |phi q ((1 + B) * v - a * u) - phi q ((1 + B) * v)| ≤ (q - 1) * (2 + B) ^ (q - 2) * a := by
    refine (phi_sub_le_of_le hq.le hv2 hv3).trans (mul_le_mul_of_nonneg_left ?_ hc)
    rw [show (1 + B) * v - a * u - (1 + B) * v = -(a * u) by ring, abs_neg, abs_mul, abs_of_nonneg ha]
    exact mul_le_of_le_one_right ha hu
  have hp1 := abs_phi_le (by linarith : (1 : ℝ) < q) hu1
  have hp2 := abs_phi_le (by linarith : (1 : ℝ) < q) hv2
  have ha2 : |a / 2| = a / 2 := abs_of_nonneg (by linarith)
  have e1 := mul_le_mul_of_nonneg_left hd1 hB.le
  have e2 := mul_le_mul_of_nonneg_left hd2 hB.le
  have e3 := mul_le_mul_of_nonneg_left hp1 (by linarith : (0 : ℝ) ≤ a / 2)
  have e4 := mul_le_mul_of_nonneg_left hp2 (by linarith : (0 : ℝ) ≤ a / 2)
  constructor
  · unfold R1
    refine (abs_sub_le_add _ _).trans ?_
    simp only [abs_mul, abs_of_pos hB, ha2]
    linarith
  · unfold R2
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_of_pos hB, ha2]
    linarith

/-- The right-hand sides of the λ-system are `O(a)` (Theorem 3.6, Step 4): `|φ(x + h) - φ(x)| ≤ (q-1) M^(q-2) |h|` (`phi_sub_le`) and
`|φ(y)| = |y|^(q-1)` (`abs_phi_eq`), with all arguments in `[-(2 + B), 2 + B]`. -/
theorem R_bound (q B : ℝ) (hq : 2 < q) (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a u v : ℝ, 0 ≤ a → a ≤ 1 → |u| ≤ 1 → |v| ≤ 1 →
      |R1 q a B u v| ≤ K * a ∧ |R2 q a B u v| ≤ K * a := by
  refine ⟨B * (q - 1) * (2 + B) ^ (q - 2) + (2 + B) ^ (q - 1) / 2, ?_,
    fun a u v ha ha1 hu hv => R_bound_explicit hq hB ha ha1 hu hv⟩
  have h1 : 0 ≤ (2 + B) ^ (q - 2) := rpow_nonneg (by linarith) _
  have h2 : 0 ≤ (2 + B) ^ (q - 1) := rpow_nonneg (by linarith) _
  have h3 : 0 ≤ B * (q - 1) := mul_nonneg hB.le (by linarith)
  have := mul_nonneg h3 h1
  linarith

/-- Cramer's rule with a determinant `≥ d`: `|λ| ≤ (2K/d) a` (Theorem 3.6, Step 4, `Λ = 2K/d`); uses `|φ(x)| ≤ 1` for `|x| ≤ 1`. -/
theorem lam_bound {q a B u v K d : ℝ} (hq : 1 < q) (hd : 0 < d) (hdet : d ≤ |detL q u v|) (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (h1 : |R1 q a B u v| ≤ K * a) (h2 : |R2 q a B u v| ≤ K * a) :
    |lam1 q a B u v| ≤ 2 * K / d * a ∧ |lam2 q a B u v| ≤ 2 * K / d * a := by
  have hφu : |phi q u| ≤ 1 := by simpa only [one_rpow] using abs_phi_le hq hu
  have hφv : |phi q v| ≤ 1 := by simpa only [one_rpow] using abs_phi_le hq hv
  -- a numerator of size `≤ 2 K a` over the determinant
  have hdiv : ∀ {N : ℝ}, |N| ≤ 2 * (K * a) → |N / detL q u v| ≤ 2 * K / d * a := fun {N} hN => by
    rw [abs_div]
    calc |N| / |detL q u v| ≤ |N| / d := div_le_div_of_nonneg_left (abs_nonneg _) hd hdet
      _ ≤ 2 * (K * a) / d := div_le_div_of_nonneg_right hN hd.le
      _ = 2 * K / d * a := by ring
  have hn1 : |R1 q a B u v * phi q v - R2 q a B u v * phi q u| ≤ 2 * (K * a) := by
    refine (abs_sub_le_add _ _).trans ?_
    rw [abs_mul, abs_mul]
    have e1 := mul_le_of_le_one_right (abs_nonneg (R1 q a B u v)) hφv
    have e2 := mul_le_of_le_one_right (abs_nonneg (R2 q a B u v)) hφu
    linarith
  have hn2 : |u * R2 q a B u v - v * R1 q a B u v| ≤ 2 * (K * a) := by
    refine (abs_sub_le_add _ _).trans ?_
    rw [abs_mul, abs_mul]
    have e1 := mul_le_of_le_one_left (abs_nonneg (R2 q a B u v)) hu
    have e2 := mul_le_of_le_one_left (abs_nonneg (R1 q a B u v)) hv
    linarith
  exact ⟨hdiv hn1, hdiv hn2⟩

/-! ## The four terms of Δ -/

/-- The first bracket of `Δ` (a second difference of `ψ`, step `Bν`, arguments `a v` apart):
`≤ q(q-1) B (2+2B)^(q-2) · a (1+|ν|)^(q-1) |ν|`. -/
private lemma delta_term1 {q B a u v ν : ℝ} (hq : 2 < q) (hB : 0 < B) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |(|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q)|
      ≤ q * (q - 1) * B * (2 + 2 * B) ^ (q - 2) * (a * (1 + |ν|) ^ (q - 1) * |ν|) := by
  have hA : (0 : ℝ) ≤ 1 + B := by linarith
  have hBν : |B * ν| = B * |ν| := by rw [abs_mul, abs_of_pos hB]
  have hBν0 : 0 ≤ B * |ν| := mul_nonneg hB.le (abs_nonneg ν)
  obtain ⟨hl1, -, hl3⟩ := abs_lin_le_one hA ha ha1 hu hv
  -- all four arguments lie in `[-M, M]`, `M = 2 + B + B|ν|`
  have hy : |(1 + B) * u + a * v - B * ν| ≤ 2 + B + B * |ν| := by
    refine (abs_sub_le_add _ _).trans ?_
    rw [hBν]
    linarith
  have hz : |(1 + B) * u - B * ν| ≤ 2 + B + B * |ν| := by
    refine (abs_sub_le_add _ _).trans ?_
    rw [hBν]
    linarith
  have key := abs_rpow_second_diff_le hq.le (M := 2 + B + B * |ν|) ((1 + B) * u + a * v - B * ν)
    ((1 + B) * u - B * ν) (B * ν) hy hz (by rw [sub_add_cancel]; linarith) (by rw [sub_add_cancel]; linarith)
  simp only [sub_add_cancel] at key
  have hyz : |(1 + B) * u + a * v - B * ν - ((1 + B) * u - B * ν)| ≤ a := by
    rw [show (1 + B) * u + a * v - B * ν - ((1 + B) * u - B * ν) = a * v by ring, abs_mul, abs_of_nonneg ha]
    exact mul_le_of_le_one_right ha hv
  have hpow : (2 + B + B * |ν|) ^ (q - 2) ≤ (2 + 2 * B) ^ (q - 2) * (1 + |ν|) ^ (q - 1) :=
    rpow_le_mul_rpow (by linarith) (by linarith) (by linarith [abs_nonneg ν])
      (by nlinarith [abs_nonneg ν]) (by linarith) (by linarith)
  have hqq : 0 ≤ q * (q - 1) := mul_nonneg (by linarith) (by linarith)
  have hP : 0 ≤ (2 + 2 * B) ^ (q - 2) * (1 + |ν|) ^ (q - 1) :=
    mul_nonneg (rpow_nonneg (by linarith) _) (rpow_nonneg (by positivity) _)
  refine key.trans ?_
  rw [hBν]
  calc _ ≤ q * (q - 1) * ((2 + 2 * B) ^ (q - 2) * (1 + |ν|) ^ (q - 1)) * (B * |ν|) * a :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hqq) hBν0) hyz (abs_nonneg _)
          (mul_nonneg (mul_nonneg hqq hP) hBν0)
    _ = _ := by ring

/-- The second bracket of `Δ`: `|ψ(A v - a u) - ψ(A v - a u + a ν)| ≤ q (2+B)^(q-1) · a (1+|ν|)^(q-1) |ν|`. -/
private lemma delta_term2 {q B a u v ν : ℝ} (hq : 2 < q) (hB : 0 < B) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    |(|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q)|
      ≤ q * (2 + B) ^ (q - 1) * (a * (1 + |ν|) ^ (q - 1) * |ν|) := by
  have hA : (0 : ℝ) ≤ 1 + B := by linarith
  obtain ⟨-, hx, -⟩ := abs_lin_le_one hA ha ha1 hv hu
  have hy : |(1 + B) * v - a * u + a * ν| ≤ (2 + B) * (1 + |ν|) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [mul_le_mul_of_nonneg_right (show a ≤ 2 + B by linarith) (abs_nonneg ν)]
  have hmax : max |(1 + B) * v - a * u| |(1 + B) * v - a * u + a * ν| ≤ (2 + B) * (1 + |ν|) :=
    max_le (hx.trans (by nlinarith [abs_nonneg ν])) hy
  have hpow := rpow_le_mul_rpow (le_max_of_le_left (abs_nonneg _)) (by linarith) (by linarith [abs_nonneg ν])
    hmax (by linarith : (0 : ℝ) ≤ q - 1) le_rfl
  have key := abs_rpow_sub_le (by linarith : (1 : ℝ) ≤ q) ((1 + B) * v - a * u) ((1 + B) * v - a * u + a * ν)
  rw [show (1 + B) * v - a * u - ((1 + B) * v - a * u + a * ν) = -(a * ν) by ring, abs_neg, abs_mul,
    abs_of_nonneg ha] at key
  refine key.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith))
    (mul_nonneg ha (abs_nonneg ν))).trans (le_of_eq (by ring)))

/-- `|k₁(v, -u + ν) - 1| ≤ q (1 + |ν|)^(q-1) |ν|` on the unit circle: `k₁(v, -u + ν) = X^(q/2)` with
`X = 1 + ν(ν - 2u)`, and `abs_rpow_sub_le` with exponent `q/2 ≥ 1`. -/
private lemma k1_sub_one_le {q u v ν : ℝ} (hq : 2 < q) (huv : u ^ 2 + v ^ 2 = 1) :
    |k1 q v (-u + ν) - 1| ≤ q * (1 + |ν|) ^ (q - 1) * |ν| := by
  have hu : |u| ≤ 1 := abs_le_one_of_sq_add huv
  unfold k1
  obtain ⟨X, hX⟩ : ∃ X, v ^ 2 + (-u + ν) ^ 2 = X := ⟨_, rfl⟩
  rw [hX]
  have hX0 : 0 ≤ X := by rw [← hX]; positivity
  have h2 : |ν - 2 * u| ≤ 2 + |ν| := by
    refine (abs_sub_le_add _ _).trans ?_
    rw [abs_mul, abs_two]
    linarith
  have hX1 : |X - 1| ≤ (2 + |ν|) * |ν| := by
    rw [show X - 1 = ν * (ν - 2 * u) by rw [← hX]; linear_combination huv, abs_mul]
    calc |ν| * |ν - 2 * u| ≤ |ν| * (2 + |ν|) := mul_le_mul_of_nonneg_left h2 (abs_nonneg ν)
      _ = (2 + |ν|) * |ν| := by ring
  have hmax : max X 1 ≤ (1 + |ν|) ^ 2 :=
    max_le (by linarith [le_abs_self (X - 1)]) (by nlinarith [abs_nonneg ν])
  have hW : ((1 + |ν|) ^ 2) ^ (q / 2 - 1) = (1 + |ν|) ^ (q - 2) := by
    rw [← rpow_natCast (1 + |ν|) 2, ← rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hW1 : (1 + |ν|) ^ (q - 1) = (1 + |ν|) ^ (q - 2) * (1 + |ν|) := by
    rw [← rpow_add_one (by positivity)]
    congr 1
    ring
  have hpow : (max X 1) ^ (q / 2 - 1) ≤ (1 + |ν|) ^ (q - 2) := by
    rw [← hW]
    exact rpow_le_rpow (le_max_of_le_right zero_le_one) hmax (by linarith)
  have hWpos : 0 ≤ (1 + |ν|) ^ (q - 2) := rpow_nonneg (by positivity) _
  have key := abs_rpow_sub_le (q := q / 2) (by linarith) X 1
  rw [abs_of_nonneg hX0, abs_one, one_rpow] at key
  calc |X ^ (q / 2) - 1| ≤ q / 2 * (max X 1) ^ (q / 2 - 1) * |X - 1| := key
    _ ≤ q / 2 * (1 + |ν|) ^ (q - 2) * ((2 + |ν|) * |ν|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by linarith)) hX1 (abs_nonneg _)
          (mul_nonneg (by linarith) hWpos)
    _ ≤ q / 2 * (1 + |ν|) ^ (q - 2) * ((2 * (1 + |ν|)) * |ν|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg ν]) (abs_nonneg ν))
          (mul_nonneg (by linarith) hWpos)
    _ = q * (1 + |ν|) ^ (q - 1) * |ν| := by rw [hW1]; ring

/-- `||-u + ν|^q - |u|^q| ≤ q (1 + |ν|)^(q-1) |ν|` for `|u| ≤ 1`. -/
private lemma psi_shift_le {q u ν : ℝ} (hq : 2 < q) (hu : |u| ≤ 1) :
    |(|-u + ν| ^ q - |u| ^ q)| ≤ q * (1 + |ν|) ^ (q - 1) * |ν| := by
  have key := abs_rpow_sub_le (by linarith : (1 : ℝ) ≤ q) (-u + ν) (-u)
  rw [abs_neg, show -u + ν - -u = ν by ring] at key
  have hmax : max |-u + ν| |u| ≤ 1 + |ν| :=
    max_le ((abs_add_le _ _).trans (by rw [abs_neg]; linarith)) (by linarith [abs_nonneg ν])
  exact key.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (rpow_le_rpow (le_max_of_le_right (abs_nonneg u)) hmax (by linarith)) (by linarith)) (abs_nonneg ν))

/-- G2 (the uniform C¹ bound, Theorem 3.6, Step 5, eq. `eq:Ea`, only in `ν`): `|Δ(u, v, ν)| ≤ L a (1 + |ν|)^(q-1) |ν|` on the unit circle.
Term by term (`A = 1 + B`, `|u|, |v| ≤ 1`, `a ≤ 1`):
* `[ψ(Au + av) - ψ(Au + av - Bν)] - [ψ(Au) - ψ(Au - Bν)]`: `abs_rpow_second_diff_le` (`y = Au + av - Bν`, `z = Au - Bν`,
  `h = Bν`, `M = A + 1 + B|ν|`): `≤ q(q-1) M^(q-2) B|ν| · a`;
* `½[ψ(Av - au) - ψ(Av - au + aν)]`: `abs_rpow_sub_le` (`≤ q (A + 1 + |ν|)^(q-1) a|ν|`);
* `λ₁ (k₁(v, -u + ν) - 1)`: `k₁(v, -u + ν) = (1 + h)^(q/2)` with `h = -2uν + ν²` (as `u² + v² = 1`), `|h| ≤ (2 + |ν|)|ν|`,
  `abs_rpow_sub_le` with exponent `q/2 ≥ 1` (bases `1 + h ≥ 0` and `1`; `max ≤ (1 + |ν|)²`), times `|λ₁| ≤ Λa`;
* `λ₂ (ψ(-u + ν) - ψ(u))`: `|-u + ν|^q - |-u|^q`, `abs_rpow_sub_le`, times `|λ₂| ≤ Λa`.
Then `(1 + |ν|)^(q-2) ≤ (1 + |ν|)^(q-1)` and `M ≤ (A + 1 + B)(1 + |ν|)` collect everything into one `L`. -/
theorem delta_first_order (q B Λ : ℝ) (hq : 2 < q) (hB : 0 < B) (hΛ : 0 ≤ Λ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a l1 l2 u v ν : ℝ, 0 < a → a ≤ 1 → |l1| ≤ Λ * a → |l2| ≤ Λ * a → u ^ 2 + v ^ 2 = 1 →
      |DeltaUV q a B l1 l2 u v ν| ≤ L * a * (1 + |ν|) ^ (q - 1) * |ν| := by
  refine ⟨q * (q - 1) * B * (2 + 2 * B) ^ (q - 2) + q * (2 + B) ^ (q - 1) / 2 + 2 * (Λ * q), ?_, ?_⟩
  · have h1 : 0 ≤ (2 + 2 * B) ^ (q - 2) := rpow_nonneg (by linarith) _
    have h2 : 0 ≤ (2 + B) ^ (q - 1) := rpow_nonneg (by linarith) _
    have h3 : 0 ≤ q * (q - 1) * B := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hB.le
    have h4 : 0 ≤ Λ * q := mul_nonneg hΛ (by linarith)
    have h5 := mul_nonneg h3 h1
    have h6 := mul_nonneg (by linarith : (0 : ℝ) ≤ q) h2
    linarith
  · intro a l1 l2 u v ν ha ha1 hl1 hl2 huv
    have hu : |u| ≤ 1 := abs_le_one_of_sq_add huv
    have hv : |v| ≤ 1 := abs_le_one_of_sq_add (by linarith : v ^ 2 + u ^ 2 = 1)
    have t1 := delta_term1 (ν := ν) hq hB ha.le ha1 hu hv
    have t2 := delta_term2 (ν := ν) hq hB ha.le ha1 hu hv
    have t3 : |l1 * (k1 q v (-u + ν) - 1)| ≤ Λ * q * (a * (1 + |ν|) ^ (q - 1) * |ν|) := by
      rw [abs_mul]
      calc |l1| * |k1 q v (-u + ν) - 1| ≤ (Λ * a) * (q * (1 + |ν|) ^ (q - 1) * |ν|) :=
            mul_le_mul hl1 (k1_sub_one_le hq huv) (abs_nonneg _) (mul_nonneg hΛ ha.le)
        _ = _ := by ring
    have t4 : |l2 * (|-u + ν| ^ q - |u| ^ q)| ≤ Λ * q * (a * (1 + |ν|) ^ (q - 1) * |ν|) := by
      rw [abs_mul]
      calc |l2| * |(|-u + ν| ^ q - |u| ^ q)| ≤ (Λ * a) * (q * (1 + |ν|) ^ (q - 1) * |ν|) :=
            mul_le_mul hl2 (psi_shift_le hq hu) (abs_nonneg _) (mul_nonneg hΛ ha.le)
        _ = _ := by ring
    unfold DeltaUV
    refine (abs_add4_le _ _ _ _).trans ?_
    linarith

end Matsaev.SJ
