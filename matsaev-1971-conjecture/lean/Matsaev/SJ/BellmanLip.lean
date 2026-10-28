-- Matsaev/SJ/BellmanLip.lean — F4 of Theorem 3.6 (Step 6, Case 2): the normal derivative n is O(a)-Lipschitz in the angle near θ_* + kπ/2.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar
import Matsaev.SJ.BellmanDefs
import Matsaev.SJ.PsiLib
import Matsaev.SJ.PowLib

/-!
Tools: `Matsaev/SJ/PsiLib.lean` (`abs_phi_eq`, `phi_sub_le`: global bounds for φ), `Matsaev/SJ/PowLib.lean`
(`phi_second_diff_bound`: the second difference of φ away from 0), `Real.abs_cos_sub_cos_le`, `Real.abs_sin_sub_sin_le`.
-/

namespace Matsaev.SJ

open Real

/-! Private helpers. -/

/-- φ is Lipschitz on `[-M, M]` with constant `(q-1) M^(q-2)`. -/
private lemma phi_sub_le_of_bound {q M L u v : ℝ} (hq : 2 ≤ q) (hu : |u| ≤ M) (hv : |v| ≤ M) (hL : |u - v| ≤ L) :
    |phi q u - phi q v| ≤ (q - 1) * M ^ (q - 2) * L := by
  have hM : 0 ≤ M := (abs_nonneg u).trans hu
  have hpow : (max |u| |v|) ^ (q - 2) ≤ M ^ (q - 2) :=
    rpow_le_rpow (le_max_of_le_left (abs_nonneg u)) (max_le hu hv) (by linarith)
  calc |phi q u - phi q v| ≤ (q - 1) * (max |u| |v|) ^ (q - 2) * |u - v| := phi_sub_le hq u v
    _ ≤ (q - 1) * M ^ (q - 2) * L :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by linarith)) hL (abs_nonneg _)
        (mul_nonneg (by linarith) (rpow_nonneg hM _))

/-- Triangle inequality for a difference of five terms. -/
private lemma abs_sub5 (x1 x2 x3 x4 x5 : ℝ) : |x1 - x2 - x3 - x4 - x5| ≤ |x1| + |x2| + |x3| + |x4| + |x5| := by
  have h1 := abs_sub (x1 - x2 - x3 - x4) x5
  have h2 := abs_sub (x1 - x2 - x3) x4
  have h3 := abs_sub (x1 - x2) x3
  have h4 := abs_sub x1 x2
  linarith

/-- F4 (Theorem 3.6, Step 6, Case 2): `n` is Lipschitz in the angle with constant `O(a)` near a point `θ₀` with `|cos θ₀| ≥ κ`.
Write `n(θ) - n(θ₀)` as: `B[φ(Ac + as) - φ(Ac + as₀)]` (`phi_sub_le`, `|s - s₀| ≤ |θ - θ₀|`) `+ B·{[φ(Ac + as₀) - φ(Ac)]
- [φ(Ac₀ + as₀) - φ(Ac₀)]}` (`phi_second_diff_bound` with `m = Aκ`, `y = Ac₀`, `z = Ac`, `h = a s₀`: needs `a ≤ Aκ/4`
and `|Ac₀ - Ac| ≤ A|θ - θ₀| ≤ Aκ/2`) `- (a/2)[φ(As - ac) - φ(As₀ - ac₀)]` (`phi_sub_le`) `- λ₁(c - c₀) - λ₂(φ(c) - φ(c₀))`
(`phi_sub_le`), where `A = 1 + B`, `c = cos θ`, `s = sin θ`, `c₀ = cos θ₀`, `s₀ = sin θ₀`. -/
theorem nUV_lipschitz (q B Λ κ : ℝ) (hq : 2 < q) (hB : 0 < B) (hΛ : 0 ≤ Λ) (hκ : 0 < κ) :
    ∃ a₄ L' : ℝ, 0 < a₄ ∧ 0 ≤ L' ∧ ∀ a l1 l2 θ θ₀ : ℝ, 0 < a → a ≤ a₄ → |l1| ≤ Λ * a → |l2| ≤ Λ * a →
      κ ≤ |Real.cos θ₀| → |θ - θ₀| ≤ κ / 2 →
      |nUV q a B l1 l2 (Real.cos θ) (Real.sin θ) - nUV q a B l1 l2 (Real.cos θ₀) (Real.sin θ₀)| ≤ L' * a * |θ - θ₀| := by
  have hA0 : 0 < 1 + B := by linarith
  have hq2 : (2 : ℝ) ≤ q := hq.le
  obtain ⟨K, hK0, hK⟩ := phi_second_diff_bound hq (m := (1 + B) * κ) (M := 1 + B) (by positivity)
  set a₄ := (1 + B) * κ / 4 with ha₄
  set P := (1 + B + a₄) ^ (q - 2) with hP
  have hP0 : 0 ≤ P := rpow_nonneg (by positivity) _
  refine ⟨a₄, B * (q - 1) * P + B * K * (1 + B) + (q - 1) * P * (1 + B + a₄) / 2 + Λ + Λ * (q - 1),
    by positivity, ?_, ?_⟩
  · have : 0 ≤ q - 1 := by linarith
    positivity
  intro a l1 l2 θ θ₀ ha ha4 hl1 hl2 hκc hθ
  set d := |θ - θ₀| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hcc : |Real.cos θ - Real.cos θ₀| ≤ d := abs_cos_sub_cos_le θ θ₀
  have hss : |Real.sin θ - Real.sin θ₀| ≤ d := abs_sin_sub_sin_le θ θ₀
  have hc1 := abs_cos_le_one θ
  have hc01 := abs_cos_le_one θ₀
  have hs1 := abs_sin_le_one θ
  have hs01 := abs_sin_le_one θ₀
  -- a bound `|A x + a y| ≤ A + a₄` for `|x|, |y| ≤ 1`
  have hlin : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |(1 + B) * x + a * y| ≤ 1 + B + a₄ := by
    intro x y hx hy
    calc |(1 + B) * x + a * y| ≤ |(1 + B) * x| + |a * y| := abs_add_le _ _
      _ = (1 + B) * |x| + a * |y| := by rw [abs_mul, abs_mul, abs_of_pos hA0, abs_of_pos ha]
      _ ≤ (1 + B) * 1 + a * 1 := by gcongr
      _ ≤ 1 + B + a₄ := by linarith
  -- term 1: `φ(Ac + as) - φ(Ac + as₀)`
  have h1 : |phi q ((1 + B) * Real.cos θ + a * Real.sin θ) - phi q ((1 + B) * Real.cos θ + a * Real.sin θ₀)|
      ≤ (q - 1) * P * (a * d) := by
    refine phi_sub_le_of_bound hq2 (hlin _ _ hc1 hs1) (hlin _ _ hc1 hs01) ?_
    rw [show (1 + B) * Real.cos θ + a * Real.sin θ - ((1 + B) * Real.cos θ + a * Real.sin θ₀)
      = a * (Real.sin θ - Real.sin θ₀) by ring, abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left hss ha.le
  -- term 2: the second difference
  have h2 : |(phi q ((1 + B) * Real.cos θ₀ + a * Real.sin θ₀) - phi q ((1 + B) * Real.cos θ₀)) -
      (phi q ((1 + B) * Real.cos θ + a * Real.sin θ₀) - phi q ((1 + B) * Real.cos θ))| ≤ K * a * ((1 + B) * d) := by
    have hy : (1 + B) * κ ≤ |(1 + B) * Real.cos θ₀| := by
      rw [abs_mul, abs_of_pos hA0]; exact mul_le_mul_of_nonneg_left hκc hA0.le
    have hyz' : |(1 + B) * Real.cos θ₀ - (1 + B) * Real.cos θ| ≤ (1 + B) * d := by
      rw [← mul_sub, abs_mul, abs_of_pos hA0, abs_sub_comm]; exact mul_le_mul_of_nonneg_left hcc hA0.le
    have hyz : |(1 + B) * Real.cos θ₀ - (1 + B) * Real.cos θ| ≤ (1 + B) * κ / 2 := by
      have : (1 + B) * d ≤ (1 + B) * (κ / 2) := mul_le_mul_of_nonneg_left hθ hA0.le
      linarith
    have hh : |a * Real.sin θ₀| ≤ (1 + B) * κ / 4 := by
      rw [abs_mul, abs_of_pos ha]
      calc a * |Real.sin θ₀| ≤ a * 1 := mul_le_mul_of_nonneg_left hs01 ha.le
        _ ≤ (1 + B) * κ / 4 := by rw [mul_one]; exact ha4
    have hyM : |(1 + B) * Real.cos θ₀| ≤ 1 + B := by
      rw [abs_mul, abs_of_pos hA0]; nlinarith
    have hk := hK ((1 + B) * Real.cos θ₀) ((1 + B) * Real.cos θ) (a * Real.sin θ₀) hy hyz hh hyM
    calc _ ≤ K * |a * Real.sin θ₀| * |(1 + B) * Real.cos θ₀ - (1 + B) * Real.cos θ| := hk
      _ ≤ K * a * ((1 + B) * d) := by
        have ha1 : |a * Real.sin θ₀| ≤ a := by
          rw [abs_mul, abs_of_pos ha]; nlinarith
        gcongr
  -- term 3: `φ(As - ac) - φ(As₀ - ac₀)`
  have h3 : |phi q ((1 + B) * Real.sin θ - a * Real.cos θ) - phi q ((1 + B) * Real.sin θ₀ - a * Real.cos θ₀)|
      ≤ (q - 1) * P * ((1 + B + a₄) * d) := by
    have hlin' : ∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |(1 + B) * x - a * y| ≤ 1 + B + a₄ := fun x y hx hy => by
      have := hlin x (-y) hx (by rwa [abs_neg])
      rwa [show (1 + B) * x + a * -y = (1 + B) * x - a * y by ring] at this
    refine phi_sub_le_of_bound hq2 (hlin' _ _ hs1 hc1) (hlin' _ _ hs01 hc01) ?_
    rw [show (1 + B) * Real.sin θ - a * Real.cos θ - ((1 + B) * Real.sin θ₀ - a * Real.cos θ₀)
      = (1 + B) * (Real.sin θ - Real.sin θ₀) - a * (Real.cos θ - Real.cos θ₀) by ring]
    calc _ ≤ |(1 + B) * (Real.sin θ - Real.sin θ₀)| + |a * (Real.cos θ - Real.cos θ₀)| := abs_sub _ _
      _ = (1 + B) * |Real.sin θ - Real.sin θ₀| + a * |Real.cos θ - Real.cos θ₀| := by
        rw [abs_mul, abs_mul, abs_of_pos hA0, abs_of_pos ha]
      _ ≤ (1 + B) * d + a₄ * d := by gcongr
      _ = (1 + B + a₄) * d := by ring
  -- term 5: `φ(c) - φ(c₀)`
  have h5 : |phi q (Real.cos θ) - phi q (Real.cos θ₀)| ≤ (q - 1) * 1 ^ (q - 2) * d :=
    phi_sub_le_of_bound hq2 hc1 hc01 hcc
  rw [one_rpow, mul_one] at h5
  -- assemble
  have hE : nUV q a B l1 l2 (Real.cos θ) (Real.sin θ) - nUV q a B l1 l2 (Real.cos θ₀) (Real.sin θ₀) =
      B * (phi q ((1 + B) * Real.cos θ + a * Real.sin θ) - phi q ((1 + B) * Real.cos θ + a * Real.sin θ₀))
      - B * ((phi q ((1 + B) * Real.cos θ₀ + a * Real.sin θ₀) - phi q ((1 + B) * Real.cos θ₀)) -
          (phi q ((1 + B) * Real.cos θ + a * Real.sin θ₀) - phi q ((1 + B) * Real.cos θ)))
      - a / 2 * (phi q ((1 + B) * Real.sin θ - a * Real.cos θ) - phi q ((1 + B) * Real.sin θ₀ - a * Real.cos θ₀))
      - l1 * (Real.cos θ - Real.cos θ₀) - l2 * (phi q (Real.cos θ) - phi q (Real.cos θ₀)) := by
    unfold nUV R1
    ring
  rw [hE]
  refine (abs_sub5 _ _ _ _ _).trans ?_
  rw [abs_mul B, abs_mul B, abs_mul (a / 2), abs_mul l1, abs_mul l2, abs_of_pos hB, abs_of_pos (by positivity : 0 < a / 2)]
  have b1 := mul_le_mul_of_nonneg_left h1 hB.le
  have b2 := mul_le_mul_of_nonneg_left h2 hB.le
  have b3 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ a / 2)
  have b4 : |l1| * |Real.cos θ - Real.cos θ₀| ≤ Λ * a * d := mul_le_mul hl1 hcc (abs_nonneg _) (by positivity)
  have b5 : |l2| * |phi q (Real.cos θ) - phi q (Real.cos θ₀)| ≤ Λ * a * ((q - 1) * d) :=
    mul_le_mul hl2 h5 (abs_nonneg _) (by positivity)
  calc _ ≤ B * ((q - 1) * P * (a * d)) + B * (K * a * ((1 + B) * d)) + a / 2 * ((q - 1) * P * ((1 + B + a₄) * d))
        + Λ * a * d + Λ * a * ((q - 1) * d) := by linarith
    _ = (B * (q - 1) * P + B * K * (1 + B) + (q - 1) * P * (1 + B + a₄) / 2 + Λ + Λ * (q - 1)) * a * d := by ring

end Matsaev.SJ
