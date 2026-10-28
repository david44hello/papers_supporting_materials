-- Matsaev/SJ/BellmanCases.lean — the cases of Step 6 of the proof of Theorem 3.6 (`thm:SJ`), as pure inequalities between reals.
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib

/-!
In use: `F = F₀(u, -u + ν)` (Lemma 3.3 gives `hF`), `S = Σ_a(θ) ≥ 0`, `Δ = Δ(u, v, ν)`, and the window value is
`F + S/4 + Δ`. `q > 2` is the exponent, `u = cos θ`, `n = n(u, v)` the normal derivative / q, `r` the angle distance to the
zero set of `Σ_a`.
-/

namespace Matsaev.SJ

/-- Large `|ν|` (Theorem 3.6, Step 6, Case 1, second half): the Lemma 3.3 term `≥ c₁ |ν|^q` beats `|Δ| ≤ L a (1 + 1/ν₂)^(q-1) |ν|^q`. -/
theorem case_large {q c₁ L a ν₂ ν u F S Δ : ℝ} (hq : 2 < q) (hc₁ : 0 < c₁) (hL : 0 ≤ L) (ha : 0 < a)
    (hν₂ : 0 < ν₂) (hν₂1 : ν₂ ≤ 1) (hν : ν₂ ≤ |ν|)
    (hF : c₁ * (|u| + |ν|) ^ (q - 2) * ν ^ 2 ≤ F) (hS : 0 ≤ S)
    (hΔ : |Δ| ≤ L * a * (1 + |ν|) ^ (q - 1) * |ν|) (hsmall : L * a * (1 / ν₂ + 1) ^ (q - 1) ≤ c₁) :
    0 ≤ F + S / 4 + Δ := by
  have hνpos : 0 < |ν| := lt_of_lt_of_le hν₂ hν
  have hq2 : 0 < q - 2 := by linarith
  have hq1 : 0 ≤ q - 1 := by linarith
  -- F ≥ c₁ |ν|^q
  have h1 : |ν| ^ (q - 2) ≤ (|u| + |ν|) ^ (q - 2) :=
    Real.rpow_le_rpow (abs_nonneg ν) (by linarith [abs_nonneg u]) hq2.le
  have hνq : |ν| ^ (q - 2) * ν ^ 2 = |ν| ^ q := by
    rw [← sq_abs ν, ← Real.rpow_natCast |ν| 2, ← Real.rpow_add hνpos]
    congr 1
    push_cast
    ring
  have hF' : c₁ * |ν| ^ q ≤ F := by
    calc c₁ * |ν| ^ q = c₁ * (|ν| ^ (q - 2) * ν ^ 2) := by rw [hνq]
      _ ≤ c₁ * ((|u| + |ν|) ^ (q - 2) * ν ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg ν)) hc₁.le
      _ = c₁ * (|u| + |ν|) ^ (q - 2) * ν ^ 2 := by ring
      _ ≤ F := hF
  -- |Δ| ≤ L a (1/ν₂ + 1)^(q-1) |ν|^q, since 1 + |ν| ≤ |ν| (1/ν₂ + 1)
  have h2 : 1 + |ν| ≤ |ν| * (1 / ν₂ + 1) := by
    have h : 1 ≤ |ν| / ν₂ := by rw [le_div_iff₀ hν₂]; linarith
    have h' : |ν| * (1 / ν₂ + 1) = |ν| / ν₂ + |ν| := by ring
    rw [h']
    linarith
  have h3 : (1 + |ν|) ^ (q - 1) ≤ |ν| ^ (q - 1) * (1 / ν₂ + 1) ^ (q - 1) := by
    rw [← Real.mul_rpow (abs_nonneg ν) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h2 hq1
  have hLa : 0 ≤ L * a := mul_nonneg hL ha.le
  have h4 : |Δ| ≤ L * a * (1 / ν₂ + 1) ^ (q - 1) * |ν| ^ q := by
    calc |Δ| ≤ L * a * (1 + |ν|) ^ (q - 1) * |ν| := hΔ
      _ ≤ L * a * (|ν| ^ (q - 1) * (1 / ν₂ + 1) ^ (q - 1)) * |ν| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hLa) (abs_nonneg ν)
      _ = L * a * (1 / ν₂ + 1) ^ (q - 1) * (|ν| ^ (q - 1) * |ν|) := by ring
      _ = L * a * (1 / ν₂ + 1) ^ (q - 1) * |ν| ^ q := by
        rw [← Real.rpow_add_one hνpos.ne', sub_add_cancel]
  have h5 : L * a * (1 / ν₂ + 1) ^ (q - 1) * |ν| ^ q ≤ c₁ * |ν| ^ q :=
    mul_le_mul_of_nonneg_right hsmall (by positivity)
  have h6 := neg_abs_le Δ
  linarith

/-- Small `|ν|`, far from the extremal angles (Theorem 3.6, Step 6, Case 1): `S/4 ≥ a η ρ²/4` beats `|Δ| ≤ L a 2^(q-1) ν₂`. -/
theorem case_far {q L a η ρ ν₂ ν F S Δ : ℝ} (hq : 2 < q) (hL : 0 ≤ L) (ha : 0 < a) (hη : 0 < η) (hρ : 0 < ρ)
    (hν₂1 : ν₂ ≤ 1) (hν : |ν| ≤ ν₂) (hF : 0 ≤ F) (hS : a * η * ρ ^ 2 ≤ S)
    (hΔ : |Δ| ≤ L * a * (1 + |ν|) ^ (q - 1) * |ν|) (hsmall : L * 2 ^ (q - 1) * ν₂ ≤ η * ρ ^ 2 / 4) :
    0 ≤ F + S / 4 + Δ := by
  have hν0 : 0 ≤ |ν| := abs_nonneg ν
  have h1 : (1 + |ν|) ^ (q - 1) ≤ 2 ^ (q - 1) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hLa : 0 ≤ L * a := mul_nonneg hL ha.le
  have h2 : |Δ| ≤ L * a * 2 ^ (q - 1) * ν₂ :=
    hΔ.trans (mul_le_mul (mul_le_mul_of_nonneg_left h1 hLa) hν hν0 (by positivity))
  have h3 : L * a * 2 ^ (q - 1) * ν₂ ≤ a * η * ρ ^ 2 / 4 := by
    calc L * a * 2 ^ (q - 1) * ν₂ = a * (L * 2 ^ (q - 1) * ν₂) := by ring
      _ ≤ a * (η * ρ ^ 2 / 4) := mul_le_mul_of_nonneg_left hsmall ha.le
      _ = a * η * ρ ^ 2 / 4 := by ring
  have h4 := neg_abs_le Δ
  linarith

/-- Small `|ν|`, near the extremal angles (Theorem 3.6, Step 6, Case 2): with `Q₀ = c₁ κ^(q-2)/2`,
`F + S/4 + Δ ≥ Q₀ ν² + (a η/4) r² - q L' a r |ν| ≥ 0` because `(q L' a)² ≤ a η Q₀` (a discriminant). -/
theorem case_near {q c₁ κ K L' a η r ν u n F S Δ : ℝ} (hq : 2 < q) (hc₁ : 0 < c₁) (hκ : 0 < κ) (ha : 0 < a)
    (hη : 0 < η) (hr : 0 ≤ r) (hu : κ ≤ |u|) (hF : c₁ * (|u| + |ν|) ^ (q - 2) * ν ^ 2 ≤ F) (hS : a * η * r ^ 2 ≤ S)
    (hΔ : |Δ - q * ν * n| ≤ K * a * ν ^ 2) (hn : |n| ≤ L' * a * r)
    (hK : K * a ≤ c₁ * κ ^ (q - 2) / 2) (hL' : q ^ 2 * L' ^ 2 * a ≤ η * (c₁ * κ ^ (q - 2) / 2)) :
    0 ≤ F + S / 4 + Δ := by
  set Q₀ := c₁ * κ ^ (q - 2) / 2 with hQ₀
  have hκq : 0 < κ ^ (q - 2) := Real.rpow_pos_of_pos hκ _
  have hQ₀pos : 0 < Q₀ := by positivity
  -- F ≥ 2 Q₀ ν², since |u| + |ν| ≥ κ
  have h1 : κ ^ (q - 2) ≤ (|u| + |ν|) ^ (q - 2) :=
    Real.rpow_le_rpow hκ.le (by linarith [abs_nonneg ν]) (by linarith)
  have hF' : 2 * Q₀ * ν ^ 2 ≤ F := by
    calc 2 * Q₀ * ν ^ 2 = c₁ * κ ^ (q - 2) * ν ^ 2 := by rw [hQ₀]; ring
      _ ≤ c₁ * (|u| + |ν|) ^ (q - 2) * ν ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc₁.le) (sq_nonneg ν)
      _ ≤ F := hF
  -- Δ ≥ q ν n - K a ν² ≥ -q L' a r |ν| - Q₀ ν²
  have hΔ' : q * ν * n - K * a * ν ^ 2 ≤ Δ := by
    have := (abs_le.mp hΔ).1
    linarith
  have hqn : -(q * L' * a * r * |ν|) ≤ q * ν * n := by
    have hb : |q * ν * n| ≤ q * L' * a * r * |ν| := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q)]
      calc q * |ν| * |n| ≤ q * |ν| * (L' * a * r) :=
            mul_le_mul_of_nonneg_left hn (mul_nonneg (by linarith) (abs_nonneg ν))
        _ = q * L' * a * r * |ν| := by ring
    linarith [(abs_le.mp hb).1]
  have hKa : K * a * ν ^ 2 ≤ Q₀ * ν ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg ν)
  -- the quadratic form Q₀ X² + (a η / 4) Y² - (q L' a) X Y is ≥ 0 (discriminant)
  have hb2 : (q * L' * a) ^ 2 ≤ Q₀ * (a * η) := by
    calc (q * L' * a) ^ 2 = (q ^ 2 * L' ^ 2 * a) * a := by ring
      _ ≤ (η * Q₀) * a := mul_le_mul_of_nonneg_right hL' ha.le
      _ = Q₀ * (a * η) := by ring
  have hdisc : 0 ≤ Q₀ * ν ^ 2 + a * η / 4 * r ^ 2 - q * L' * a * r * |ν| := by
    have key : 4 * Q₀ * (Q₀ * ν ^ 2 + a * η / 4 * r ^ 2 - q * L' * a * r * |ν|) =
        (2 * Q₀ * |ν| - q * L' * a * r) ^ 2 + (Q₀ * (a * η) - (q * L' * a) ^ 2) * r ^ 2 := by
      rw [← sq_abs ν]
      ring
    have hrhs : 0 ≤ (2 * Q₀ * |ν| - q * L' * a * r) ^ 2 + (Q₀ * (a * η) - (q * L' * a) ^ 2) * r ^ 2 :=
      add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
    rw [← key] at hrhs
    nlinarith
  linarith

end Matsaev.SJ
