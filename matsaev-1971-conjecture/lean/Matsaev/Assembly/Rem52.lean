/-
Matsaev/Assembly/Rem52.lean — the pointwise strict inequality behind Remark 5.2 (`‖2I + αJ‖_p < 2 + |α|`, real `α ≠ 0`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Matsaev.Rem52

/-- The pointwise strict bound behind Remark 5.2: for `q > 1`, real `α ≠ 0` and `(u, v) ≠ 0`,
`|2u + αv|^q + |2v - αu|^q < (2 + |α|)^q (|u|^q + |v|^q)`. -/
theorem pointwise_lt (q : ℝ) (hq : 1 < q) (α u v : ℝ) (hα : α ≠ 0) (huv : u ≠ 0 ∨ v ≠ 0) :
    |2 * u + α * v| ^ q + |2 * v - α * u| ^ q < (2 + |α|) ^ q * (|u| ^ q + |v| ^ q) := by
  have hs : 0 < 2 + |α| := by positivity
  set s := 2 + |α| with hsdef
  have hαpos : 0 < |α| := abs_pos.mpr hα
  set w₁ := 2 / s with hw₁
  set w₂ := |α| / s with hw₂
  have hw₁p : 0 < w₁ := by positivity
  have hw₂p : 0 < w₂ := by positivity
  have hw : w₁ + w₂ = 1 := by rw [hw₁, hw₂, ← add_div, div_self hs.ne']
  have hconv := (strictConvexOn_rpow hq)
  -- convexity: (w₁ x + w₂ y)^q ≤ w₁ x^q + w₂ y^q on [0, ∞)
  have hc : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (w₁ * x + w₂ * y) ^ q ≤ w₁ * x ^ q + w₂ * y ^ q := fun x y hx hy => by
    have := hconv.convexOn.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hw₁p.le hw₂p.le hw
    simpa [smul_eq_mul] using this
  have hcs : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≠ y → (w₁ * x + w₂ * y) ^ q < w₁ * x ^ q + w₂ * y ^ q :=
    fun x y hx hy hxy => by
      have := hconv.2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy) hxy hw₁p hw₂p hw
      simpa [smul_eq_mul] using this
  -- triangle bounds
  have hB₁ : 2 * |u| + |α| * |v| = s * (w₁ * |u| + w₂ * |v|) := by
    rw [hw₁, hw₂]; field_simp
  have hB₂ : 2 * |v| + |α| * |u| = s * (w₁ * |v| + w₂ * |u|) := by
    rw [hw₁, hw₂]; field_simp
  have ht₁ : |2 * u + α * v| ≤ 2 * |u| + |α| * |v| := by
    calc |2 * u + α * v| ≤ |2 * u| + |α * v| := abs_add_le _ _
      _ = 2 * |u| + |α| * |v| := by rw [abs_mul, abs_mul, abs_two]
  have ht₂ : |2 * v - α * u| ≤ 2 * |v| + |α| * |u| := by
    calc |2 * v - α * u| ≤ |2 * v| + |α * u| := abs_sub _ _
      _ = 2 * |v| + |α| * |u| := by rw [abs_mul, abs_mul, abs_two]
  have hq0 : 0 ≤ q := by linarith
  have hpow : ∀ x y : ℝ, 0 ≤ x → x ≤ s * y → x ^ q ≤ s ^ q * y ^ q := fun x y hx hxy => by
    have hy : 0 ≤ y := by
      by_contra h; push Not at h; nlinarith
    rw [← Real.mul_rpow hs.le hy]
    exact Real.rpow_le_rpow hx hxy hq0
  have hpow_lt : ∀ x y : ℝ, 0 ≤ x → x < s * y → x ^ q < s ^ q * y ^ q := fun x y hx hxy => by
    have hy : 0 ≤ y := by
      by_contra h; push Not at h; nlinarith
    rw [← Real.mul_rpow hs.le hy]
    exact Real.rpow_lt_rpow hx hxy (by linarith)
  have hu0 := abs_nonneg u
  have hv0 := abs_nonneg v
  have hsq : 0 < s ^ q := Real.rpow_pos_of_pos hs q
  -- the sum of the convexity bounds
  have hsum : s ^ q * (w₁ * |u| ^ q + w₂ * |v| ^ q) + s ^ q * (w₁ * |v| ^ q + w₂ * |u| ^ q) =
      s ^ q * (|u| ^ q + |v| ^ q) := by
    have : w₁ * |u| ^ q + w₂ * |v| ^ q + (w₁ * |v| ^ q + w₂ * |u| ^ q) = (w₁ + w₂) * (|u| ^ q + |v| ^ q) := by ring
    rw [← mul_add, this, hw, one_mul]
  by_cases huv' : |u| = |v|
  · -- equal moduli: one triangle inequality is strict
    have hu : u ≠ 0 := by
      rcases huv with h | h
      · exact h
      · intro h0; apply h; rw [h0, abs_zero] at huv'; exact abs_eq_zero.mp huv'.symm
    have hv : v ≠ 0 := by
      intro h0; apply hu; rw [h0, abs_zero] at huv'; exact abs_eq_zero.mp huv'
    have hstrict : |2 * u + α * v| < 2 * |u| + |α| * |v| ∨ |2 * v - α * u| < 2 * |v| + |α| * |u| := by
      by_contra hne
      push Not at hne
      obtain ⟨h₁, h₂⟩ := hne
      have e₁ : |2 * u + α * v| = |2 * u| + |α * v| := by
        rw [abs_mul, abs_mul, abs_two]; exact le_antisymm ht₁ h₁
      have e₂ : |2 * v + -(α * u)| = |2 * v| + |-(α * u)| := by
        rw [abs_neg, abs_mul, abs_mul, abs_two, ← sub_eq_add_neg]; exact le_antisymm ht₂ h₂
      rw [abs_add_eq_add_abs_iff] at e₁ e₂
      have hα2 : 0 < α ^ 2 := by positivity
      have huv2 : 0 < u ^ 2 * v ^ 2 := by positivity
      have p₁ : 0 ≤ (2 * u) * (α * v) := by
        rcases e₁ with ⟨a1, a2⟩ | ⟨a1, a2⟩
        exacts [mul_nonneg a1 a2, mul_nonneg_of_nonpos_of_nonpos a1 a2]
      have p₂ : 0 ≤ (2 * v) * -(α * u) := by
        rcases e₂ with ⟨b1, b2⟩ | ⟨b1, b2⟩
        exacts [mul_nonneg b1 b2, mul_nonneg_of_nonpos_of_nonpos b1 b2]
      nlinarith [mul_nonneg p₁ p₂, mul_pos hα2 huv2]
    have hA : |2 * u + α * v| ^ q ≤ s ^ q * (w₁ * |u| + w₂ * |v|) ^ q :=
      hpow _ _ (abs_nonneg _) (by rw [← hB₁]; exact ht₁)
    have hB : |2 * v - α * u| ^ q ≤ s ^ q * (w₁ * |v| + w₂ * |u|) ^ q :=
      hpow _ _ (abs_nonneg _) (by rw [← hB₂]; exact ht₂)
    have hcA := hc |u| |v| hu0 hv0
    have hcB := hc |v| |u| hv0 hu0
    rcases hstrict with h | h
    · have hA' : |2 * u + α * v| ^ q < s ^ q * (w₁ * |u| + w₂ * |v|) ^ q :=
        hpow_lt _ _ (abs_nonneg _) (by rw [← hB₁]; exact h)
      nlinarith
    · have hB' : |2 * v - α * u| ^ q < s ^ q * (w₁ * |v| + w₂ * |u|) ^ q :=
        hpow_lt _ _ (abs_nonneg _) (by rw [← hB₂]; exact h)
      nlinarith
  · -- different moduli: the convexity inequality is strict
    have hA : |2 * u + α * v| ^ q ≤ s ^ q * (w₁ * |u| + w₂ * |v|) ^ q :=
      hpow _ _ (abs_nonneg _) (by rw [← hB₁]; exact ht₁)
    have hB : |2 * v - α * u| ^ q ≤ s ^ q * (w₁ * |v| + w₂ * |u|) ^ q :=
      hpow _ _ (abs_nonneg _) (by rw [← hB₂]; exact ht₂)
    have hcA := hcs |u| |v| hu0 hv0 huv'
    have hcB := hc |v| |u| hv0 hu0
    nlinarith

end Matsaev.Rem52
