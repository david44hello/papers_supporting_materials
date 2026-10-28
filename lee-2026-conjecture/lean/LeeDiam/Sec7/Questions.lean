/-
LeeDiam/Sec7/Questions.lean — Section 7: the remark after Question 7.1; the ratio 4/3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band
import LeeDiam.Defs.Pn
import LeeDiam.Cited.Lee26
import LeeDiam.Sec1.Bounds
import LeeDiam.Sec1.Main
import LeeDiam.Sec3.Band
import LeeDiam.Sec5.Upper

namespace LeeDiam

open Finset

namespace S7

/-- `3 ≤ x` fails for `x ≤ 1` in `ℕ∞`. -/
theorem not_three_le_of_le_one {x : ℕ∞} (hx : x ≤ 1) (h3 : 3 ≤ x) : False := by
  have h := h3.trans hx
  exact absurd (show (3 : ℕ) ≤ 1 by exact_mod_cast h) (by norm_num)

/-- Remark (a): if `orderDiam P ≤ 2`, Theorem 1.5 gives `chainDiam P ≤ 4`, too small for a gap of 3. -/
theorem three_le_orderDiam (P : Type) [Fintype P] [PartialOrder P]
    (h : orderDiam P + 3 ≤ chainDiam P) : 3 ≤ orderDiam P := by
  by_contra hlt
  have h2 : orderDiam P ≤ 2 :=
    Order.le_of_lt_add_one (by rw [show (2 : ℕ∞) + 1 = 3 by norm_num]; exact not_le.1 hlt)
  have h3 : (3 : ℕ∞) ≤ chainDiam P := le_add_self.trans h
  rcases isEmpty_or_nonempty P with hE | hN
  · exact not_three_le_of_le_one ((S1.diam_empty hE).2.le.trans zero_le_one) h3
  by_cases h1 : orderDiam P ≤ 1
  · exact not_three_le_of_le_one (S1.chainDiam_chain hN (S1.chain_of_orderDiam_le_one h1)).le h3
  have h2' : (2 : ℕ∞) ≤ orderDiam P :=
    S1.two_le_of_ne (fun e => h1 (by rw [e]; exact zero_le_one)) (fun e => h1 e.le)
  have h5 : (5 : ℕ∞) ≤ chainDiam P :=
    calc (5 : ℕ∞) = 2 + 3 := by norm_num
      _ ≤ orderDiam P + 3 := by gcongr
      _ ≤ chainDiam P := h
  have h54 := h5.trans (thm_1_5_proved P h2)
  exact absurd (show (5 : ℕ) ≤ 4 by exact_mod_cast h54) (by norm_num)

/-- `r * d < k` from `4 d ≤ 3 (k + 1)` and `3 r < k0 (4 - 3 r)`, `k = k0 + 1`. -/
theorem ratio_lt (r : ℝ) (hr : r < 4 / 3) (k0 d : ℕ) (hk0 : 3 * r / (4 - 3 * r) < k0)
    (hdk : 4 * d ≤ 3 * (k0 + 1 + 1)) (hd : 0 < (d : ℝ)) : r < ((k0 + 1 : ℕ) : ℝ) / d := by
  rw [lt_div_iff₀ hd]
  push_cast
  have h43 : (0 : ℝ) < 4 - 3 * r := by linarith
  have hk0' : 3 * r < k0 * (4 - 3 * r) := by rwa [div_lt_iff₀ h43] at hk0
  have hdk' : (4 : ℝ) * d ≤ 3 * (k0 + 1 + 1) := by exact_mod_cast hdk
  have hk0nn : (0 : ℝ) ≤ k0 := Nat.cast_nonneg k0
  rcases le_or_gt r 0 with hr0 | hr0
  · nlinarith
  · have e1 : r * (4 * d) ≤ r * (3 * (k0 + 1 + 1)) := mul_le_mul_of_nonneg_left hdk' hr0.le
    nlinarith

/-- The ratio row, given the chain diameter bound of the bands. -/
theorem ratio_of_band
    (hband : ∀ k : ℕ, 1 ≤ k → ∃ d : ℕ, chainDiam (Band k) = d ∧ 4 * d ≤ 3 * (k + 1))
    (r : ℝ) (hr : r < 4 / 3) :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ), IsConnPoset P ∧ orderDiam P = dO ∧
      chainDiam P = dC ∧ 0 < dC ∧ r < (dO : ℝ) / dC := by
  obtain ⟨k0, hk0⟩ := exists_nat_gt (3 * r / (4 - 3 * r))
  have hk : 1 ≤ k0 + 1 := Nat.le_add_left 1 k0
  obtain ⟨d, hd, hdk⟩ := hband (k0 + 1) hk
  have hne : Nonempty (Band (k0 + 1)) := ⟨show Fin (k0 + 1) × Fin 3 from (0, 0)⟩
  have hd1 : 1 ≤ d := by
    have h1 := S1.one_le_chainDiam hne
    rw [hd] at h1
    exact_mod_cast h1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  exact ⟨Band (k0 + 1), inferInstance, inferInstance, k0 + 1, d,
    (lem_3_1_consequences_proved (k0 + 1)).2.2.1 hk, thm_3_3_proved (k0 + 1) hk, hd, hd1,
    ratio_lt r hr k0 d hk0 hdk hdR⟩

end S7

theorem sec7_q1_remark_proved :
    (∀ (P : Type) [Fintype P] [PartialOrder P], (compGraph P).Preconnected →
      orderDiam P + 3 ≤ chainDiam P → 3 ≤ orderDiam P) ∧
    (∀ (P : Type) [Fintype P] [PartialOrder P], IsEmpty P → orderDiam P = 0 ∧ chainDiam P = 0) ∧
    (∀ (P : Type) [Fintype P] [PartialOrder P], Nonempty P → orderDiam P ≤ 1 →
      IsChain (· ≤ ·) (Set.univ : Set P) ∧ chainDiam P = 1) := by
  refine ⟨fun P _ _ _ h => S7.three_le_orderDiam P h, fun P _ _ hP => S1.diam_empty hP,
    fun P _ _ hP h1 => ?_⟩
  have hc := S1.chain_of_orderDiam_le_one h1
  exact ⟨hc, S1.chainDiam_chain hP hc⟩

theorem sec7_ratio_proved (r : ℝ) (hr : r < 4 / 3) :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ), IsConnPoset P ∧ orderDiam P = dO ∧
      chainDiam P = dC ∧ 0 < dC ∧ r < (dO : ℝ) / dC :=
  S7.ratio_of_band S1.band_chain_nat r hr

end LeeDiam
