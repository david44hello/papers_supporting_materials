/-
Additivity over disjoint unions and arbitrarily large finite diameter gaps.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec1.Products
import LeeDiam.Sec1.SumGraphs
import LeeDiam.Sec1.RepeatedSums
import LeeDiam.Sec3.Band
import LeeDiam.Sec4.Chain
import LeeDiam.Sec6.Order
import LeeDiam.Sec6.Chain

namespace LeeDiam

open Finset

theorem sec1_additive_proved (P Q : Type) [Fintype P] [PartialOrder P] [Fintype Q] [PartialOrder Q] :
    (∀ x : P ⊕ Q → ℝ, x ∈ orderPolytope (P ⊕ Q) ↔
      (x ∘ Sum.inl ∈ orderPolytope P ∧ x ∘ Sum.inr ∈ orderPolytope Q)) ∧
    (∀ x : P ⊕ Q → ℝ, x ∈ chainPolytope (P ⊕ Q) ↔
      (x ∘ Sum.inl ∈ chainPolytope P ∧ x ∘ Sum.inr ∈ chainPolytope Q)) ∧
    orderDiam (P ⊕ Q) = orderDiam P + orderDiam Q ∧ chainDiam (P ⊕ Q) = chainDiam P + chainDiam Q := by
  exact ⟨orderPolytope_sum_iff P Q, chainPolytope_sum_iff P Q, order_diameter_sum, chain_diameter_sum⟩

theorem sec1_many_components_proved (M : ℕ) :
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      orderDiam P = dO ∧ chainDiam P = dC ∧ dC + M ≤ dO) ∧
    (∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (dO dC : ℕ),
      orderDiam P = dO ∧ chainDiam P = dC ∧ dO + M ≤ dC) := by
  refine many_components_from_examples (fun P Q _ _ _ _ =>
    ⟨order_diameter_sum (P := P) (Q := Q), chain_diameter_sum (P := P) (Q := Q)⟩)
    (Band 8) (Pn 4) ?_ ?_ M
  · have upper : chainDiam (Band 8) ≤ (6 : ℕ∞) := by
      simpa using thm_4_1_proved 8 (by decide)
    rw [thm_3_3_proved 8 (by decide)]
    calc
      chainDiam (Band 8) + 1 ≤ (6 : ℕ∞) + 1 := add_le_add upper le_rfl
      _ ≤ (8 : ℕ∞) := by norm_num
  · rw [thm_6_7_proved 4 (by decide), (thm_6_13_proved 4 (by decide)).2]
    norm_num

end LeeDiam
