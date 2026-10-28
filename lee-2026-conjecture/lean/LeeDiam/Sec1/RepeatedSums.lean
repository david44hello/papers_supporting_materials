/-
Arbitrarily large finite diameter gaps by repeated disjoint sums.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec2.ComponentPaths

namespace LeeDiam

section RepeatedSums

theorem repeat_order_gap
    (additive : ∀ (P Q : Type) [Fintype P] [PartialOrder P] [Fintype Q] [PartialOrder Q],
      orderDiam (P ⊕ Q) = orderDiam P + orderDiam Q ∧ chainDiam (P ⊕ Q) = chainDiam P + chainDiam Q)
    (P : Type) [Fintype P] [PartialOrder P] (gap : chainDiam P + 1 ≤ orderDiam P) (M : ℕ) :
    ∃ (T : Type) (_ : Fintype T) (_ : PartialOrder T), chainDiam T + M ≤ orderDiam T := by
  induction M with
  | zero =>
    refine ⟨P, inferInstance, inferInstance, ?_⟩
    simp only [Nat.cast_zero, add_zero]
    exact (le_add_of_nonneg_right (show (0 : ℕ∞) ≤ 1 from zero_le)).trans gap
  | succ M ih =>
    obtain ⟨T, finite, ordered, previous⟩ := ih
    let : Fintype T := finite
    let : PartialOrder T := ordered
    refine ⟨T ⊕ P, inferInstance, inferInstance, ?_⟩
    rw [(additive T P).1, (additive T P).2]
    calc
      chainDiam T + chainDiam P + ((M + 1 : ℕ) : ℕ∞) =
          (chainDiam T + M) + (chainDiam P + 1) := by push_cast; ac_rfl
      _ ≤ orderDiam T + orderDiam P := add_le_add previous gap

theorem repeat_chain_gap
    (additive : ∀ (P Q : Type) [Fintype P] [PartialOrder P] [Fintype Q] [PartialOrder Q],
      orderDiam (P ⊕ Q) = orderDiam P + orderDiam Q ∧ chainDiam (P ⊕ Q) = chainDiam P + chainDiam Q)
    (P : Type) [Fintype P] [PartialOrder P] (gap : orderDiam P + 1 ≤ chainDiam P) (M : ℕ) :
    ∃ (T : Type) (_ : Fintype T) (_ : PartialOrder T), orderDiam T + M ≤ chainDiam T := by
  induction M with
  | zero =>
    refine ⟨P, inferInstance, inferInstance, ?_⟩
    simp only [Nat.cast_zero, add_zero]
    exact (le_add_of_nonneg_right (show (0 : ℕ∞) ≤ 1 from zero_le)).trans gap
  | succ M ih =>
    obtain ⟨T, finite, ordered, previous⟩ := ih
    let : Fintype T := finite
    let : PartialOrder T := ordered
    refine ⟨T ⊕ P, inferInstance, inferInstance, ?_⟩
    rw [(additive T P).1, (additive T P).2]
    calc
      orderDiam T + orderDiam P + ((M + 1 : ℕ) : ℕ∞) =
          (orderDiam T + M) + (orderDiam P + 1) := by push_cast; ac_rfl
      _ ≤ chainDiam T + chainDiam P := add_le_add previous gap

theorem diameter_values_finite (P : Type) [Fintype P] [PartialOrder P] :
    ∃ a b : ℕ, orderDiam P = a ∧ chainDiam P = b := by
  have finite_order : orderDiam P ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt order_diameter_le_width (by simp))
  have finite_chain : chainDiam P ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt chain_diameter_le_width (by simp))
  exact ⟨(orderDiam P).toNat, (chainDiam P).toNat,
    (ENat.natCast_toNat finite_order).symm, (ENat.natCast_toNat finite_chain).symm⟩

theorem many_components_from_examples
    (additive : ∀ (P Q : Type) [Fintype P] [PartialOrder P] [Fintype Q] [PartialOrder Q],
      orderDiam (P ⊕ Q) = orderDiam P + orderDiam Q ∧ chainDiam (P ⊕ Q) = chainDiam P + chainDiam Q)
    (P Q : Type) [Fintype P] [PartialOrder P] [Fintype Q] [PartialOrder Q]
    (order_gap : chainDiam P + 1 ≤ orderDiam P) (chain_gap : orderDiam Q + 1 ≤ chainDiam Q) (M : ℕ) :
    (∃ (T : Type) (_ : Fintype T) (_ : PartialOrder T) (a b : ℕ),
      orderDiam T = a ∧ chainDiam T = b ∧ b + M ≤ a) ∧
    (∃ (T : Type) (_ : Fintype T) (_ : PartialOrder T) (a b : ℕ),
      orderDiam T = a ∧ chainDiam T = b ∧ a + M ≤ b) := by
  constructor
  · obtain ⟨T, finite, ordered, gap⟩ := repeat_order_gap additive P order_gap M
    let : Fintype T := finite
    let : PartialOrder T := ordered
    obtain ⟨a, b, ha, hb⟩ := diameter_values_finite T
    refine ⟨T, finite, ordered, a, b, ha, hb, ?_⟩
    rw [ha, hb] at gap
    exact_mod_cast gap
  · obtain ⟨T, finite, ordered, gap⟩ := repeat_chain_gap additive Q chain_gap M
    let : Fintype T := finite
    let : PartialOrder T := ordered
    obtain ⟨a, b, ha, hb⟩ := diameter_values_finite T
    refine ⟨T, finite, ordered, a, b, ha, hb, ?_⟩
    rw [ha, hb] at gap
    exact_mod_cast gap

end RepeatedSums

end LeeDiam
