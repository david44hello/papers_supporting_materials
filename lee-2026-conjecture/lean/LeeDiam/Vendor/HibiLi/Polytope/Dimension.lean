/-
HibiLiLean — full dimension of chain-order polytopes.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Polytope.ChainOrder

namespace HibiLi

private theorem open_forall {E κ : Type*} [TopologicalSpace E] [Finite κ]
    {predicate : κ → E → Prop} (opened : ∀ index, IsOpen {point | predicate index point}) :
    IsOpen {point | ∀ index, predicate index point} := by
  simpa only [Set.iInter_ofPred] using isOpen_iInter_of_finite opened

private theorem open_imp {E : Type*} [TopologicalSpace E] (condition : Prop)
    {predicate : E → Prop} (opened : IsOpen {point | predicate point}) :
    IsOpen {point | condition → predicate point} := by
  by_cases holds : condition <;> simp_all

theorem chainOrderPolytope_adim (P : Type*) [Fintype P] [PartialOrder P] (ideal : Set P) :
    adim (chainOrderPolytope P ideal) = Fintype.card P := by
  classical
  let rank : P → ℕ := fun coord => (Finset.univ.filter (fun lower : P => lower ≤ coord)).card
  let epsilon : ℝ := 1 / (4 * ((Fintype.card P : ℝ) + 1))
  have card_nonneg : 0 ≤ (Fintype.card P : ℝ) := Nat.cast_nonneg _
  have positive : 0 < epsilon := by dsimp [epsilon]; positivity
  have epsilon_bound : epsilon * ((Fintype.card P : ℝ) + 1) = 1 / 4 := by
    dsimp [epsilon]
    field_simp
  have rank_bound (coord : P) : rank coord ≤ Fintype.card P :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have rank_strict {lower upper : P} (relation : lower < upper) : rank lower < rank upper := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro coord member
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
      exact member.trans relation.le
    · intro same
      have member : upper ∈ Finset.univ.filter (fun coord : P => coord ≤ upper) := by simp
      rw [← same] at member
      exact relation.not_ge (Finset.mem_filter.mp member).2
  let center : P → ℝ := fun coord =>
    if coord ∈ ideal then epsilon else 1 / 2 + epsilon * ((rank coord : ℝ) + 1)
  let region : Set (P → ℝ) :=
    {point | (∀ coord ∈ ideal, 0 < point coord) ∧
      (∀ coord ∉ ideal, 1 / 2 < point coord ∧ point coord < 1) ∧
      (∀ lower upper, lower ∉ ideal → upper ∉ ideal → lower < upper → point lower < point upper) ∧
      (∀ chain : Finset P, (↑chain ⊆ ideal) → ∑ coord ∈ chain, point coord < 1 / 2)}
  have center_mem : center ∈ region := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro coord member
      simpa [center, member] using positive
    · intro coord outside
      simp only [center, ite_eq_right outside]
      have lower_rank : 0 ≤ (rank coord : ℝ) := Nat.cast_nonneg _
      have upper_rank : (rank coord : ℝ) ≤ Fintype.card P := by exact_mod_cast rank_bound coord
      constructor <;> nlinarith
    · intro lower upper lower_out upper_out relation
      simp only [center, ite_eq_right lower_out, ite_eq_right upper_out]
      have strict : (rank lower : ℝ) < rank upper := by exact_mod_cast rank_strict relation
      nlinarith
    · intro chain inside
      have sum_eq : ∑ coord ∈ chain, center coord = (chain.card : ℝ) * epsilon := by
        calc
          ∑ coord ∈ chain, center coord = ∑ _coord ∈ chain, epsilon :=
            Finset.sum_congr rfl (fun coord member => by simp [center, inside member])
          _ = _ := by simp
      rw [sum_eq]
      have card_bound : (chain.card : ℝ) ≤ Fintype.card P := by exact_mod_cast Finset.card_le_univ chain
      nlinarith
  have region_open : IsOpen region := by
    refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
    · apply open_forall
      intro coord
      apply open_imp
      exact isOpen_lt continuous_const (continuous_apply coord)
    · apply open_forall
      intro coord
      apply open_imp
      exact (isOpen_lt continuous_const (continuous_apply coord)).inter
        (isOpen_lt (continuous_apply coord) continuous_const)
    · apply open_forall
      intro lower
      apply open_forall
      intro upper
      apply open_imp
      apply open_imp
      apply open_imp
      exact isOpen_lt (continuous_apply lower) (continuous_apply upper)
    · apply open_forall
      intro chain
      apply open_imp
      exact isOpen_lt (by fun_prop) continuous_const
  have inside : region ⊆ chainOrderPolytope P ideal := by
    intro point member
    refine ⟨fun coord hc => (member.1 coord hc).le, ?_, ?_, ?_, ?_⟩
    · intro coord outside
      obtain ⟨lower, upper⟩ := member.2.1 coord outside
      exact ⟨by linarith, upper.le⟩
    · intro lower upper lower_out upper_out relation
      rcases relation.eq_or_lt with same | strict
      · simp [same]
      · exact (member.2.2.1 lower upper lower_out upper_out strict).le
    · intro upper outside chain contained _ _
      exact (member.2.2.2 chain contained).le.trans (member.2.1 upper outside).1.le
    · intro chain contained _
      have bound := member.2.2.2 chain contained
      linarith
  have span_top : affineSpan ℝ (chainOrderPolytope P ideal) = ⊤ := by
    apply top_unique
    rw [← region_open.affineSpan_eq_top ⟨center, center_mem⟩]
    exact affineSpan_mono ℝ inside
  unfold adim
  rw [← direction_affineSpan, span_top, AffineSubspace.direction_top]
  simp

theorem sec3_dim_proved (P : Type*) [Fintype P] [PartialOrder P] (I : Set P)
    (_hI : IsLowerSet I) :
    IsPolytope (chainOrderPolytope P I) ∧ adim (chainOrderPolytope P I) = Fintype.card P :=
  ⟨chainOrderPolytope_isPolytope P I, chainOrderPolytope_adim P I⟩

end HibiLi
