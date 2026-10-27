/-
HibiLi/Proofs/SwitchFacts.lean — small facts about one switch used to assemble Theorem 4.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi.Proofs

open HibiLi Polynomial Finset

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- The `k`-th coefficient of `δ_E` is `δ_{E,k}` for `k ≤ |P'|`, and `0` above. -/
lemma delta_coeff (E : Set (s.P' → ℝ)) (k : ℕ) :
    (s.delta E).coeff k = if k ≤ Fintype.card s.P' then s.deltaCoeff E k else 0 := by
  unfold Switch.delta
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- `I ∪ {q}` is again an order ideal (Fourier §3: "In particular, I ∪ {q} is again an order ideal"). -/
lemma insert_isLowerSet : IsLowerSet (insert s.q s.I) := by
  intro x y hyx hx
  rcases hx with rfl | hx
  · rcases hyx.lt_or_eq with hlt | heq
    · exact Or.inr (s.q_minimal y hlt)
    · exact Or.inl heq
  · exact Or.inr (s.isLowerSet hyx hx)

/-- The ideal `I` seen inside `P'` is an order ideal of `P'`. -/
lemma I'_isLowerSet : IsLowerSet s.I' := fun _ _ hba ha => s.isLowerSet (show _ ≤ _ from hba) ha

/-- `|P'| = |P| − 1`. -/
lemma card_P' : Fintype.card s.P' = Fintype.card P - 1 := by
  classical
  have : Fintype.card s.P' = Fintype.card {p : P // p ≠ s.q} := Fintype.card_congr (Equiv.refl _)
  rw [this]
  simp [Fintype.card_subtype_compl]

end HibiLi.Proofs
