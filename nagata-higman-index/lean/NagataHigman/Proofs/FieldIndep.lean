/-
NagataHigman/Proofs/FieldIndep.lean — (F1), last sentence: dim W_{n,m}, and hence d(n), is the same for every field of
characteristic zero (the spanning elements have integer coefficients).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Proofs.FieldStep

noncomputable section

namespace NagataHigman.Proofs.FieldIndep

open NagataHigman NagataHigman.Proofs

/-- `x_1 ⋯ x_m ∈ T` iff `dim W_{n,m} = m!` (`W_{n,m} ⊆ V_m` and `dim V_m = m!`). -/
theorem mem_TIdeal_iff_finrank (K : Type*) [Field K] [CharZero K] (n m : ℕ) (hm : 1 ≤ m) :
    firstLettersProd K m ∈ TIdeal K n ↔ Module.finrank K (multilinIdentities K n m) = m.factorial := by
  rw [F0_mem_iff_proved K n m hm]
  have hle : multilinIdentities K n m ≤ multilinSpace K m := inf_le_left
  have : FiniteDimensional K (multilinSpace K m) := FiniteDimensional.span_of_finite K (Set.finite_range _)
  constructor
  · intro h
    rw [h, finrank_multilinSpace hm]
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_multilinSpace hm, h]

/-- **(F1), last sentence**: for any two fields `F`, `K` of characteristic `0`, `dim_F W_{n,m} = dim_K W_{n,m}` for
every `m ≥ 1`, and `d_F(n) = d_K(n)`. -/
theorem field_indep (F K : Type*) [Field F] [CharZero F] [Field K] [CharZero K] (n : ℕ) (hn : 1 ≤ n) :
    (∀ m, 1 ≤ m → Module.finrank F (multilinIdentities F n m) = Module.finrank K (multilinIdentities K n m)) ∧
      nhIndex F n = nhIndex K n := by
  have hdim : ∀ m, 1 ≤ m →
      Module.finrank F (multilinIdentities F n m) = Module.finrank K (multilinIdentities K n m) := fun m hm => by
    rw [FieldStep.finrank_multilinIdentities_eq_rat F n m hn hm,
      FieldStep.finrank_multilinIdentities_eq_rat K n m hn hm]
  refine ⟨hdim, ?_⟩
  have hset : {m | 1 ≤ m ∧ firstLettersProd F m ∈ TIdeal F n} = {m | 1 ≤ m ∧ firstLettersProd K m ∈ TIdeal K n} := by
    ext m
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨hm, (mem_TIdeal_iff_finrank K n m hm).mpr
        ((hdim m hm).symm.trans ((mem_TIdeal_iff_finrank F n m hm).mp h))⟩
    · rintro ⟨hm, h⟩
      exact ⟨hm, (mem_TIdeal_iff_finrank F n m hm).mpr
        ((hdim m hm).trans ((mem_TIdeal_iff_finrank K n m hm).mp h))⟩
  unfold nhIndex
  rw [hset]

end NagataHigman.Proofs.FieldIndep

end
