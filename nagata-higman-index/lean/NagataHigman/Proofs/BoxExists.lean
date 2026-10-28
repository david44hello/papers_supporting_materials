/-
NagataHigman/Proofs/BoxExists.lean — the existence halves of Lemma 3.1 and Section 4.1: the box `(n^n)` holds a shape
of `n²` (the square), and for `n ≥ 2` a shape of `n² - 1` (`ν = (n^{n-1}, n-1)`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Uniqueness ("the ONLY partition in the box") is proved in Shapes.lean; these are the witnesses, so the claims about
the square and about `ν` are not vacuous. `n = 0` is allowed for the square (the empty partition of 0).
-/
import Mathlib
import NagataHigman.Defs.Young

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

/-- The square `(n^n)` as a shape of `n²`. -/
def squareShape (n : ℕ) : Shape (n ^ 2) where
  parts := Multiset.replicate n n
  parts_pos := fun {i} hi => by
    obtain ⟨hn, rfl⟩ := Multiset.mem_replicate.1 hi
    exact Nat.pos_of_ne_zero hn
  parts_sum := by
    rw [Multiset.sum_replicate, smul_eq_mul, sq]

/-- `ν = (n^{n-1}, n-1)` as a shape of `n² - 1` (`n ≥ 2`). -/
def nuShape (n : ℕ) (hn : 2 ≤ n) : Shape (n ^ 2 - 1) where
  parts := Multiset.replicate (n - 1) n + {n - 1}
  parts_pos := fun {i} hi => by
    rcases Multiset.mem_add.1 hi with h | h
    · rw [(Multiset.mem_replicate.1 h).2]
      omega
    · rw [Multiset.mem_singleton.1 h]
      omega
  parts_sum := by
    rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton, smul_eq_mul]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (k + 1) ^ 2 = k * (k + 1) + k + 1 by ring]
    omega

/-- **Lemma 3.1, existence half**: the square `(n^n)` lies in the box. -/
theorem lem_3_1_square_exists_proved (n : ℕ) : ∃ lam : Shape (n ^ 2), lam.InBox n := by
  refine ⟨squareShape n, ?_, ?_⟩
  · simp [Shape.numRows, squareShape]
  · exact Multiset.sup_le.2 fun p hp => ((Multiset.mem_replicate.1 hp).2).le

/-- **Section 4.1, existence half**: `ν = (n^{n-1}, n-1)` lies in the box (`n ≥ 2`). -/
theorem sec_4_1_nu_exists_proved (n : ℕ) (hn : 2 ≤ n) : ∃ lam : Shape (n ^ 2 - 1), lam.InBox n := by
  refine ⟨nuShape n hn, ?_, ?_⟩
  · simp only [Shape.numRows, nuShape, Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
    omega
  · refine Multiset.sup_le.2 fun p hp => ?_
    rcases Multiset.mem_add.1 hp with h | h
    · exact ((Multiset.mem_replicate.1 h).2).le
    · rw [Multiset.mem_singleton.1 h]
      omega

end NagataHigman.Proofs

end
