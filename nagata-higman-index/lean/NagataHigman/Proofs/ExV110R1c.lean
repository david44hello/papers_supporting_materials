/-
NagataHigman/Proofs/ExV110R1c.lean — project 011 v1.10 FINAL, coverage review r1: SHOULD-2 (the Kuzmin sentence of
Section 1, v1.10 l. 124-125: the word's degree, the endomorphism, the reduction; `kuzminWord` is the word, used in the
statements of those rows) and SHOULD-4 (step (6) of Proposition 2.1, v1.10 l. 367: "By steps (2), (3) and (5), P(I) is
spanned by such sums"). The rows are in Paper/Statements.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now. Paper v1.10.
-/
import NagataHigman.Proofs.ExV110

universe u

noncomputable section

/-! ## The Kuzmin word -/

namespace NagataHigman

/-- Kuzmin's word `x_2 x_1 x_2 x_1^2 ⋯ x_2 x_1^{n-1}` (v1.10 l. 124) as a list of letters: the blocks
`x_2 x_1^{i+1}`, `i = 0, …, n-2`. The paper's letters `x_2`, `x_1` are Lean's `1`, `0`. -/
def kuzminWord (n : ℕ) : List ℕ := ((List.range (n - 1)).map fun i => 1 :: List.replicate (i + 1) 0).flatten

end NagataHigman

/-! ## Proofs -/

namespace NagataHigman.Proofs.ExV110R1c

open NagataHigman Equiv Finset

/-- The first `k` blocks of Kuzmin's word have total length `∑_{i<k} (i + 2)`, i.e. twice it plus `2` is
`(k + 1)(k + 2)`. -/
theorem kuzmin_length_aux (k : ℕ) :
    2 * (((List.range k).map fun i => 1 :: List.replicate (i + 1) 0).flatten).length + 2 = (k + 1) * (k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, List.length_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_cons, List.length_replicate]
    linarith

/-- v1.10 l. 124: Kuzmin's word has degree `n(n+1)/2 - 1`. -/
theorem kuzmin_degree_proved (n : ℕ) (hn : 1 ≤ n) : (kuzminWord n).length = n * (n + 1) / 2 - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have h : 2 * (kuzminWord (k + 1)).length + 2 = (k + 1) * (k + 1 + 1) := by
    unfold kuzminWord
    rw [Nat.add_sub_cancel]
    exact kuzmin_length_aux k
  generalize (k + 1) * (k + 1 + 1) = P at h ⊢
  omega

variable (F : Type*) [Field F]

/-- v1.10 l. 125: the endomorphism `x_i ↦ (i-th letter of Kuzmin's word)` maps `x_1 ⋯ x_{n(n+1)/2-1}` onto the word. -/
theorem kuzmin_endo_proved (n : ℕ) (hn : 2 ≤ n) :
    ∃ φ : FreeNUAlg F →ₙₐ[F] FreeNUAlg F,
      φ (firstLettersProd F (n * (n + 1) / 2 - 1)) = wordOf F (kuzminWord n) := by
  refine ⟨freeLift F (fun i => if hi : i < (kuzminWord n).length then
    letter F ((kuzminWord n).get ⟨i, hi⟩) else 0), ?_⟩
  rw [← kuzmin_degree_proved n (by omega), firstLettersProd, map_tupleProd, wordOf]
  simp [freeLift_letter]

/-- v1.10 l. 125: if Kuzmin's word is not in `T`, neither is `x_1 ⋯ x_{n(n+1)/2-1}` (T-ideals are closed under
endomorphisms). -/
theorem kuzmin_reduction_proved (n : ℕ) (hn : 2 ≤ n) (hK : wordOf F (kuzminWord n) ∉ TIdeal F n) :
    firstLettersProd F (n * (n + 1) / 2 - 1) ∉ TIdeal F n := by
  intro h
  obtain ⟨φ, hφ⟩ := kuzmin_endo_proved F n hn
  exact hK (hφ ▸ (isTIdeal_TIdeal F n).endo φ _ h)

open Classical in
/-- v1.10 l. 367: by steps (2), (3) and (5), `P(I)` is spanned by the sums `∑_{π ∈ Π} τπ` (`τ` an `N`-cycle,
`|X| = n + 1`). -/
theorem step6_PI_span_proved (n m : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) :
    (altIdeal F (m + 1) n).map (cycleProj F (m + 1)) = Submodule.span F
      {x | ∃ (τ : Perm (Fin (m + 1))) (X : Finset (Fin (m + 1))), IsFullCycle τ ∧ X.card = n + 1 ∧
        x = ∑ π ∈ univ.filter (fun π : Perm (Fin (m + 1)) => π.support ⊆ X ∧ IsFullCycle (τ * π)), perm F (τ * π)} := by
  rw [altIdeal_eq_span F (by omega : n + 1 ≤ m + 1), Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨τ, X, hX, rfl⟩, rfl⟩
    by_cases h : ∃ π : Perm (Fin (m + 1)), π.support ⊆ X ∧ IsFullCycle (τ * π)
    · obtain ⟨π₀, -, h₀, heq⟩ := prop21_step3_reduce (F := F) τ X h
      rw [heq, map_smul, prop21_step5_sum h₀ X]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨τ * π₀, X, h₀, hX, rfl⟩)
    · push_neg at h
      rw [prop21_step3_zero (F := F) τ X h]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨τ, X, hτ, hX, rfl⟩
    exact Submodule.subset_span ⟨perm F τ * altSum F X, ⟨τ, X, hX, rfl⟩, prop21_step5_sum hτ X⟩

end NagataHigman.Proofs.ExV110R1c

end
