/-
HibiLi/Proofs/MaxChainFinset.lean — a finite set is a maximal chain iff its elements are pairwise comparable and every
element comparable with all of them belongs to it (makes "maximal chain" decidable for Example 2.1's counts).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi.Proofs

/-- For a finite set `K` in a partial order: `K` is a maximal chain iff any two of its elements are comparable and every
element comparable with all of `K` lies in `K`. (A helper: it makes "is a maximal chain" decidable for finite `K`.) -/
theorem isMaxChain_finset_iff {α : Type*} [PartialOrder α] (K : Finset α) :
    IsMaxChain (· ≤ ·) (K : Set α) ↔
      (∀ x ∈ K, ∀ y ∈ K, x ≤ y ∨ y ≤ x) ∧ ∀ z, (∀ y ∈ K, z ≤ y ∨ y ≤ z) → z ∈ K := by
  constructor
  · rintro ⟨hchain, hmax⟩
    refine ⟨fun x hx y hy => ?_, fun z hz => ?_⟩
    · rcases eq_or_ne x y with rfl | hne
      · exact Or.inl le_rfl
      · exact hchain hx hy hne
    · have hins : IsChain (· ≤ ·) (insert z (K : Set α)) :=
        hchain.insert fun y hy _ => hz y hy
      have heq := hmax hins (Set.subset_insert z _)
      have : z ∈ insert z (K : Set α) := Set.mem_insert z _
      rw [← heq] at this
      exact this
  · rintro ⟨hcomp, hclosed⟩
    refine ⟨fun x hx y hy _ => hcomp x hx y hy, fun t ht hKt => ?_⟩
    refine Set.Subset.antisymm hKt fun z hz => hclosed z fun y hy => ?_
    rcases eq_or_ne z y with rfl | hne
    · exact Or.inl le_rfl
    · exact ht hz (hKt hy) hne

end HibiLi.Proofs
