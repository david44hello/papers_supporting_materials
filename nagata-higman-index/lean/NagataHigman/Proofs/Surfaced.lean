/-
NagataHigman/Proofs/Surfaced.lean — small named sub-claims of the paper that were proved inside larger proofs, restated
in the paper's words so they can be listed as claims.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.Tableaux
import NagataHigman.Proofs.Shapes

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

/-- Paper v1.02 l. 396-397: `ν` has two removable corners, `A = (n-1, n)` of content `+1` and `B = (n, n-1)` of content `-1`
(1-indexed); in every standard tableau the largest entry sits at one of them (0-indexed cells below). -/
theorem nu_top_corner (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n) (T : SYT lam)
    (top : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) :
    (T.pos top = (n - 2, n - 1) ∧ T.content top = 1) ∨ (T.pos top = (n - 1, n - 2) ∧ T.content top = -1) := by
  have hparts := sec_4_1_nu_proved n hn lam hlam
  rcases nu_pos_top n hn lam hparts T top htop with h | h
  · refine Or.inl ⟨h, ?_⟩
    unfold SYT.content; rw [h]; dsimp only; omega
  · refine Or.inr ⟨h, ?_⟩
    unfold SYT.content; rw [h]; dsimp only; omega

end NagataHigman.Proofs
