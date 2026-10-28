/-
NagataHigman/Proofs/Criterion.lean — Proposition 2.1, the forward direction used by Theorems A and B (Remark 2.2):
`C_N ∩ B_n = 0 ⇒ x_1 ⋯ x_m ∈ T`, for an arbitrary Young system.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper step (7), forward half: if `x_1 ⋯ x_m ∉ W_{n,m}`, a linear functional `φ` kills `W_{n,m}` but not `x_1 ⋯ x_m`.
Its cycle vector `f = Σ_w φ(x_w) Φ(w) ∈ C_N` is orthogonal to `I` (forward half of step (6)), so `f ∈ I^⊥ ⊆ A`, so
`f ∈ C_N ∩ A ⊆ C_N ∩ B_n = 0` (sign twist); but `f(Φ(x_1 ⋯ x_m)) = φ(x_1 ⋯ x_m) ≠ 0`.
-/
import NagataHigman.Proofs.WordSide
import NagataHigman.Proofs.AltIdeal

noncomputable section

namespace NagataHigman.Proofs

open Equiv NagataHigman

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem multilinWord_one (m : ℕ) : multilinWord F (1 : Perm (Fin m)) = firstLettersProd F m := rfl

/-- **Remark 2.2 = Proposition 2.1, forward direction** (v1.02 tex 266-299): for `1 ≤ n ≤ m`, `N = m + 1` and any Young
system, `C_N ∩ B_n = 0` implies `x_1 ⋯ x_m ∈ T`. -/
theorem rem_2_2_forward_general (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (Y : YoungSystem F (m + 1))
    (h : cycleSpan F (m + 1) ⊓ Y.boxSum n = ⊥) : firstLettersProd F m ∈ TIdeal F n := by
  by_contra hnot
  have hx : firstLettersProd F m ∉ multilinIdentities F n m := fun hmem => hnot hmem.2
  obtain ⟨φ, hφx, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hφ : ∀ p ∈ multilinIdentities F n m, φ p = 0 := by
    intro p hp
    have hmap := Submodule.mem_map_of_mem (f := φ) hp
    rw [hφW, Submodule.mem_bot] at hmap
    exact hmap
  have hC : cycleElem F m φ ∈ cycleSpan F (m + 1) := cycleElem_mem_cycleSpan m (le_trans hn hnm) φ
  have hA : cycleElem F m φ ∈ Y.rowSum n :=
    YoungSystem.mem_rowSum_of_perp_altIdeal Y n (by omega) _ (cycleElem_perp_altIdeal n m hn hnm φ hφ)
  have hB : cycleElem F m φ ∈ cycleSpan F (m + 1) ⊓ Y.boxSum n :=
    ⟨hC, YoungSystem.cycleSpan_inf_rowSum_le_boxSum Y n ⟨hC, hA⟩⟩
  rw [h, Submodule.mem_bot] at hB
  apply hφx
  rw [← multilinWord_one, ← coeff_cycleElem m φ 1, hB]
  simp

end NagataHigman.Proofs
