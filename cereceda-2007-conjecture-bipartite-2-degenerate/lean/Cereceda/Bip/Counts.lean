/-
Cereceda/Bip/Counts.lean — Theorem 3.1 helpers: the length bound from the per-vertex move counts, and sorted vertex lists.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Moved from Bip/Main.lean (deleted with the earlier proof route of Theorem 3.1), content unchanged:
`length_le_of_counts` (used by Bip/MainV40.lean and Paper/Statements.lean) and `sorted_all` (used by Bip/MainV40.lean).
-/
import Cereceda.Bip.Basic

namespace Cereceda

open Finset

namespace Bip

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The length bound of Theorem 3.1 from the per-vertex counts. -/
theorem length_le_of_counts (I : Instance W) (ms : List (W × Fin 4)) (h1 : movesOf ms I.sink = 1)
    (h2 : ∀ v, v ≠ I.sink → movesOf ms v ≤ 2) : ms.length ≤ 2 * Fintype.card W - 1 := by
  rw [length_eq_sum_movesOf ms, ← Finset.add_sum_erase _ _ (Finset.mem_univ I.sink), h1]
  have hle : ∑ v ∈ Finset.univ.erase I.sink, movesOf ms v ≤ (Finset.univ.erase I.sink).card • 2 :=
    Finset.sum_le_card_nsmul _ _ _ (fun v hv => h2 v (Finset.ne_of_mem_erase hv))
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, smul_eq_mul] at hle
  have hpos : 0 < Fintype.card W := Fintype.card_pos_iff.2 ⟨I.sink⟩
  omega

omit [DecidableEq W] in
/-- A duplicate-free list of all vertices, sorted by a key (for the orders of Lemma 3.4). -/
theorem sorted_all {κ : W → Fin 4} (le : Fin 4 → Fin 4 → Prop) [DecidableRel le]
    (htrans : ∀ a b c, le a b → le b c → le a c) (htotal : ∀ a b, le a b ∨ le b a) :
    ∃ l : List W, (l.Nodup ∧ ∀ v, v ∈ l) ∧ l.Pairwise (fun u v => le (κ u) (κ v)) := by
  let l := (Finset.univ : Finset W).toList.mergeSort (fun a b => decide (le (κ a) (κ b)))
  have hperm := List.mergeSort_perm (Finset.univ : Finset W).toList (fun a b => decide (le (κ a) (κ b)))
  refine ⟨l, ⟨hperm.nodup_iff.2 (Finset.nodup_toList _), fun v => hperm.mem_iff.2 (by simp)⟩, ?_⟩
  have hp := List.pairwise_mergeSort (le := fun a b => decide (le (κ a) (κ b)))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact htrans _ _ _ hab hbc)
    (fun a b => by simpa using htotal (κ a) (κ b)) (Finset.univ : Finset W).toList
  exact hp.imp fun h => by simpa using h

end Bip

end Cereceda
