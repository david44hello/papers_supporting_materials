/-
NagataHigman/Proofs/NonVacuity.lean — the box block sums of Lemma 3.1 and Lemma 4.3 are single NONZERO blocks:
B_n^{(n²)} = I_{(n^n)} ≠ 0 and B_n^{(n²-1)} = I_ν ≠ 0, for every Young system.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.TwoCorner.Section4
import NagataHigman.Proofs.BoxExists

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

variable {F : Type*} [Field F] [CharZero F]

/-- A block of a Young system is never zero: it contains an element acting as the identity on `S^λ`. -/
theorem block_ne_bot {N : ℕ} (Y : YoungSystem F N) (lam : Shape N) : Y.block lam ≠ ⊥ := by
  obtain ⟨a, ha, hρ⟩ := YoungSystem.exists_mem_block Y lam 1
  intro hbot
  rw [hbot, Submodule.mem_bot] at ha
  subst ha
  have hpos : 0 < Y.dim lam := Nat.pos_of_ne_zero fun h => dim_ne_zero Y lam (by simp [h])
  have h01 := congrFun (congrFun hρ ⟨0, hpos⟩) ⟨0, hpos⟩
  simp at h01

omit [CharZero F] in
/-- If the only shape in `S` is `lam`, the block sum over `S` is the block `I_λ`. -/
theorem blockSum_eq_block {N : ℕ} (Y : YoungSystem F N) {S : Set (Shape N)} {lam : Shape N} (hS : S = {lam}) :
    Y.blockSum S = Y.block lam := by
  subst hS
  unfold YoungSystem.blockSum
  simp

omit [CharZero F] in
/-- **Lemma 3.1, setting** (l. 363-368): `B_n^{(n²)} = I_{(n^n)}`, the block of the square. -/
theorem boxSum_sq_eq_block (n : ℕ) (Y : YoungSystem F (n ^ 2)) (lam : Shape (n ^ 2)) (hlam : lam.InBox n) :
    Y.boxSum n = Y.block lam := by
  unfold YoungSystem.boxSum
  refine blockSum_eq_block Y (Set.ext fun mu => ⟨fun hmu => ?_, fun hmu => ?_⟩)
  · exact Set.mem_singleton_iff.2
      (Nat.Partition.ext (by rw [lem_3_1_square_proved n mu hmu, lem_3_1_square_proved n lam hlam]))
  · rw [Set.mem_singleton_iff.1 hmu]; exact hlam

/-- `B_n^{(n²)} ≠ 0`: Lemma 3.1 is not vacuous. -/
theorem boxSum_sq_ne_bot (n : ℕ) (Y : YoungSystem F (n ^ 2)) : Y.boxSum n ≠ ⊥ := by
  obtain ⟨lam, hlam⟩ := lem_3_1_square_exists_proved n
  rw [boxSum_sq_eq_block n Y lam hlam]
  exact block_ne_bot Y lam

omit [CharZero F] in
/-- **Section 4.1** (v1.02 l. 341-346): `B_n^{(n²-1)} = I_ν` for `n ≥ 2`. -/
theorem boxSum_nu_eq_block (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) : Y.boxSum n = Y.block lam := by
  unfold YoungSystem.boxSum
  refine blockSum_eq_block Y (Set.ext fun mu => ⟨fun hmu => ?_, fun hmu => ?_⟩)
  · exact Set.mem_singleton_iff.2
      (Nat.Partition.ext (by rw [sec_4_1_nu_proved n hn mu hmu, sec_4_1_nu_proved n hn lam hlam]))
  · rw [Set.mem_singleton_iff.1 hmu]; exact hlam

/-- `B_n^{(n²-1)} ≠ 0` (`n ≥ 2`): Lemma 4.3 is not vacuous. -/
theorem boxSum_nu_ne_bot (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) : Y.boxSum n ≠ ⊥ := by
  obtain ⟨lam, hlam⟩ := sec_4_1_nu_exists_proved n hn
  rw [boxSum_nu_eq_block n hn Y lam hlam]
  exact block_ne_bot Y lam

end NagataHigman.Proofs
