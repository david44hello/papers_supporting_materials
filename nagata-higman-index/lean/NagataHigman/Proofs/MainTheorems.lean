/-
NagataHigman/Proofs/MainTheorems.lean — the paper's headline results, for an arbitrary Young system: Remark 2.3
(box empty, Razmyslov's bound), Lemma 3.1, Theorem A, Theorem B (over ℂ, then over every char-0 field), the index facts used by the corollaries.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.Criterion
import NagataHigman.Proofs.Lemma31
import NagataHigman.Proofs.Restriction
import NagataHigman.Proofs.FreeAlgebraLayer
import NagataHigman.Proofs.Shapes
import NagataHigman.Proofs.TwoCorner.Theorem44
import NagataHigman.Proofs.BaseChange

noncomputable section

namespace NagataHigman.Proofs

open Equiv NagataHigman

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
/-- A partition in the `n × n` box has at most `n²` cells. -/
theorem le_sq_of_inBox {N n : ℕ} {lam : Shape N} (h : lam.InBox n) : N ≤ n ^ 2 := by
  have hsum : lam.parts.sum ≤ Multiset.card lam.parts • lam.parts.sup :=
    Multiset.sum_le_card_nsmul _ _ fun x hx => Multiset.le_sup hx
  rw [lam.parts_sum, smul_eq_mul] at hsum
  calc N ≤ Multiset.card lam.parts * lam.parts.sup := hsum
    _ ≤ n * n := Nat.mul_le_mul h.1 h.2
    _ = n ^ 2 := (sq n).symm

omit [CharZero F] in
/-- **Remark 2.3** (l. 357): for `N > n²` no partition of `N` fits in the box, so `B_n^{(N)} = 0`. -/
theorem boxSum_eq_bot_of_lt {N : ℕ} (Y : YoungSystem F N) (n : ℕ) (h : n ^ 2 < N) : Y.boxSum n = ⊥ := by
  unfold YoungSystem.boxSum YoungSystem.blockSum
  refine le_bot_iff.1 (iSup₂_le fun lam hlam => ?_)
  exact absurd (le_sq_of_inBox hlam) (by omega)

/-- **Remark 2.3** (l. 357): Razmyslov's bound `x_1 ⋯ x_{n²} ∈ T` (`n ≥ 1`), via Remark 2.2 at `N = n² + 1`. -/
theorem razmyslov_mem (n : ℕ) (hn : 1 ≤ n) (Y : YoungSystem F (n ^ 2 + 1)) :
    firstLettersProd F (n ^ 2) ∈ TIdeal F n := by
  refine rem_2_2_forward_general n (n ^ 2) hn (by nlinarith) Y ?_
  rw [boxSum_eq_bot_of_lt Y n (by omega)]
  exact inf_bot_eq _

/-- **Lemma 3.1** (tex 363-377) for any Young system on `N = n²` points. -/
theorem lem_3_1_general (n : ℕ) (hn : 2 ≤ n) {N : ℕ} (hN : N = n ^ 2) (Y : YoungSystem F N) :
    cycleSpan F N ⊓ Y.boxSum n = ⊥ := by
  subst hN
  exact lemma_3_1_of hn Y (restriction_of_young Y) (lem_3_1_square_proved n)
    (fun lam hlam T top htop => square_pos_top n (by omega) lam hlam T top htop)

/-- **Theorem A** (tex 130-132, proof l. 363-377): `x_1 ⋯ x_{n²-1} ∈ T` for `n ≥ 2`. -/
theorem thm_A_mem (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1 + 1)) :
    firstLettersProd F (n ^ 2 - 1) ∈ TIdeal F n := by
  have h2n : 2 * n ≤ n ^ 2 := by nlinarith
  exact rem_2_2_forward_general n (n ^ 2 - 1) (by omega) (by omega) Y
    (lem_3_1_general n hn (by omega) Y)

omit [CharZero F] in
/-- `d(n) ≥ k + 1` from `x_1 ⋯ x_k ∉ T`, once some `x_1 ⋯ x_{m₀} ∈ T` (so that `d(n)` is attained). -/
theorem succ_le_nhIndex {n m₀ k : ℕ} (hm₀ : 1 ≤ m₀) (h₀ : firstLettersProd F m₀ ∈ TIdeal F n) (hk : 1 ≤ k)
    (hnot : firstLettersProd F k ∉ TIdeal F n) : k + 1 ≤ nhIndex F n := by
  by_contra hlt
  exact hnot ((nhIndex_le_iff_of_mem F hm₀ h₀ k hk).1 (by omega))

omit [CharZero F] in
/-- The lower bound of Corollaries 3.2 and 4.6: `n(n+1)/2 ≤ d(n)` from `x_1 ⋯ x_{n(n+1)/2-1} ∉ T` (Kuzmin, cited in
`Paper/Statements.lean`) and any upper bound `x_1 ⋯ x_{m₀} ∈ T`. -/
theorem half_le_nhIndex (n : ℕ) (hn : 2 ≤ n) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (h₀ : firstLettersProd F m₀ ∈ TIdeal F n)
    (hK : firstLettersProd F (n * (n + 1) / 2 - 1) ∉ TIdeal F n) : n * (n + 1) / 2 ≤ nhIndex F n := by
  have h6 : 6 ≤ n * (n + 1) := by nlinarith
  have h3 : 3 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have := succ_le_nhIndex hm₀ h₀ (by omega) hK
  omega

/-- Lemma 4.3 with the number of points given as any `N = n² - 1`. -/
theorem thm_4_4_of_eq (n : ℕ) (hn : 3 ≤ n) {N : ℕ} (hN : N = n ^ 2 - 1) (Y : YoungSystem ℂ N)
    (hsplit : AlternatingSplit Y) : cycleSpan ℂ N ⊓ Y.boxSum n = ⊥ := by
  subst hN
  exact thm_4_4_general n hn Y hsplit

/-- **Theorem B over ℂ** (v1.02 tex 466-468): Lemma 4.3 and Remark 2.2 with `m = n² - 2` give `x_1 ⋯ x_{n²-2} ∈ T` over ℂ. -/
theorem thm_B_mem_complex (n : ℕ) (hn : 3 ≤ n) (Y : YoungSystem ℂ (n ^ 2 - 2 + 1)) (hsplit : AlternatingSplit Y) :
    firstLettersProd ℂ (n ^ 2 - 2) ∈ TIdeal ℂ n := by
  have h3n : 3 * n ≤ n ^ 2 := by nlinarith
  exact rem_2_2_forward_general n (n ^ 2 - 2) (by omega) (by omega) Y (thm_4_4_of_eq n hn (by omega) Y hsplit)

omit [CharZero F] in
/-- **Theorem B** (tex 134-136) over every field of characteristic 0: the membership over ℂ transfers (ℂ → ℚ → F,
`BaseChange.lean`). -/
theorem thm_B_mem (F : Type*) [Field F] [CharZero F] (n : ℕ) (hn : 3 ≤ n)
    (Y : YoungSystem ℂ (n ^ 2 - 2 + 1)) (hsplit : AlternatingSplit Y) :
    firstLettersProd F (n ^ 2 - 2) ∈ TIdeal F n :=
  mem_TIdeal_of_complex n (n ^ 2 - 2) (by omega) F (thm_B_mem_complex n hn Y hsplit)

end NagataHigman.Proofs
