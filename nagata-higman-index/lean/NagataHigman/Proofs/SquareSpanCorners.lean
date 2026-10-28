/-
NagataHigman/Proofs/SquareSpanCorners.lean — two sentences of the paper's proofs as claims: Lemma 3.1's "the ρ(σ),
σ ∈ S_{N-1}, span End(S^β)" on the square (tex 370-372), and "ν has two removable corners, and each holds the top
entry of some standard tableau" (v1.02 tex 396).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Span: Restriction.restriction_of_young says span ρ(S_{N-1}) is the commutant of ρ(J_top); on the square every
tableau has `top` in the corner `(n-1, n-1)`, of content 0, so ρ(J_top) = 0 and the commutant is everything.
Corners: the column-reading tableau of `ν` ends at `A = (n-2, n-1)`, the row-reading one at `B = (n-1, n-2)`
(each is the last cell of its reading order, Tableaux.keyEnum_eq_of_card).
-/
import NagataHigman.Proofs.Lemma31
import NagataHigman.Proofs.Restriction
import NagataHigman.Proofs.Shapes

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F]

/-- **Lemma 3.1, span step** (tex 370-372): on the square, the `ρ(σ)` with `σ` fixing the last point span all of
`End(S^β)`. -/
theorem lem_3_1_span_proved [CharZero F] (n : ℕ) (hn : 1 ≤ n) (Y : YoungSystem F (n ^ 2)) (lam : Shape (n ^ 2))
    (hlam : lam.InBox n) (last : Fin (n ^ 2)) (hlast : (last : ℕ) + 1 = n ^ 2) :
    Submodule.span F (Set.range fun σ : {σ : Perm (Fin (n ^ 2)) // σ last = last} => Y.rho lam σ.1) = ⊤ := by
  have hsq := lem_3_1_square_proved n lam hlam
  have hJ : Y.rhoAlg lam (jucysMurphy F last) = 0 :=
    YoungSystem.rhoAlg_jucysMurphy_eq_zero Y lam last fun T => by
      simp [SYT.content, square_pos_top n hn lam hsq T last hlast]
  have hset : ((Y.rho lam : Perm (Fin (n ^ 2)) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab last) =
      Set.range fun σ : {σ : Perm (Fin (n ^ 2)) // σ last = last} => Y.rho lam σ.1 := by
    ext M
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, hσ⟩, rfl⟩
    · rintro ⟨⟨σ, hσ⟩, rfl⟩
      exact ⟨σ, hσ, rfl⟩
  rw [eq_top_iff]
  rintro X -
  rw [← hset, restriction_of_young Y lam last hlast X, hJ, Matrix.mul_zero, Matrix.zero_mul]

/-- In a finite linear order, the largest element has all the others below it. -/
private theorem card_filter_lt_of_max {α : Type*} [LinearOrder α] {s : Finset α} {x : α} (hx : x ∈ s)
    (hmax : ∀ y ∈ s, y ≤ x) : (s.filter (· < x)).card = s.card - 1 := by
  have h : s.filter (· < x) = s.erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hy, hlt⟩
      exact ⟨ne_of_lt hlt, hy⟩
    · rintro ⟨hne, hy⟩
      exact ⟨hy, lt_of_le_of_ne (hmax y hy) hne⟩
  rw [h, Finset.card_erase_of_mem hx]

/-- The tableau filling the cells in `key` order ends at the `key`-largest cell. -/
private theorem sytOfKey_pos_top {N : ℕ} {lam : Shape N} (key : ℕ × ℕ ≃ ℕ ×ₗ ℕ)
    (hmono : ∀ a b : ℕ × ℕ, a.1 ≤ b.1 → a.2 ≤ b.2 → key a ≤ key b) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    {c : ℕ × ℕ} (hc : c ∈ lam.diagram.cells) (hmax : ∀ d ∈ lam.diagram.cells, key d ≤ key c) :
    (sytOfKey lam key hmono).pos top = c := by
  have hmem : key c ∈ keyCells lam key := Finset.mem_map.2 ⟨c, hc, rfl⟩
  have hk : ((keyCells lam key).filter (· < key c)).card = top := by
    rw [card_filter_lt_of_max hmem, card_keyCells]
    · omega
    · intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_map.1 hy
      exact hmax d hd
  show key.symm (keyEnum lam key top) = c
  rw [keyEnum_eq_of_card lam key hmem top hk, Equiv.symm_apply_apply]

/-- **ν has two removable corners** (v1.02 tex 396): some standard tableau of `ν` has its top entry at `A = (n-2, n-1)`, and
some has it at `B = (n-1, n-2)`. -/
theorem nu_two_corners_exist_proved (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n)
    (top : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) :
    (∃ T : SYT lam, T.pos top = (n - 2, n - 1)) ∧ ∃ T : SYT lam, T.pos top = (n - 1, n - 2) := by
  have hparts := sec_4_1_nu_proved n hn lam hlam
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 2 = m := by omega
  have e2 : m + 2 - 1 = m + 1 := by omega
  rw [e2] at hparts
  rw [e1, e2]
  have hmem := nu_mem (lam := lam) m hparts
  refine ⟨⟨sytOfKey lam colKey colKey_mono, ?_⟩, ⟨sytOfKey lam toLex rowKey_mono, ?_⟩⟩
  · refine sytOfKey_pos_top colKey colKey_mono top htop ((hmem m (m + 1)).2 (Or.inl ⟨by omega, by omega⟩)) ?_
    rintro ⟨i, j⟩ hd
    have := (hmem i j).1 hd
    simp only [colKey, Equiv.trans_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.Lex.toLex_le_toLex]
    omega
  · refine sytOfKey_pos_top toLex rowKey_mono top htop ((hmem (m + 1) m).2 (Or.inr ⟨rfl, by omega⟩)) ?_
    rintro ⟨i, j⟩ hd
    have := (hmem i j).1 hd
    simp only [Prod.Lex.toLex_le_toLex]
    omega

end NagataHigman.Proofs

end
