/-
NagataHigman/Proofs/F1Span.lean — package B2, item G10: the spanning statement of (F1) as one equality.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.02, lines 175-179:
"The T-ideal (L)^T is spanned by the elements p·L(h_1,…,h_n)·q, where p, q are monomials or 1 and the h_i have no
constant term. … By multilinearity the h_i may be taken to be monomials." In the non-unital free algebra `FreeNUAlg F`
no element has a constant term, so "h_i without constant term" = any `h i : FreeNUAlg F`. A monomial `p` is a word
`wordOf F a` with `a ≠ []`; "p = 1" is `a = []` (then `sandwich` omits that side). `T = (x^n)^T = (L)^T` in
characteristic 0 is (F1)'s first sentence (`F1_TIdeal_eq_proved`).
-/
import Mathlib
import NagataHigman.Proofs.PropExact

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv

variable (F : Type*) [Field F]

/-- `p · L(h_1, …, h_n) · q ∈ T` for words (or absent) `p`, `q` and ANY `h_i`. -/
theorem sandwich_symSum_mem_TIdeal (n : ℕ) (hn : 1 ≤ n) (a b : List ℕ) (h : Fin n → FreeNUAlg F) :
    sandwich F a b (symSum n h) ∈ TIdeal F n := by
  unfold sandwich
  dsimp only
  by_cases ha : a = [] <;> by_cases hb : b = []
  · rw [ite_eq_left hb, ite_eq_left ha]
    exact F1_symSum_mem_proved F n hn _
  · rw [ite_eq_right hb, ite_eq_left ha]
    exact symSum_mul_mem F n hn _ _
  · rw [ite_eq_left hb, ite_eq_right ha]
    exact mul_symSum_mem F n hn _ _
  · rw [ite_eq_right hb, ite_eq_right ha]
    exact mul_symSum_mul_mem F n hn _ _ _

/-- **(F1), v1.02 line 179** ("the `h_i` may be taken to be monomials"): `T` is spanned by the `a · L(v_1, …, v_n) · b`
with nonempty words `v_i` and words-or-absent `a`, `b`. -/
theorem F1_TIdeal_eq_sandwichSpan [CharZero F] (n : ℕ) (hn : 1 ≤ n) :
    TIdeal F n = Submodule.span F
      {p | ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ), (∀ i, v i ≠ []) ∧ p = sandwichElem F a v b} := by
  refine le_antisymm (PropExact.TIdeal_le_sandwichSpan n hn) (Submodule.span_le.mpr ?_)
  rintro _ ⟨a, v, b, -, rfl⟩
  exact sandwichElem_mem_TIdeal F n hn a v b

/-- **(F1), lines 221-222**: `T = (L)^T` is spanned by the `p · L(h_1, …, h_n) · q` with `p`, `q` monomials or `1`
and ANY `h_i` (in the non-unital algebra every element has no constant term). -/
theorem F1_TIdeal_eq_span [CharZero F] (n : ℕ) (hn : 1 ≤ n) :
    TIdeal F n = Submodule.span F
      {p | ∃ (a : List ℕ) (h : Fin n → FreeNUAlg F) (b : List ℕ), p = sandwich F a b (symSum n h)} := by
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · rw [F1_TIdeal_eq_sandwichSpan F n hn]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, v, b, -, rfl⟩
    exact ⟨a, fun i => wordOf F (v i), b, rfl⟩
  · rintro _ ⟨a, h, b, rfl⟩
    exact sandwich_symSum_mem_TIdeal F n hn a b h

end NagataHigman.Proofs

end
