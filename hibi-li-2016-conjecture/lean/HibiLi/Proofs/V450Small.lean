/-
HibiLi/Proofs/V450Small.lean — three small claims new in paper v4.50 and v4.60: the caption of Figure 1 (the poset
P_7, v4.60 l. 108), the values of the two terms of the maximum and of the minimum at the point w of the proof of
Lemma 4.6 (v4.60 l. 689-692), and "for n ≤ 4 no poset contains X" (caption of Figure 2, v4.60).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.SharpFamily
import HibiLi.Defs.PaperDefs
import HibiLi.Proofs.AddV170

namespace HibiLi.Proofs.V450

open HibiLi

/-- Figure 1's caption (v4.60 l. 108): `P_7 = sharpFamily 2` is `X` with a new least element adjoined two times in
succession (`WithBot (WithBot X)`); it has 7 elements, contains `X`, and attains the bound of Theorem 4.1:
`F_C(P_7) − F_O(P_7) = t²(1+t)⁴` (Proposition 5.2 at `n = 7`). -/
theorem fig1_P7_proved :
    sharpFamily 2 = WithBot (WithBot XElem) ∧
    Fintype.card (sharpFamily 2) = 7 ∧ ContainsX (sharpFamily 2) ∧
    facePoly (chainPolytope (sharpFamily 2)) - facePoly (orderPolytope (sharpFamily 2)) = gapPoly 7 :=
  ⟨rfl, prop_5_2_proved 2⟩

/-- The point `w = w(ζ₁)` of the proof of Lemma 4.6 (v4.60 l. 689-692): if `w` has `α = 1/4 + ε/2`, `β = 1/4 − ε/2`
with `ε = λ_b − λ_a`, and `γ = η = 3/4`, then "the two terms of the maximum in Lemma 4.5(b) are both equal to
`1/4 + (λ_a + λ_b)/2`, and the two terms of the minimum are both equal to `3/4`". -/
theorem lemma_4_6_point_values_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)
    (w : x.toSwitch.P' → ℝ) (hα : w x.pa = 1 / 4 + (x.lamB w - x.lamA w) / 2)
    (hβ : w x.pb = 1 / 4 - (x.lamB w - x.lamA w) / 2) (hγ : w x.pg = 3 / 4) (hη : w x.ph = 3 / 4) :
    w x.pa + x.lamA w = 1 / 4 + (x.lamA w + x.lamB w) / 2 ∧
      w x.pb + x.lamB w = 1 / 4 + (x.lamA w + x.lamB w) / 2 ∧
      w x.pg = 3 / 4 ∧ w x.ph = 3 / 4 := by
  refine ⟨?_, ?_, hγ, hη⟩
  · rw [hα]; ring
  · rw [hβ]; ring

/-- Figure 2's caption (v4.60; the figure file `fig_before_after.tex`, input at l. 146): "for `n ≤ 4` no poset contains
`X`".  A poset that contains `X` has an order embedding of `X`, which has five elements, so it has at least five
elements. -/
theorem fig_beforeafter_no_X_proved (P : Type*) [Fintype P] [PartialOrder P] (hP : Fintype.card P ≤ 4) :
    ¬ ContainsX P := by
  intro hX
  obtain ⟨f⟩ := (HibiLi.Proofs.AddV170.containsX_iff_embedding_proved P).1 hX
  have hcard : Fintype.card XElem = 5 := by decide
  have hle := Fintype.card_le_of_embedding f.toEmbedding
  omega

end HibiLi.Proofs.V450
