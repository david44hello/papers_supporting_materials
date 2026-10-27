/-
HibiLi/Example21/SharpFamily.lean — Proposition 5.2, the sharpness family in all dimensions.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.BottomPyramid
import HibiLi.Example21.Result

namespace HibiLi

open Polynomial

theorem ContainsX.withBot {P : Type*} [Fintype P] [PartialOrder P] (hX : ContainsX P) :
    ContainsX (WithBot P) := by
  obtain ⟨aa, bb, cc, gg, hh, hrelations⟩ := hX
  refine ⟨(aa : WithBot P), (bb : WithBot P), (cc : WithBot P),
    (gg : WithBot P), (hh : WithBot P), ?_⟩
  simpa using hrelations

theorem sharpFamily_card (mm : ℕ) : Fintype.card (sharpFamily mm) = mm + 5 := by
  induction mm with
  | zero => change Fintype.card XElem = 5; decide
  | succ mm ih =>
    change Fintype.card (Option (sharpFamily mm)) = mm + 1 + 5
    rw [Fintype.card_option, ih]

theorem sharpFamily_containsX (mm : ℕ) : ContainsX (sharpFamily mm) := by
  induction mm with
  | zero =>
    change ContainsX XElem
    exact ⟨XElem.a, XElem.b, XElem.c, XElem.g, XElem.h, by
      simp only [lt_iff_le_not_ge]
      decide⟩
  | succ mm ih =>
    change ContainsX (WithBot (sharpFamily mm))
    exact ih.withBot

theorem facePoly_gap_X :
    facePoly (chainPolytope XElem) - facePoly (orderPolytope XElem) = gapPoly 5 := by
  have hcard : Fintype.card XElem = 5 := by decide
  have horder (kk : ℕ) := (ex_2_1_proved kk).1
  have hchain (kk : ℕ) := (ex_2_1_proved kk).2
  norm_num [facePoly, facePolyUpTo, hcard, horder, hchain, Finset.sum_range_succ, gapPoly]
  ring

theorem sharpFamily_gap (mm : ℕ) :
    facePoly (chainPolytope (sharpFamily mm)) - facePoly (orderPolytope (sharpFamily mm)) =
      gapPoly (mm + 5) := by
  induction mm with
  | zero => exact facePoly_gap_X
  | succ mm ih =>
    change facePoly (chainPolytope (WithBot (sharpFamily mm))) -
      facePoly (orderPolytope (WithBot (sharpFamily mm))) = gapPoly (mm + 1 + 5)
    rw [facePoly_gap_withBot, ih]
    unfold gapPoly
    rw [show mm + 1 + 5 - 3 = (mm + 5 - 3) + 1 by omega, pow_succ]
    ring

theorem prop_5_2_proved (m : ℕ) :
    Fintype.card (sharpFamily m) = m + 5 ∧ ContainsX (sharpFamily m) ∧
    facePoly (chainPolytope (sharpFamily m)) - facePoly (orderPolytope (sharpFamily m)) =
      gapPoly (m + 5) :=
  ⟨sharpFamily_card m, sharpFamily_containsX m, sharpFamily_gap m⟩

end HibiLi
