/-
HibiLi/Proofs/SmallClaims.lean — proofs of four small in-text claims of the paper: the induced copy of `X` (paper v2.10
lines 95–97), `dim B = n − 1` (lines 309–310), `λ_a(ζ₀) = λ_b(ζ₀) = 0` (lines 738–743), and "We cannot always take
`q = c`" (lines 681–684, on the poset `a, b < c < d < g, h`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.ExtraDefs
import HibiLi.Proofs.SwitchFacts
import HibiLi.Proofs.Lemma46
import HibiLi.Polytope.Dimension
import HibiLi.Polytope.SwitchDomains

namespace HibiLi.Proofs

open HibiLi

/-- Lines 95–97: the five elements of an `X`-copy carry an order embedding of `X`. -/
theorem sec1_X_copy_induced_proved {P : Type*} [PartialOrder P] {a b c g h : P} (hX : IsXCopy a b c g h) :
    ∃ f : XElem ↪o P, f XElem.a = a ∧ f XElem.b = b ∧ f XElem.c = c ∧ f XElem.g = g ∧ f XElem.h = h := by
  obtain ⟨hac, hbc, hcg, hch, hab, hba, hgh, hhg⟩ := hX
  let f : XElem → P := fun
    | .a => a | .b => b | .c => c | .g => g | .h => h
  have key : ∀ x y : XElem, f x ≤ f y ↔ x ≤ y := by
    intro x y
    cases x <;> cases y
    all_goals first
      | exact iff_of_true (by dsimp only [f]; order) (by decide)
      | exact iff_of_false (by dsimp only [f]; order) (by decide)
  exact ⟨OrderEmbedding.ofMapLEIff f key, rfl, rfl, rfl, rfl, rfl⟩

/-- Lines 309–310: `B = O_I(P′)` is a polytope of dimension `n − 1`. -/
theorem sec3_B_dim_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    IsPolytope s.B ∧ adim s.B + 1 = Fintype.card P := by
  refine ⟨s.B_isPolytope, ?_⟩
  have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨s.q⟩
  rw [Switch.B, chainOrderPolytope_adim, card_P' s]
  omega

/-- Lines 738–743: every form of the `a`- and `b`-families vanishes at `ζ₀`, so `λ_a(ζ₀) = λ_b(ζ₀) = 0`. -/
theorem sec4_lam_u0_proved {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    x.lamA x.u0 = 0 ∧ x.lamB x.u0 = 0 :=
  ⟨(Lemma46.familyA x).at_u0, (Lemma46.familyB x).at_u0⟩

namespace SmallClaims

/-- `<` on `XdElem` is decidable (from the decidable `≤`), so `decide` settles finite order facts. -/
local instance : DecidableLT XdElem := decidableLTOfDecidableLE

/-- Above `d` sit exactly the incomparable `g, h`. -/
lemma not_chain_Ioi_d : ¬ IsChain (· ≤ ·) (Set.Ioi XdElem.d) := by
  intro hch
  rcases hch (x := XdElem.g) (y := XdElem.h) (by decide) (by decide) (by decide) with h | h <;> revert h <;> decide

/-- Above `g` or `h` there is nothing. -/
lemma chain_Ioi_above_d : ∀ r : XdElem, XdElem.d < r → IsChain (· ≤ ·) (Set.Ioi r) := by
  intro r hr
  have hempty : Set.Ioi r = ∅ := by
    ext z
    simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
    revert r z
    decide
  rw [hempty]
  exact IsChain.empty

/-- The switch of Section 4 on `XdElem`: the copy `a, b < c < g, h`, `q = d`, `g' = g`, `h' = h`. -/
def xd : XSwitch XdElem where
  a := XdElem.a
  b := XdElem.b
  c := XdElem.c
  g := XdElem.g
  h := XdElem.h
  isX := by unfold IsXCopy; decide
  q := XdElem.d
  c_le_q := by decide
  q_not_chain := not_chain_Ioi_d
  q_max := chain_Ioi_above_d
  g' := XdElem.g
  h' := XdElem.h
  q_covby_g' := by unfold CovBy; decide
  q_covby_h' := by unfold CovBy; decide
  g'_ne_h' := by decide
  g'_h'_incomp := by decide

lemma c_lt_d : XdElem.c < XdElem.d := by decide

end SmallClaims

/-- Lines 681–684: in `a, b < c < d < g, h` the elements `a, b, c, g, h` form a copy of `X`, a switch of Section 4
exists (with `q = d`), and none uses `q = c` (above `c` sits `d`, whose strict upper set `{g, h}` is not a chain). -/
theorem sec4_q_c_remark_proved :
    IsXCopy XdElem.a XdElem.b XdElem.c XdElem.g XdElem.h ∧ Nonempty (XSwitch XdElem) ∧
      ∀ x : XSwitch XdElem, x.q ≠ XdElem.c := by
  refine ⟨SmallClaims.xd.isX, ⟨SmallClaims.xd⟩, fun x hq => ?_⟩
  exact SmallClaims.not_chain_Ioi_d (x.q_max XdElem.d (hq ▸ SmallClaims.c_lt_d))

end HibiLi.Proofs
