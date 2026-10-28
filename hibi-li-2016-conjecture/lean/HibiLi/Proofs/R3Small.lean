/-
HibiLi/Proofs/R3Small.lean — three in-text claims of the paper found unstated by the fresh review r3 (findings F3,
F4, F5): L = max(α, β) and U = min(γ, η) on B for P = X; c has no two upper covers in XdElem; the upper covers g′, h′
of q need not be g, h.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.ExtraDefs
import HibiLi.Defs.R3Witness
import HibiLi.Proofs.Lemma44
import HibiLi.Example21.CenterSwitch

namespace HibiLi.Proofs

open Finset

local instance : DecidableLT XElem := decidableLTOfDecidableLE
local instance : DecidableLT XdElem := decidableLTOfDecidableLE
local instance : DecidableLT R3Elem := decidableLTOfDecidableLE

namespace R3Small

section OnE0

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

/-- `(some γ)` is a branch of `U`: `g' > q`. -/
lemma some_pg_mem : (some x.pg) ∈ x.toSwitch.upBranches := by
  simp only [Switch.upBranches, mem_insert, reduceCtorEq, mem_image, mem_filter, mem_univ, true_and,
    Option.some.injEq, exists_eq_right, false_or]
  exact x.q_covby_g'.lt

/-- `(some η)` is a branch of `U`: `h' > q`. -/
lemma some_ph_mem : (some x.ph) ∈ x.toSwitch.upBranches := by
  simp only [Switch.upBranches, mem_insert, reduceCtorEq, mem_image, mem_filter, mem_univ, true_and,
    Option.some.injEq, exists_eq_right, false_or]
  exact x.q_covby_h'.lt

/-- On `E₀`, `L = max(α, β)`: a branch `K` of `L` meets at most one of the incomparable `a, b`, and `ζ₀` vanishes on
the other chain coordinates; the branches `{a}`, `{b}` give the reverse bound. -/
lemma L_eq_max_on_E0 {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) : x.toSwitch.L u = max (u x.pa) (u x.pb) := by
  have hsys := Lemma44.E0_subset x (pa := x.pa) (pb := x.pb) (pg := x.pg) (ph := x.ph) rfl rfl rfl rfl hu
  unfold Switch.L
  apply le_antisymm
  · apply Finset.sup'_le
    intro K hK
    simp only [Switch.lowBranches, mem_filter, mem_univ, true_and] at hK
    exact Lemma44.chainSum_le_max x rfl rfl hu.2.1 hsys.1 hK.1 hK.2.1
  · apply max_le
    · simpa only [Switch.chainSum, sum_singleton] using
        le_sup' (x.toSwitch.chainSum · u) x.singleton_pa_mem
    · simpa only [Switch.chainSum, sum_singleton] using
        le_sup' (x.toSwitch.chainSum · u) x.singleton_pb_mem

/-- On `E₀`, `U = min(γ, η)`: the other order coordinates equal `1` there, and `γ, η ≤ 1`. -/
lemma U_eq_min_on_E0 {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.E0) : x.toSwitch.U u = min (u x.pg) (u x.ph) := by
  have hsys := Lemma44.E0_subset x (pa := x.pa) (pb := x.pb) (pg := x.pg) (ph := x.ph) rfl rfl rfl rfl hu
  have hmin1 : min (u x.pg) (u x.ph) ≤ 1 := (min_le_left _ _).trans hsys.2.2.2.1
  apply le_antisymm
  · exact le_min (inf'_le (x.toSwitch.upVal · u) (some_pg_mem x))
      (inf'_le (x.toSwitch.upVal · u) (some_ph_mem x))
  · apply le_inf'
    intro j hj
    simp only [Switch.upBranches, mem_insert, mem_image, mem_filter, mem_univ, true_and] at hj
    rcases hj with rfl | ⟨r, hr, rfl⟩
    · exact hmin1
    · by_cases h1 : r.1 = x.g'
      · obtain rfl : r = x.pg := Subtype.ext h1
        exact min_le_left _ _
      by_cases h2 : r.1 = x.h'
      · obtain rfl : r = x.ph := Subtype.ext h2
        exact min_le_right _ _
      have hrI : r.1 ∉ x.toSwitch.I := fun h => h hr.le
      show min (u x.pg) (u x.ph) ≤ u r
      rw [hu.2.2 r hrI h1 h2]
      exact hmin1

end OnE0

section XFacts


/-- In `X`, the middle element of a copy of `X` is `c`. -/
lemma X_c_eq (x : XSwitch XElem) : x.c = XElem.c := by
  have center : ∀ p₁ p₂ p₃ : XElem, p₁ < p₂ → p₂ < p₃ → p₂ = XElem.c := by decide
  exact center x.a x.c x.g x.isX.1 x.isX.2.2.1

/-- In `X`, two distinct elements below `c` are `a, b`. -/
lemma X_pair_below (p₁ p₂ : XElem) (h₁ : p₁ < XElem.c) (h₂ : p₂ < XElem.c) (hne : p₁ ≠ p₂) :
    ({p₁, p₂} : Set XElem) = {XElem.a, XElem.b} := by
  have key : ∀ p₁ p₂ : XElem, p₁ < XElem.c → p₂ < XElem.c → p₁ ≠ p₂ →
      (p₁ = XElem.a ∧ p₂ = XElem.b) ∨ (p₁ = XElem.b ∧ p₂ = XElem.a) := by decide
  rcases key p₁ p₂ h₁ h₂ hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Set.pair_comm _ _

/-- In `X`, two distinct elements above `c` are `g, h`. -/
lemma X_pair_above (r₁ r₂ : XElem) (h₁ : XElem.c < r₁) (h₂ : XElem.c < r₂) (hne : r₁ ≠ r₂) :
    ({r₁, r₂} : Set XElem) = {XElem.g, XElem.h} := by
  have key : ∀ r₁ r₂ : XElem, XElem.c < r₁ → XElem.c < r₂ → r₁ ≠ r₂ →
      (r₁ = XElem.g ∧ r₂ = XElem.h) ∨ (r₁ = XElem.h ∧ r₂ = XElem.g) := by decide
  rcases key r₁ r₂ h₁ h₂ hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Set.pair_comm _ _

end XFacts

section XdFacts


/-- In `XdElem`, the only upper cover of `c` is `d`. -/
lemma Xd_covBy_c (y : XdElem) (hy : XdElem.c ⋖ y) : y = XdElem.d := by
  have key : ∀ y : XdElem, XdElem.c ⋖ y → y = XdElem.d := by unfold CovBy; decide
  exact key y hy

end XdFacts

section R3Facts


/-- `IsChain` of a strict upper set, unfolded to a decidable statement. -/
lemma R3_isChain_Ioi_iff (q : R3Elem) :
    IsChain (· ≤ ·) (Set.Ioi q) ↔ ∀ y, q < y → ∀ z, q < z → y ≠ z → y ≤ z ∨ z ≤ y := Iff.rfl

/-- The witness switch for paper line 706: the copy `a, b, c, g, h'` of `X`, `q = d`, and its upper covers
`g', h'`. -/
def r3Switch : XSwitch R3Elem where
  a := .a
  b := .b
  c := .c
  g := .g
  h := .hp
  isX := by unfold IsXCopy; decide
  q := .d
  c_le_q := by decide
  q_not_chain := by rw [R3_isChain_Ioi_iff]; decide
  q_max := by simp only [R3_isChain_Ioi_iff]; decide
  g' := .gp
  h' := .hp
  q_covby_g' := by unfold CovBy; decide
  q_covby_h' := by unfold CovBy; decide
  g'_ne_h' := by decide
  g'_h'_incomp := by decide

/-- For the copy `a, b, c, g, h'`, every element `q` allowed by Section 4.2 (the hypotheses of Lemma 4.3) is `d`. -/
lemma R3_q_eq_d (q : R3Elem) (hcq : R3Elem.c ≤ q) (hq : ¬ IsChain (· ≤ ·) (Set.Ioi q))
    (hmax : ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) : q = R3Elem.d := by
  simp only [R3_isChain_Ioi_iff] at hq hmax
  revert q
  decide

/-- The upper covers of `d` are `g', h'`. -/
lemma R3_covBy_d (y : R3Elem) (hy : R3Elem.d ⋖ y) : y = R3Elem.gp ∨ y = R3Elem.hp := by
  have key : ∀ y : R3Elem, R3Elem.d ⋖ y → y = R3Elem.gp ∨ y = R3Elem.hp := by unfold CovBy; decide
  exact key y hy

/-- Two upper covers of `d` never form the pair `{g, h'}`: `g` is not an upper cover of `d` (`d < g' < g`). -/
lemma R3_pair_ne (g' h' : R3Elem) (hg : R3Elem.d ⋖ g') (hh : R3Elem.d ⋖ h') :
    ({g', h'} : Set R3Elem) ≠ {R3Elem.g, R3Elem.hp} := by
  intro heq
  have hmem : R3Elem.g ∈ ({g', h'} : Set R3Elem) := by rw [heq]; exact Or.inl rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases R3_covBy_d g' hg with rfl | rfl <;> rcases R3_covBy_d h' hh with rfl | rfl <;> simp at hmem

end R3Facts

end R3Small

open R3Small

/-- Paper v2.10 lines 657–661 (Figure 2 caption: "for `P = X` … `L = max(α, β)`, `U = min(γ, η)`") and lines 905–907
(proof of Proposition 5.1: "When `c` is switched, `I = {a, b}` and `J' = {g, h}` … with `L = max(α, β)` and
`U = min(γ, η)`"): for every switch of Section 4.2 in `X`, `q = c`, `I = {a, b}`, `J' = J \ {q} = {g, h}`, the
coordinates `α, β` are those of `a, b` and `γ, η` those of `g, h`, and on all of `B` the two functions are
`L = max(α, β)` and `U = min(γ, η)`. -/
theorem prop_5_1_X_LU_proved : ∀ x : XSwitch XElem,
    x.q = XElem.c ∧ x.toSwitch.I = {XElem.a, XElem.b} ∧ x.toSwitch.Iᶜ \ {x.q} = {XElem.g, XElem.h} ∧
      ({x.a, x.b} : Set XElem) = {XElem.a, XElem.b} ∧ ({x.g', x.h'} : Set XElem) = {XElem.g, XElem.h} ∧
      ∀ u ∈ x.toSwitch.B, x.toSwitch.L u = max (u x.pa) (u x.pb) ∧ x.toSwitch.U u = min (u x.pg) (u x.ph) := by
  intro x
  have hq : x.q = XElem.c := Example21.CenterSwitch.q_eq_c x
  have hc : x.c = XElem.c := X_c_eq x
  refine ⟨hq, ?_, ?_, ?_, ?_, fun u hu => ?_⟩
  · change (Set.Ici x.q)ᶜ = _
    rw [hq]
    ext p
    simp only [Set.mem_compl_iff, Set.mem_Ici, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert p
    decide
  · change (Set.Ici x.q)ᶜᶜ \ {x.q} = _
    rw [hq, compl_compl]
    ext p
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_insert_iff, Set.mem_singleton_iff]
    revert p
    decide
  · exact X_pair_below x.a x.b (hc ▸ x.isX.1) (hc ▸ x.isX.2.1) (Lemma44.a_ne_b x)
  · exact X_pair_above x.g' x.h' (hq ▸ x.q_covby_g'.lt) (hq ▸ x.q_covby_h'.lt) x.g'_ne_h'
  · rw [← Example21.CenterSwitch.E0_eq_B x] at hu
    exact ⟨L_eq_max_on_E0 x hu, U_eq_min_on_E0 x hu⟩

/-- Paper v2.10 lines 679–684, the reason behind "We cannot always take `q = c`: the construction of `E₀` below needs
two incomparable upper covers of `q`, and `c` may have only one": in `a, b < c < d < g, h` (`XdElem`, whose
`a, b, c, g, h` form a copy of `X`), `c` is among the elements `m ≥ c` with a strict upper set that is not a chain, yet
`c` has no two distinct upper covers (its only one is `d`), so `E₀` cannot be built with `q = c`. -/
theorem sec4_q_c_no_two_covers_proved :
    ¬ IsChain (· ≤ ·) (Set.Ioi XdElem.c) ∧
      ¬ ∃ g' h' : XdElem, XdElem.c ⋖ g' ∧ XdElem.c ⋖ h' ∧ g' ≠ h' := by
  refine ⟨fun hch => ?_, ?_⟩
  · rcases hch (x := XdElem.g) (y := XdElem.h) (show XdElem.c < XdElem.g by decide)
      (show XdElem.c < XdElem.h by decide) (by decide) with hle | hle <;> revert hle <;> decide
  · rintro ⟨g', h', hg, hh, hne⟩
    exact hne ((Xd_covBy_c g' hg).trans (Xd_covBy_c h' hh).symm)

/-- Paper v2.10 line 706, "Fix two upper covers `g′` and `h′` of `q`; they need not be `g` and `h`", in a strong form.
In `a, b < c < d < g', h'`, `g' < g` (`R3Elem`), the elements `a, b, c, g, h'` form a copy of `X`; a switch of Section
4.2 for this copy exists with `q > c` and `{g', h'} ≠ {g, h}`; and the difference is forced: every `q` satisfying the
hypotheses of Lemma 4.3 for this copy has `q > c`, and no two distinct upper covers of such a `q` form the pair
`{g, h'}`. -/
theorem sec4_covers_may_differ_proved :
    IsXCopy R3Elem.a R3Elem.b R3Elem.c R3Elem.g R3Elem.hp ∧
    (∃ x : XSwitch R3Elem, x.a = R3Elem.a ∧ x.b = R3Elem.b ∧ x.c = R3Elem.c ∧ x.g = R3Elem.g ∧
      x.h = R3Elem.hp ∧ x.c < x.q ∧ ({x.g', x.h'} : Set R3Elem) ≠ {x.g, x.h}) ∧
    ∀ q : R3Elem, R3Elem.c ≤ q → ¬ IsChain (· ≤ ·) (Set.Ioi q) →
      (∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) →
        R3Elem.c < q ∧ ∀ g' h' : R3Elem, q ⋖ g' → q ⋖ h' → g' ≠ h' →
          ({g', h'} : Set R3Elem) ≠ {R3Elem.g, R3Elem.hp} := by
  refine ⟨r3Switch.isX, ⟨r3Switch, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩, fun q hcq hq hmax => ?_⟩
  · show R3Elem.c < R3Elem.d
    decide
  · exact R3_pair_ne _ _ r3Switch.q_covby_g' r3Switch.q_covby_h'
  · obtain rfl := R3_q_eq_d q hcq hq hmax
    exact ⟨by decide, fun g' h' hg hh _ => R3_pair_ne g' h' hg hh⟩

/-- Paper v2.10 line 706 in the bare existential form: some poset containing `X` has a switch of Section 4.2 with
`q > c` whose upper covers `g', h'` differ (as a pair) from `g, h`. -/
theorem sec4_covers_may_differ_exists_proved :
    ∃ (P : Type) (_ : Fintype P) (_ : PartialOrder P) (x : XSwitch P),
      x.c < x.q ∧ ({x.g', x.h'} : Set P) ≠ {x.g, x.h} := by
  obtain ⟨-, ⟨x, -, -, -, -, -, hlt, hne⟩, -⟩ := sec4_covers_may_differ_proved
  exact ⟨R3Elem, inferInstance, inferInstance, x, hlt, hne⟩

end HibiLi.Proofs
