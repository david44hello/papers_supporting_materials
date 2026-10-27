/-
HibiLi — the center switch in Proposition 5.1.
-/
import HibiLi.Example21.OtherSwitches
import HibiLi.Proofs.Lemma44
import HibiLi.Proofs.SwitchFacts

namespace HibiLi.Example21.CenterSwitch

open Finset Polynomial

local instance : DecidableLT XElem := decidableLTOfDecidableLE

lemma not_chain_Ioi_c : ¬ IsChain (· ≤ ·) (Set.Ioi XElem.c) := by
  intro chain
  rcases chain (x := XElem.g) (y := XElem.h) (by decide) (by decide) (by decide) with h | h <;>
    revert h <;> decide

lemma chain_Ioi_above_c : ∀ r : XElem, XElem.c < r → IsChain (· ≤ ·) (Set.Ioi r) := by
  intro r hr
  have empty : Set.Ioi r = ∅ := by
    ext z
    simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
    revert r z
    decide
  rw [empty]
  exact IsChain.empty

def canonical : XSwitch XElem where
  a := .a
  b := .b
  c := .c
  g := .g
  h := .h
  isX := by unfold IsXCopy; decide
  q := .c
  c_le_q := le_rfl
  q_not_chain := not_chain_Ioi_c
  q_max := chain_Ioi_above_c
  g' := .g
  h' := .h
  q_covby_g' := by unfold CovBy; decide
  q_covby_h' := by unfold CovBy; decide
  g'_ne_h' := by decide
  g'_h'_incomp := by decide

theorem q_eq_c (x : XSwitch XElem) : x.q = XElem.c := by
  have center : ∀ a c g : XElem, a < c → c < g → c = XElem.c := by decide
  have hc : x.c = XElem.c := center x.a x.c x.g x.isX.1 x.isX.2.2.1
  have middle : ∀ q g : XElem, XElem.c ≤ q → q < g → q = XElem.c := by decide
  exact middle x.q x.g' (hc ▸ x.c_le_q) x.q_covby_g'.lt

theorem E0_eq_B (x : XSwitch XElem) : x.E0 = x.toSwitch.B := by
  obtain ⟨face, dim, _⟩ := Proofs.lemma_4_4_proved x x.pa x.pb x.pg x.ph rfl rfl rfl rfl
  apply face.eq_of_adim_eq
  rw [dim, Switch.B, chainOrderPolytope_adim, Proofs.card_P']
  rfl

theorem switch_eq_canonical (x : XSwitch XElem) : x.toSwitch = canonical.toSwitch := by
  have hq := q_eq_c x
  unfold XSwitch.toSwitch
  simp only [hq]
  rfl

theorem exists_and_base : Nonempty (XSwitch XElem) ∧
    ∀ x : XSwitch XElem, x.q = XElem.c ∧ x.E0 = x.toSwitch.B :=
  ⟨⟨canonical⟩, fun x => ⟨q_eq_c x, E0_eq_B x⟩⟩

end HibiLi.Example21.CenterSwitch
