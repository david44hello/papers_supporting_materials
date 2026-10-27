/-
HibiLi/Example21/BottomGeometry.lean — zero-one generators after adjoining a bottom element.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.BottomLift

namespace HibiLi

variable {P : Type*} [Fintype P] [PartialOrder P]

theorem bottomDrop_zeroOne {v : WithBot P → ℝ} (hv : v ∈ zeroOneVectors (WithBot P)) :
    bottomDrop v ∈ zeroOneVectors P := fun pp => hv pp

theorem bottomLift_drop_of_bot_zero {v : WithBot P → ℝ} (hv : v ⊥ = 0) :
    bottomLift (bottomDrop v) = v := by
  ext pp
  cases pp using WithBot.recBotCoe with
  | bot => exact hv.symm
  | coe pp => rfl

theorem bottomLift_order_mem {v : P → ℝ} (hv : v ∈ orderPolytope P) :
    bottomLift v ∈ orderPolytope (WithBot P) := by
  constructor
  · intro pp
    cases pp using WithBot.recBotCoe with
    | bot => simp
    | coe pp => exact hv.1 pp
  · intro pp qq hpq
    cases pp using WithBot.recBotCoe with
    | bot =>
      cases qq using WithBot.recBotCoe with
      | bot => rfl
      | coe qq => exact (hv.1 qq).1
    | coe pp =>
      cases qq using WithBot.recBotCoe with
      | bot => simp at hpq
      | coe qq => exact hv.2 pp qq (WithBot.coe_le_coe.mp hpq)

theorem bottomDrop_order_mem {v : WithBot P → ℝ} (hv : v ∈ orderPolytope (WithBot P)) :
    bottomDrop v ∈ orderPolytope P :=
  ⟨fun pp => hv.1 pp, fun pp qq hpq => hv.2 pp qq (WithBot.coe_le_coe.mpr hpq)⟩

theorem bottomLift_chain_mem {v : P → ℝ} (hv : v ∈ chainPolytope P)
    (hz : v ∈ zeroOneVectors P) : bottomLift v ∈ chainPolytope (WithBot P) := by
  apply zeroOne_antichain_mem_chainPolytope (bottomLift_zeroOne hz)
  intro pp hp qq hq hne hle
  cases pp using WithBot.recBotCoe with
  | bot => simp at hp
  | coe pp =>
    cases qq using WithBot.recBotCoe with
    | bot => simp at hq
    | coe qq => exact (support_antichain hv) hp hq (by simpa using hne) (WithBot.coe_le_coe.mp hle)

theorem bottomDrop_chain_mem {v : WithBot P → ℝ} (hv : v ∈ chainPolytope (WithBot P))
    (hz : v ∈ zeroOneVectors (WithBot P)) : bottomDrop v ∈ chainPolytope P := by
  apply zeroOne_antichain_mem_chainPolytope (bottomDrop_zeroOne hz)
  intro pp hp qq hq hne hle
  exact (support_antichain hv) hp hq (by simpa using hne) (WithBot.coe_le_coe.mpr hle)

theorem orderBottomApex_mem : orderBottomApex (P := P) ∈ orderPolytope (WithBot P) :=
  ⟨fun _ => by simp, fun _ _ _ => le_refl 1⟩

theorem orderBottomApex_zeroOne : orderBottomApex (P := P) ∈ zeroOneVectors (WithBot P) :=
  fun _ => Or.inr rfl

theorem chainBottomApex_zeroOne : chainBottomApex (P := P) ∈ zeroOneVectors (WithBot P) := by
  intro pp
  cases pp using WithBot.recBotCoe <;> simp

theorem chainBottomApex_mem : chainBottomApex (P := P) ∈ chainPolytope (WithBot P) := by
  apply zeroOne_antichain_mem_chainPolytope chainBottomApex_zeroOne
  have hs : {pp : WithBot P | chainBottomApex pp = 1} = {⊥} := by
    ext pp
    cases pp using WithBot.recBotCoe <;> simp
  rw [hs]
  exact IsAntichain.singleton

theorem order_eq_apex_of_bot_one {v : WithBot P → ℝ}
    (hv : v ∈ orderPolytope (WithBot P)) (hbot : v ⊥ = 1) : v = orderBottomApex := by
  ext pp
  have hlow := hv.2 ⊥ pp bot_le
  have hhigh := (hv.1 pp).2
  change v pp = 1
  linarith

theorem chain_eq_apex_of_bot_one {v : WithBot P → ℝ}
    (hv : v ∈ chainPolytope (WithBot P)) (hz : v ∈ zeroOneVectors (WithBot P))
    (hbot : v ⊥ = 1) : v = chainBottomApex := by
  ext pp
  cases pp using WithBot.recBotCoe with
  | bot => exact hbot
  | coe pp =>
    rcases hz (pp : WithBot P) with hzero | hone
    · exact hzero
    · have hbad : (⊥ : WithBot P) = (pp : WithBot P) := (support_antichain hv).eq hbot hone bot_le
      simp at hbad

theorem orderZeroOne_withBot :
    orderPolytope (WithBot P) ∩ zeroOneVectors (WithBot P) =
      insert orderBottomApex (bottomLift '' (orderPolytope P ∩ zeroOneVectors P)) := by
  ext v
  constructor
  · rintro ⟨hv, hz⟩
    rcases hz (⊥ : WithBot P) with hzero | hone
    · exact Or.inr ⟨bottomDrop v, ⟨bottomDrop_order_mem hv, bottomDrop_zeroOne hz⟩,
        bottomLift_drop_of_bot_zero hzero⟩
    · exact Or.inl (order_eq_apex_of_bot_one hv hone)
  · rintro (rfl | ⟨v, ⟨hv, hz⟩, rfl⟩)
    · exact ⟨orderBottomApex_mem, orderBottomApex_zeroOne⟩
    · exact ⟨bottomLift_order_mem hv, bottomLift_zeroOne hz⟩

theorem chainZeroOne_withBot :
    chainPolytope (WithBot P) ∩ zeroOneVectors (WithBot P) =
      insert chainBottomApex (bottomLift '' (chainPolytope P ∩ zeroOneVectors P)) := by
  ext v
  constructor
  · rintro ⟨hv, hz⟩
    rcases hz (⊥ : WithBot P) with hzero | hone
    · exact Or.inr ⟨bottomDrop v, ⟨bottomDrop_chain_mem hv hz, bottomDrop_zeroOne hz⟩,
        bottomLift_drop_of_bot_zero hzero⟩
    · exact Or.inl (chain_eq_apex_of_bot_one hv hz hone)
  · rintro (rfl | ⟨v, ⟨hv, hz⟩, rfl⟩)
    · exact ⟨chainBottomApex_mem, chainBottomApex_zeroOne⟩
    · exact ⟨bottomLift_chain_mem hv hz, bottomLift_zeroOne hz⟩

end HibiLi
