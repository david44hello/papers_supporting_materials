/-
LeeDiam/Sec6/Chain.lean — Section 6.3 of paper 004 (short v1.50, sec_reverse.tex l. 191-277): d_C(A, B) = 4 and
diam C(P_n) = 4 (Lemmas 6.8, 6.9, 6.10, Proposition 6.11, Remark 6.12, Theorem 6.13).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Vertices
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Pn
import LeeDiam.Defs.PnSets
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec2.Walks
import LeeDiam.Sec4.BandOrder
import LeeDiam.Sec5.Upper
import LeeDiam.Sec6.Structure
import LeeDiam.Sec6.Order
import LeeDiam.Sec6.ChainHelp
import LeeDiam.Sec6.ChainProp
import LeeDiam.Sec6.Rem612

namespace LeeDiam

open PnSets

theorem lem_6_8_proved (n : ℕ) (_hn : 2 ≤ n) (X : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n)) (hne : X ≠ tgtA n) :
    IsTypeD n X ∨ IsTypeE n X ∨ IsTypeL n X ∨ IsTypeH n X :=
  S6C.lem_6_8 n X hX hne

theorem lem_6_8_B_proved (n : ℕ) (_hn : 2 ≤ n) (Y : Set (Pn n)) (hY : Y ∈ nbhdC (tgtB n)) (hne : Y ≠ tgtB n) :
    IsTypeD' n Y ∨ IsTypeE' n Y ∨ IsTypeL' n Y ∨ IsTypeH' n Y :=
  S6C.lem_6_8_B n Y hY hne

theorem lem_6_9_proved {P : Type} [PartialOrder P] (X Y : Set P) (hX : IsAntichainSet X) (_hY : IsAntichainSet Y)
    (x : P) (hx : x ∈ X \ Y) (hxY : ∀ z ∈ Y, ¬ Comp x z) :
    (∀ g ∈ symmDiff X Y, ¬ Comp g x) ∧ (2 ≤ (symmDiff X Y).encard → ¬ IsConnSet (symmDiff X Y)) :=
  S6C.isolated X Y hX x hx hxY

theorem lem_6_10_proved (n : ℕ) (_hn : 2 ≤ n) :
    (∀ Y : Set (Pn n), (Y = tgtB n ∨ IsTypeD' n Y ∨ IsTypeL' n Y) →
      Y ⊆ lamB n ∧ ∀ z ∈ Y, ∀ u ∈ tgtA n, ¬ Attached z u) ∧
    (∀ z ∈ zB n, (∀ z' ∈ insert z (tgtB n), z' ≠ z → ∀ u ∈ tgtA n, ¬ Attached z' u) ∧
      {u | u ∈ tgtA n ∧ Attached z u}.encard ≤ 2) ∧
    (∀ (j : Fin n) (S : Set (Pn n)), (S = {PnElem.w' j} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ i, x = PnElem.t i j})) →
      ((tgtB n \ {PnElem.b j}) ∪ S) ∩ tgtA n = ∅ ∧
      (∀ z ∈ (tgtB n \ {PnElem.b j}) ∪ S, ∀ u ∈ tgtA n, Comp z u → ∃ p, z = PnElem.t p j ∧ z ∈ S) ∧
      ∀ p : Fin n, ∀ u ∈ tgtA n, Comp (PnElem.t p j : Pn n) u → u = PnElem.a p) :=
  S6C.lem_6_10 n

theorem lem_6_10_swap_proved (n : ℕ) (_hn : 2 ≤ n) :
    (∀ X : Set (Pn n), (X = tgtA n ∨ IsTypeD n X ∨ IsTypeL n X) →
      X ⊆ lamA n ∧ ∀ z ∈ X, ∀ u ∈ tgtB n, ¬ Attached z u) ∧
    (∀ z ∈ zA n, (∀ z' ∈ insert z (tgtA n), z' ≠ z → ∀ u ∈ tgtB n, ¬ Attached z' u) ∧
      {u | u ∈ tgtB n ∧ Attached z u}.encard ≤ 2) ∧
    (∀ (i : Fin n) (S : Set (Pn n)), (S = {PnElem.w i} ∨ (S.Nonempty ∧ S ⊆ {x | ∃ j, x = PnElem.t i j})) →
      ((tgtA n \ {PnElem.a i}) ∪ S) ∩ tgtB n = ∅ ∧
      (∀ z ∈ (tgtA n \ {PnElem.a i}) ∪ S, ∀ u ∈ tgtB n, Comp z u → ∃ q, z = PnElem.t i q ∧ z ∈ S) ∧
      ∀ q : Fin n, ∀ u ∈ tgtB n, Comp (PnElem.t i q : Pn n) u → u = PnElem.b q) :=
  S6C.lem_6_10_swap n

theorem prop_6_11_proved (n : ℕ) (hn : 4 ≤ n) (X Y : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n))
    (hY : Y ∈ nbhdC (tgtB n)) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) ∧ X ≠ Y ∧
      ∀ (hX' : IsAntichainSet X) (hY' : IsAntichainSet Y), 2 ≤ dC X Y hX' hY' :=
  S6C.prop_6_11 n hn X Y hX hY

theorem prop_6_11_n3_proved (n : ℕ) (hn : 3 ≤ n) (X Y : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n))
    (hY : Y ∈ nbhdC (tgtB n)) (hEH : ¬ (IsTypeE n X ∧ IsTypeH' n Y)) (hHE : ¬ (IsTypeH n X ∧ IsTypeE' n Y)) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) :=
  S6C.prop_n3 n hn X Y hX hY hEH hHE

theorem rem_6_12_proved (n : ℕ) (hn : n = 2 ∨ n = 3) :
    (∃ E : Pair n, E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) ∧
    ∀ E : Pair n, E.1 = {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} →
      IsWalkFromTo [tgtA n, (tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j},
          insert (PnElem.m E) (tgtB n), tgtB n] (tgtA n) (tgtB n) ∧
        IsTypeH n ((tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j}) ∧
        (tgtA n \ {PnElem.a ⟨0, by omega⟩}) ∪ {x | ∃ j, x = PnElem.t ⟨0, by omega⟩ j} ∈ nbhdC (tgtA n) ∧
        IsTypeE' n (insert (PnElem.m E) (tgtB n)) ∧ insert (PnElem.m E) (tgtB n) ∈ nbhdC (tgtB n) := by
  exact S6C.rem_6_12 n hn

theorem thm_6_13_walk_proved (n : ℕ) (hn : 2 ≤ n) :
    IsWalkFromTo [tgtA n, pairMinA n, {PnElem.h}, pairMinB n, tgtB n] (tgtA n) (tgtB n) :=
  S6C.walk_6_13 hn

/-- Every set at `d_C ≤ 1` from `X` (both antichains) lies in `N[X]`. -/
theorem mem_nbhdC_of_le {P : Type} [Fintype P] [PartialOrder P] (X Y : Set P) (hX : IsAntichainSet X)
    (hY : IsAntichainSet Y) (h : X = Y ∨ IsConnSet (symmDiff X Y)) : Y ∈ nbhdC X :=
  ⟨hX, hY, S5.dC_le_one X Y hX hY h⟩

theorem tgtA_ne_tgtB (n : ℕ) (hn : 1 ≤ n) : tgtA n ≠ tgtB n := by
  intro h
  have ha : (PnElem.a ⟨0, hn⟩ : Pn n) ∈ tgtA n := ⟨_, rfl⟩
  rw [h] at ha
  obtain ⟨j, hj⟩ := ha
  cases hj

theorem thm_6_13_proved (n : ℕ) (hn : 4 ≤ n) :
    (∀ (hA : IsAntichainSet (tgtA n)) (hB : IsAntichainSet (tgtB n)), dC (tgtA n) (tgtB n) hA hB = 4) ∧
      chainDiam (Pn n) = 4 := by
  obtain ⟨hA, hB, -⟩ := sec6_antichains_proved n
  have hne := tgtA_ne_tgtB n (by omega)
  -- lower bound: no walk of length ≤ 3 from `A` to `B` (Proposition 6.11)
  have hlow : ¬ dC (tgtA n) (tgtB n) hA hB ≤ ((3 : ℕ) : ℕ∞) := by
    intro h3
    obtain ⟨W, ⟨⟨hWne, hWa, hWc⟩, hhead, hlast⟩, hlen⟩ := (dC_le_iff _ _ hA hB 3).1 h3
    rcases W with _ | ⟨V0, _ | ⟨V1, _ | ⟨V2, _ | ⟨V3, _ | ⟨V4, W⟩⟩⟩⟩⟩
    · exact hWne rfl
    · simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at hhead hlast
      exact hne (hhead.symm.trans hlast)
    · simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons, List.getLast?_singleton]
        at hhead hlast
      subst hhead hlast
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hWc
      have hX : tgtB n ∈ nbhdC (tgtA n) := mem_nbhdC_of_le _ _ hA hB (Or.inr hWc)
      have hY : tgtA n ∈ nbhdC (tgtB n) :=
        mem_nbhdC_of_le _ _ hB hA (Or.inr (by rw [symmDiff_comm]; exact hWc))
      have := (prop_6_11_proved n hn _ _ hX hY).2.1
      rw [symmDiff_comm] at this
      exact this hWc
    · simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons, List.getLast?_singleton]
        at hhead hlast
      subst hhead hlast
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hWc
      have h1 : IsAntichainSet V1 := hWa V1 (by simp)
      have hX : V1 ∈ nbhdC (tgtA n) := mem_nbhdC_of_le _ _ hA h1 (Or.inr hWc.1)
      have hY : V1 ∈ nbhdC (tgtB n) :=
        mem_nbhdC_of_le _ _ hB h1 (Or.inr (by rw [symmDiff_comm]; exact hWc.2))
      exact (prop_6_11_proved n hn _ _ hX hY).2.2.1 rfl
    · simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons, List.getLast?_singleton]
        at hhead hlast
      subst hhead hlast
      simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hWc
      have h1 : IsAntichainSet V1 := hWa V1 (by simp)
      have h2 : IsAntichainSet V2 := hWa V2 (by simp)
      have hX : V1 ∈ nbhdC (tgtA n) := mem_nbhdC_of_le _ _ hA h1 (Or.inr hWc.1)
      have hY : V2 ∈ nbhdC (tgtB n) :=
        mem_nbhdC_of_le _ _ hB h2 (Or.inr (by rw [symmDiff_comm]; exact hWc.2.2))
      exact (prop_6_11_proved n hn _ _ hX hY).2.1 hWc.2.1
    · simp at hlen
      omega
  -- upper bound: the walk `A → M_A → {h} → M_B → B`
  have hup : dC (tgtA n) (tgtB n) hA hB ≤ 4 := by
    have := sec2_walk_dist_proved _ _ _ hA hB (thm_6_13_walk_proved n (by omega))
    simpa using this
  have hAB : dC (tgtA n) (tgtB n) hA hB = 4 := by
    refine le_antisymm hup ?_
    have h4 := (ENat.add_one_le_iff (ENat.natCast_ne_top 3)).2 (not_le.1 hlow)
    norm_num at h4
    exact h4
  refine ⟨fun hA' hB' => hAB, le_antisymm ?_ ?_⟩
  · exact thm_1_5_proved _ (le_of_eq (thm_6_7_proved n (by omega)))
  · rw [← hAB, dC_eq, chainDiam_eq]
    exact SimpleGraph.edist_le_ediam

end LeeDiam
