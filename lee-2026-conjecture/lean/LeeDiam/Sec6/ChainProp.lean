/-
LeeDiam/Sec6/ChainProp.lean — Section 6.3 of paper 004 (short v1.50, sec_reverse.tex l. 218-258): Lemma 6.9 (isolated
elements) and Proposition 6.11 (for `X ∈ N[A]`, `Y ∈ N[B]`, the set `X △ Y` is nonempty and disconnected), with the
`n ≥ 3` version outside Case 4.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Sec6.ChainNbr

namespace LeeDiam.S6C

open PnSets PnOrder

/-- Lemma 6.9 (Isolated elements). -/
theorem isolated {P : Type} [PartialOrder P] (X Y : Set P) (hX : IsAntichainSet X) (x : P) (hx : x ∈ X \ Y)
    (hxY : ∀ z ∈ Y, ¬ Comp x z) :
    (∀ g ∈ symmDiff X Y, ¬ Comp g x) ∧ (2 ≤ (symmDiff X Y).encard → ¬ IsConnSet (symmDiff X Y)) := by
  have hiso : ∀ g ∈ symmDiff X Y, ¬ Comp g x := by
    intro g hg hgx
    rcases hg with ⟨hgX, -⟩ | ⟨hgY, -⟩
    · by_cases hgx' : g = x
      · subst hgx'
        rcases hgx with h | h <;> exact lt_irrefl _ h
      · exact not_comp_of_anti hX hgX hx.1 hgx' hgx
    · exact hxY g hgY (Or.symm hgx)
  refine ⟨hiso, fun h2 hconn => ?_⟩
  have hxG : x ∈ symmDiff X Y := Or.inl hx
  obtain ⟨g, hg, hgx⟩ := Set.exists_ne_of_one_lt_encard (lt_of_lt_of_le (by norm_num) h2) x
  obtain ⟨v, hv, -, hc⟩ := exists_comp_of_conn hconn hxG hg hgx
  exact hiso v hv (Or.symm hc)

variable {n : ℕ}

/-- An isolated element and a second element of `X △ Y`: the set is nonempty and disconnected. -/
theorem not_conn_of_isolated {X Y : Set (Pn n)} (hX : IsAntichainSet X) {x : Pn n} (hx : x ∈ X \ Y)
    (hxY : ∀ z ∈ Y, ¬ Comp x z) {g : Pn n} (hg : g ∈ symmDiff X Y) (hgx : g ≠ x) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  have hxG : x ∈ symmDiff X Y := Set.mem_symmDiff.2 (Or.inl hx)
  refine ⟨⟨x, hxG⟩, (isolated X Y hX x hx hxY).2 ?_⟩
  have hsub : ({x, g} : Set (Pn n)) ⊆ symmDiff X Y := by
    rintro z (rfl | rfl)
    exacts [hxG, hg]
  exact (Set.encard_pair (Ne.symm hgx)).symm.le.trans (Set.encard_le_encard hsub)

/-- The same with the isolated element in `Y \ X`. -/
theorem not_conn_of_isolated' {X Y : Set (Pn n)} (hY : IsAntichainSet Y) {y : Pn n} (hy : y ∈ Y \ X)
    (hyX : ∀ z ∈ X, ¬ Comp y z) {g : Pn n} (hg : g ∈ symmDiff X Y) (hgy : g ≠ y) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  rw [symmDiff_comm] at hg ⊢
  exact not_conn_of_isolated hY hy hyX hg hgy

theorem exists_ne_fin (hn : 2 ≤ n) (i : Fin n) : ∃ k : Fin n, k ≠ i := by
  by_cases h : i.val = 0
  · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
  · exact ⟨⟨0, by omega⟩, fun e => h (by rw [← e])⟩

theorem exists_two_ne (hn : 3 ≤ n) (j : Fin n) : ∃ p q : Fin n, p ≠ q ∧ p ≠ j ∧ q ≠ j := by
  by_cases h0 : j.val = 0
  · refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;> intro e <;> simp [Fin.ext_iff] at e <;> omega
  · by_cases h1 : j.val = 1
    · refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩ <;> intro e <;> simp [Fin.ext_iff] at e <;> omega
    · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, ?_⟩ <;> intro e <;> simp [Fin.ext_iff] at e <;> omega

/-- More than `k` values of an injective map cannot all lie in a set of size at most `k`. -/
theorem exists_not_mem {f : Fin n → Pn n} (hf : Function.Injective f) {T : Set (Pn n)} {k : ℕ}
    (hT : T.encard ≤ k) (hk : k < n) : ∃ p, f p ∉ T := by
  by_contra hcon
  push Not at hcon
  have hsub : f '' Set.univ ⊆ T := by
    rintro _ ⟨p, -, rfl⟩
    exact hcon p
  have hle := (Set.encard_le_encard hsub).trans hT
  rw [hf.encard_image, Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hle
  exact absurd (by exact_mod_cast hle : n ≤ k) (by omega)

theorem a_injective : Function.Injective (fun i : Fin n => (PnElem.a i : Pn n)) := fun _ _ h => PnElem.a.inj h

theorem b_injective : Function.Injective (fun j : Fin n => (PnElem.b j : Pn n)) := fun _ _ h => PnElem.b.inj h

theorem tgtB_sub_lamB : tgtB n ⊆ lamB n := Set.subset_union_right

theorem tgtA_sub_lamA : tgtA n ⊆ lamA n := Set.subset_union_right

/-- `X` is low: `X = A` or of type (D) or (L). -/
abbrev LowA (n : ℕ) (X : Set (Pn n)) : Prop := X = tgtA n ∨ IsTypeD n X ∨ IsTypeL n X

/-- `Y` is low: `Y = B` or of type (D') or (L'). -/
abbrev LowB (n : ℕ) (Y : Set (Pn n)) : Prop := Y = tgtB n ∨ IsTypeD' n Y ∨ IsTypeL' n Y

theorem lowA_nonempty (hn : 2 ≤ n) {X : Set (Pn n)} (hX : LowA n X) : X.Nonempty := by
  rcases hX with rfl | ⟨i, rfl⟩ | ⟨R, S, -, -, ⟨s, hs⟩, -, -, rfl⟩
  · exact ⟨PnElem.a ⟨0, by omega⟩, ⟨_, rfl⟩⟩
  · obtain ⟨k, hk⟩ := exists_ne_fin hn i
    exact ⟨PnElem.a k, ⟨k, rfl⟩, fun e => hk (PnElem.a.inj e)⟩
  · exact ⟨s, Or.inr hs⟩

theorem lowB_nonempty (hn : 2 ≤ n) {Y : Set (Pn n)} (hY : LowB n Y) : Y.Nonempty := by
  rcases hY with rfl | ⟨j, rfl⟩ | ⟨R, S, -, -, ⟨s, hs⟩, -, -, rfl⟩
  · exact ⟨PnElem.b ⟨0, by omega⟩, ⟨_, rfl⟩⟩
  · obtain ⟨k, hk⟩ := exists_ne_fin hn j
    exact ⟨PnElem.b k, ⟨k, rfl⟩, fun e => hk (PnElem.b.inj e)⟩
  · exact ⟨s, Or.inr hs⟩

theorem classA {X : Set (Pn n)} (hX : X ∈ nbhdC (tgtA n)) : LowA n X ∨ IsTypeE n X ∨ IsTypeH n X := by
  by_cases h : X = tgtA n
  · exact Or.inl (Or.inl h)
  rcases lem_6_8 n X hX h with h | h | h | h
  exacts [Or.inl (Or.inr (Or.inl h)), Or.inr (Or.inl h), Or.inl (Or.inr (Or.inr h)), Or.inr (Or.inr h)]

theorem classB {Y : Set (Pn n)} (hY : Y ∈ nbhdC (tgtB n)) : LowB n Y ∨ IsTypeE' n Y ∨ IsTypeH' n Y := by
  by_cases h : Y = tgtB n
  · exact Or.inl (Or.inl h)
  rcases lem_6_8_B n Y hY h with h | h | h | h
  exacts [Or.inl (Or.inr (Or.inl h)), Or.inr (Or.inl h), Or.inl (Or.inr (Or.inr h)), Or.inr (Or.inr h)]

/-! ### The five cases -/

/-- Case 1: both low. -/
theorem case1 (hn : 2 ≤ n) {X Y : Set (Pn n)} (hXl : LowA n X) (hYl : LowB n Y) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  have hXs := sub_lamA X hXl
  have hYs := sub_lamB Y hYl
  obtain ⟨x, hx⟩ := lowA_nonempty hn hXl
  obtain ⟨y, hy⟩ := lowB_nonempty hn hYl
  have hdisj := (def_6_1_partition_proved n).2.1
  have hxY : x ∉ Y := fun h => Set.disjoint_left.1 hdisj (hXs hx) (hYs h)
  have hyX : y ∉ X := fun h => Set.disjoint_left.1 hdisj (hXs h) (hYs hy)
  refine ⟨⟨x, Set.mem_symmDiff.2 (Or.inl ⟨hx, hxY⟩)⟩, fun hconn => ?_⟩
  obtain ⟨u, -, v, hv, hQu, hQv, huv⟩ := S4.isConnSet_cross hconn (fun z => z ∈ lamA n)
    (Set.mem_symmDiff.2 (Or.inl ⟨hx, hxY⟩)) (Set.mem_symmDiff.2 (Or.inr ⟨hy, hyX⟩)) (hXs hx)
    (fun h => Set.disjoint_left.1 hdisj h (hYs hy))
  have hvB : v ∈ lamB n := by
    rcases Set.mem_symmDiff.1 hv with ⟨hvX, -⟩ | ⟨hvY, -⟩
    · exact absurd (hXs hvX) hQv
    · exact hYs hvY
  exact (lem_6_2_iii_proved n) u hQu v hvB huv

/-- Two targets of `B` in a set of type (E') or (H') (`n ≥ 3`). -/
theorem two_targets_B (hn : 3 ≤ n) {Y : Set (Pn n)} (hY : IsTypeE' n Y ∨ IsTypeH' n Y) :
    ∃ p q : Fin n, p ≠ q ∧ (PnElem.b p : Pn n) ∈ Y ∧ (PnElem.b q : Pn n) ∈ Y := by
  rcases hY with ⟨z, -, rfl⟩ | ⟨j, S, -, rfl⟩
  · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩
  · obtain ⟨p, q, hpq, hpj, hqj⟩ := exists_two_ne hn j
    exact ⟨p, q, hpq, Or.inl ⟨⟨p, rfl⟩, fun e => hpj (PnElem.b.inj e)⟩,
      Or.inl ⟨⟨q, rfl⟩, fun e => hqj (PnElem.b.inj e)⟩⟩

/-- Two targets of `A` in a set of type (E) or (H) (`n ≥ 3`). -/
theorem two_targets_A (hn : 3 ≤ n) {X : Set (Pn n)} (hX : IsTypeE n X ∨ IsTypeH n X) :
    ∃ p q : Fin n, p ≠ q ∧ (PnElem.a p : Pn n) ∈ X ∧ (PnElem.a q : Pn n) ∈ X := by
  rcases hX with ⟨z, -, rfl⟩ | ⟨i, S, -, rfl⟩
  · exact ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff], Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩
  · obtain ⟨p, q, hpq, hpi, hqi⟩ := exists_two_ne hn i
    exact ⟨p, q, hpq, Or.inl ⟨⟨p, rfl⟩, fun e => hpi (PnElem.a.inj e)⟩,
      Or.inl ⟨⟨q, rfl⟩, fun e => hqi (PnElem.a.inj e)⟩⟩

/-- Case 2: `X` low, `Y` not low. -/
theorem case2 (hn : 3 ≤ n) {X Y : Set (Pn n)} (hYa : IsAntichainSet Y) (hXl : LowA n X)
    (hY : IsTypeE' n Y ∨ IsTypeH' n Y) : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  have hXs := sub_lamA X hXl
  obtain ⟨p, q, hpq, hp, hq⟩ := two_targets_B hn hY
  have hnot : ∀ l : Fin n, (PnElem.b l : Pn n) ∉ X := fun l hl =>
    lamA_not_att _ (hXs hl) _ ⟨l, rfl⟩ (Or.inl rfl)
  have hiso : ∀ z ∈ X, ¬ Comp (PnElem.b p : Pn n) z := fun z hz hc =>
    lamA_not_att z (hXs hz) _ ⟨p, rfl⟩ (Or.inr (Or.symm hc))
  exact not_conn_of_isolated' hYa ⟨hp, hnot p⟩ hiso (Set.mem_symmDiff.2 (Or.inr ⟨hq, hnot q⟩))
    (fun e => hpq (PnElem.b.inj e).symm)

/-- Case 2, symmetric: `X` not low, `Y` low. -/
theorem case2' (hn : 3 ≤ n) {X Y : Set (Pn n)} (hXa : IsAntichainSet X) (hX : IsTypeE n X ∨ IsTypeH n X)
    (hYl : LowB n Y) : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  have hYs := sub_lamB Y hYl
  obtain ⟨p, q, hpq, hp, hq⟩ := two_targets_A hn hX
  have hnot : ∀ l : Fin n, (PnElem.a l : Pn n) ∉ Y := fun l hl =>
    lamB_not_att _ (hYs hl) _ ⟨l, rfl⟩ (Or.inl rfl)
  have hiso : ∀ z ∈ Y, ¬ Comp (PnElem.a p : Pn n) z := fun z hz hc =>
    lamB_not_att z (hYs hz) _ ⟨p, rfl⟩ (Or.inr (Or.symm hc))
  exact not_conn_of_isolated hXa ⟨hp, hnot p⟩ hiso (Set.mem_symmDiff.2 (Or.inl ⟨hq, hnot q⟩))
    (fun e => hpq (PnElem.a.inj e).symm)

/-- Case 3: types (E) and (E'). -/
theorem case3 (hn : 3 ≤ n) {X Y : Set (Pn n)} (hXa : IsAntichainSet X) (hX : IsTypeE n X)
    (hY : IsTypeE' n Y) : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  obtain ⟨z, hz, rfl⟩ := hX
  obtain ⟨z', hz', rfl⟩ := hY
  obtain ⟨p, hp⟩ := exists_not_mem a_injective (att_A_le_two z' hz') (show 2 < n by omega)
  obtain ⟨q, hq⟩ := exists_not_mem b_injective (att_B_le_two z hz) (show 2 < n by omega)
  simp only [Set.mem_ofPred_eq, not_and] at hp hq
  have hpY : (PnElem.a p : Pn n) ∉ insert z' (tgtB n) := by
    rintro (e | ⟨l, e⟩)
    · exact hp ⟨p, rfl⟩ (Or.inl e.symm)
    · cases e
  have hqX : (PnElem.b q : Pn n) ∉ insert z (tgtA n) := by
    rintro (e | ⟨l, e⟩)
    · exact hq ⟨q, rfl⟩ (Or.inl e.symm)
    · cases e
  have hiso : ∀ y ∈ insert z' (tgtB n), ¬ Comp (PnElem.a p : Pn n) y := by
    rintro y (rfl | hyB) hc
    · exact hp ⟨p, rfl⟩ (Or.inr (Or.symm hc))
    · exact lamB_not_att y (tgtB_sub_lamB hyB) _ ⟨p, rfl⟩ (Or.inr (Or.symm hc))
  exact not_conn_of_isolated hXa ⟨Or.inr ⟨p, rfl⟩, hpY⟩ hiso
    (Set.mem_symmDiff.2 (Or.inr ⟨Or.inr ⟨q, rfl⟩, hqX⟩)) (fun e => by cases e)

/-- Case 4: types (E) and (H') (`n ≥ 4`). -/
theorem case4 (hn : 4 ≤ n) {X Y : Set (Pn n)} (hYa : IsAntichainSet Y) (hX : IsTypeE n X)
    (hY : IsTypeH' n Y) : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  obtain ⟨z, hz, rfl⟩ := hX
  obtain ⟨j, S, hS, rfl⟩ := hY
  have hT : ({u | u ∈ tgtB n ∧ Attached z u} ∪ {PnElem.b j}).encard ≤ (3 : ℕ) :=
    calc _ ≤ _ + _ := Set.encard_union_le _ _
      _ ≤ 2 + 1 := add_le_add (att_B_le_two z hz) (Set.encard_singleton _).le
      _ = ((3 : ℕ) : ℕ∞) := by norm_num
  obtain ⟨q, hq⟩ := exists_not_mem b_injective hT (show 3 < n by omega)
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_or, not_and] at hq
  have hqY : (PnElem.b q : Pn n) ∈ (tgtB n \ {PnElem.b j}) ∪ S := Or.inl ⟨⟨q, rfl⟩, hq.2⟩
  have hqX : (PnElem.b q : Pn n) ∉ insert z (tgtA n) := by
    rintro (e | ⟨l, e⟩)
    · exact hq.1 ⟨q, rfl⟩ (Or.inl e.symm)
    · cases e
  have hiso : ∀ x ∈ insert z (tgtA n), ¬ Comp (PnElem.b q : Pn n) x := by
    rintro x (rfl | hxA) hc
    · exact hq.1 ⟨q, rfl⟩ (Or.inr (Or.symm hc))
    · exact lamA_not_att x (tgtA_sub_lamA hxA) _ ⟨q, rfl⟩ (Or.inr (Or.symm hc))
  have hYA := ((lem_6_10 n).2.2 j S hS).1
  have ha0 : (PnElem.a ⟨0, by omega⟩ : Pn n) ∉ (tgtB n \ {PnElem.b j}) ∪ S := fun h =>
    (Set.eq_empty_iff_forall_notMem.1 hYA) _ ⟨h, ⟨_, rfl⟩⟩
  exact not_conn_of_isolated' hYa ⟨hqY, hqX⟩ hiso
    (Set.mem_symmDiff.2 (Or.inl ⟨Or.inr ⟨_, rfl⟩, ha0⟩)) (fun e => by cases e)

/-- Case 4, symmetric: types (H) and (E') (`n ≥ 4`). -/
theorem case4' (hn : 4 ≤ n) {X Y : Set (Pn n)} (hXa : IsAntichainSet X) (hX : IsTypeH n X)
    (hY : IsTypeE' n Y) : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  obtain ⟨i, S, hS, rfl⟩ := hX
  obtain ⟨z', hz', rfl⟩ := hY
  have hT : ({u | u ∈ tgtA n ∧ Attached z' u} ∪ {PnElem.a i}).encard ≤ (3 : ℕ) :=
    calc _ ≤ _ + _ := Set.encard_union_le _ _
      _ ≤ 2 + 1 := add_le_add (att_A_le_two z' hz') (Set.encard_singleton _).le
      _ = ((3 : ℕ) : ℕ∞) := by norm_num
  obtain ⟨p, hp⟩ := exists_not_mem a_injective hT (show 3 < n by omega)
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_singleton_iff, not_or, not_and] at hp
  have hpX : (PnElem.a p : Pn n) ∈ (tgtA n \ {PnElem.a i}) ∪ S := Or.inl ⟨⟨p, rfl⟩, hp.2⟩
  have hpY : (PnElem.a p : Pn n) ∉ insert z' (tgtB n) := by
    rintro (e | ⟨l, e⟩)
    · exact hp.1 ⟨p, rfl⟩ (Or.inl e.symm)
    · cases e
  have hiso : ∀ y ∈ insert z' (tgtB n), ¬ Comp (PnElem.a p : Pn n) y := by
    rintro y (rfl | hyB) hc
    · exact hp.1 ⟨p, rfl⟩ (Or.inr (Or.symm hc))
    · exact lamB_not_att y (tgtB_sub_lamB hyB) _ ⟨p, rfl⟩ (Or.inr (Or.symm hc))
  have hXB := ((lem_6_10_swap n).2.2 i S hS).1
  have hb0 : (PnElem.b ⟨0, by omega⟩ : Pn n) ∉ (tgtA n \ {PnElem.a i}) ∪ S := fun h =>
    (Set.eq_empty_iff_forall_notMem.1 hXB) _ ⟨h, ⟨_, rfl⟩⟩
  exact not_conn_of_isolated hXa ⟨hpX, hpY⟩ hiso
    (Set.mem_symmDiff.2 (Or.inr ⟨Or.inr ⟨_, rfl⟩, hb0⟩)) (fun e => by cases e)

/-- Case 5: types (H) and (H'). -/
theorem case5 (hn : 2 ≤ n) {X Y : Set (Pn n)} (hXa : IsAntichainSet X) (hX : IsTypeH n X)
    (hY : IsTypeH' n Y) : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  obtain ⟨i, S, hS, rfl⟩ := hX
  obtain ⟨j, S', hS', rfl⟩ := hY
  obtain ⟨p, hpi⟩ := exists_ne_fin hn i
  obtain ⟨q, hqj⟩ := exists_ne_fin hn j
  have hXform : ∀ x ∈ (tgtA n \ {PnElem.a i}) ∪ S,
      (∃ k, k ≠ i ∧ x = PnElem.a k) ∨ x = PnElem.w i ∨ ∃ l, x = PnElem.t i l := by
    rintro x (⟨⟨k, rfl⟩, hk⟩ | hxS)
    · exact Or.inl ⟨k, fun e => hk (e ▸ rfl), rfl⟩
    · rcases hS with rfl | ⟨-, hS⟩
      · exact Or.inr (Or.inl hxS)
      · exact Or.inr (Or.inr (hS hxS))
  have hpX : (PnElem.a p : Pn n) ∈ (tgtA n \ {PnElem.a i}) ∪ S := Or.inl ⟨⟨p, rfl⟩, fun e => hpi (PnElem.a.inj e)⟩
  have hXB := ((lem_6_10_swap n).2.2 i S hS).1
  have hYA := ((lem_6_10 n).2.2 j S' hS').1
  have hpY : (PnElem.a p : Pn n) ∉ (tgtB n \ {PnElem.b j}) ∪ S' := fun h =>
    (Set.eq_empty_iff_forall_notMem.1 hYA) _ ⟨h, ⟨_, rfl⟩⟩
  have hqY : (PnElem.b q : Pn n) ∈ (tgtB n \ {PnElem.b j}) ∪ S' := Or.inl ⟨⟨q, rfl⟩, fun e => hqj (PnElem.b.inj e)⟩
  have hqX : (PnElem.b q : Pn n) ∉ (tgtA n \ {PnElem.a i}) ∪ S := fun h =>
    (Set.eq_empty_iff_forall_notMem.1 hXB) _ ⟨h, ⟨_, rfl⟩⟩
  have hqG : (PnElem.b q : Pn n) ∈ symmDiff ((tgtA n \ {PnElem.a i}) ∪ S) ((tgtB n \ {PnElem.b j}) ∪ S') :=
    Set.mem_symmDiff.2 (Or.inr ⟨hqY, hqX⟩)
  rcases hS' with rfl | ⟨-, hS'⟩
  · -- (5a) `S' = {w'_j}`: `a_p` is comparable to no element of `Y`
    refine not_conn_of_isolated hXa ⟨hpX, hpY⟩ ?_ hqG (fun e => by cases e)
    rintro y (⟨⟨l, rfl⟩, -⟩ | hy) hc
    · simp [comp_iff_ple, ple] at hc
    · rw [Set.mem_singleton_iff.1 hy] at hc
      simp [comp_iff_ple, ple] at hc
  · -- (5b) `S' ⊆ {t_1j, …, t_nj}`: the component of `a_p` lies in `{a_p, t_pj}`
    have hYform : ∀ y ∈ (tgtB n \ {PnElem.b j}) ∪ S', (∃ l, l ≠ j ∧ y = PnElem.b l) ∨ ∃ k, y = PnElem.t k j := by
      rintro y (⟨⟨l, rfl⟩, hl⟩ | hyS)
      · exact Or.inl ⟨l, fun e => hl (e ▸ rfl), rfl⟩
      · exact Or.inr (hS' hyS)
    have hpG := Set.mem_symmDiff.2 (Or.inl ⟨hpX, hpY⟩)
    refine ⟨⟨_, hpG⟩, fun hconn => ?_⟩
    obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ := S4.isConnSet_cross hconn
      (fun z => z = PnElem.a p ∨ z = PnElem.t p j) hpG hqG (Or.inl rfl) (by rintro (e | e) <;> cases e)
    simp only [not_or] at hQv
    have hvXY : v ∈ (tgtA n \ {PnElem.a i}) ∪ S ∨ v ∈ (tgtB n \ {PnElem.b j}) ∪ S' := by
      rcases Set.mem_symmDiff.1 hv with ⟨h, -⟩ | ⟨h, -⟩
      exacts [Or.inl h, Or.inr h]
    rcases hQu with rfl | rfl
    · rcases hvXY with hvX | hvY
      · rcases hXform v hvX with ⟨k, -, rfl⟩ | rfl | ⟨l, rfl⟩
        · simp [comp_iff_ple, ple] at huv; exact huv.2 (huv.1.elim id Eq.symm)
        · simp [comp_iff_ple, ple] at huv; exact hpi huv
        · simp [comp_iff_ple, ple] at huv; exact hpi huv
      · rcases hYform v hvY with ⟨l, -, rfl⟩ | ⟨k, rfl⟩
        · simp [comp_iff_ple, ple] at huv
        · simp [comp_iff_ple, ple] at huv; exact hQv.2 (by rw [huv])
    · rcases hvXY with hvX | hvY
      · rcases hXform v hvX with ⟨k, -, rfl⟩ | rfl | ⟨l, rfl⟩
        · simp [comp_iff_ple, ple] at huv; exact hQv.1 (by rw [huv])
        · simp [comp_iff_ple, ple] at huv; exact hpi huv.symm
        · simp [comp_iff_ple, ple] at huv
          rcases huv with ⟨⟨h1, h2⟩ | ⟨h1, h2⟩, h3⟩
          exacts [h3 h1 h2, h3 h1.symm h2.symm]
      · rcases hYform v hvY with ⟨l, hl, rfl⟩ | ⟨k, rfl⟩
        · simp [comp_iff_ple, ple] at huv; exact hl huv
        · simp [comp_iff_ple, ple] at huv; exact huv.2 (huv.1.elim id Eq.symm)

/-- Proposition 6.11 for `n ≥ 3`, outside Case 4 (Remark 6.12, sec_reverse l. 261). -/
theorem prop_n3 (n : ℕ) (hn : 3 ≤ n) (X Y : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n)) (hY : Y ∈ nbhdC (tgtB n))
    (hEH : ¬ (IsTypeE n X ∧ IsTypeH' n Y)) (hHE : ¬ (IsTypeH n X ∧ IsTypeE' n Y)) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
  obtain ⟨-, hXa, -⟩ := id hX
  obtain ⟨-, hYa, -⟩ := id hY
  rcases classA hX with hXl | hXE | hXH <;> rcases classB hY with hYl | hYE | hYH
  · exact case1 (by omega) hXl hYl
  · exact case2 hn hYa hXl (Or.inl hYE)
  · exact case2 hn hYa hXl (Or.inr hYH)
  · exact case2' hn hXa (Or.inl hXE) hYl
  · exact case3 hn hXa hXE hYE
  · exact absurd ⟨hXE, hYH⟩ hEH
  · exact case2' hn hXa (Or.inr hXH) hYl
  · exact absurd ⟨hXH, hYE⟩ hHE
  · exact case5 (by omega) hXa hXH hYH

/-- Proposition 6.11 (sec_reverse l. 240-242), `n ≥ 4`. -/
theorem prop_6_11 (n : ℕ) (hn : 4 ≤ n) (X Y : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n))
    (hY : Y ∈ nbhdC (tgtB n)) :
    (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) ∧ X ≠ Y ∧
      ∀ (hX' : IsAntichainSet X) (hY' : IsAntichainSet Y), 2 ≤ dC X Y hX' hY' := by
  have key : (symmDiff X Y).Nonempty ∧ ¬ IsConnSet (symmDiff X Y) := by
    by_cases hEH : IsTypeE n X ∧ IsTypeH' n Y
    · exact case4 hn hY.2.1 hEH.1 hEH.2
    by_cases hHE : IsTypeH n X ∧ IsTypeE' n Y
    · exact case4' hn hX.2.1 hHE.1 hHE.2
    exact prop_n3 n (by omega) X Y hX hY hEH hHE
  have hne : X ≠ Y := by
    rintro rfl
    obtain ⟨x, hx⟩ := key.1
    rw [symmDiff_self] at hx
    exact hx
  refine ⟨key.1, key.2, hne, fun hX' hY' => ?_⟩
  by_contra hlt
  have hle : dC X Y hX' hY' ≤ ((1 : ℕ) : ℕ∞) := by
    rw [not_le] at hlt
    have h1 : dC X Y hX' hY' < (1 : ℕ∞) + 1 := by simpa [one_add_one_eq_two] using hlt
    exact_mod_cast Order.le_of_lt_add_one h1
  exact key.2 (conn_of_mem_nbhdC ⟨hX', hY', by exact_mod_cast hle⟩ (Ne.symm hne)).2.2

end LeeDiam.S6C
