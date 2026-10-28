/-
LeeDiam/Sec6/ChainNbr.lean — Section 6.3 of paper 004 (short v1.50, sec_reverse.tex l. 199-216): Lemma 6.8, the
neighbors of `A` (types (D), (E), (L), (H)) and, with `A` and `B` exchanged, of `B`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec6.ChainHelp

namespace LeeDiam.S6C

open PnSets PnOrder

/-- A neighbor `Y ≠ X` of `X` is an antichain, and `X △ Y` is connected. -/
theorem conn_of_mem_nbhdC {P : Type} [Fintype P] [PartialOrder P] {X Y : Set P} (hY : Y ∈ nbhdC X) (hne : Y ≠ X) :
    IsAntichainSet X ∧ IsAntichainSet Y ∧ IsConnSet (symmDiff X Y) := by
  obtain ⟨hX, hY', hd⟩ := hY
  refine ⟨hX, hY', ?_⟩
  obtain ⟨W, ⟨⟨-, -, hWc⟩, hh, hl⟩, hlen⟩ := (dC_le_iff X Y hX hY' 1).1 (by simpa using hd)
  rcases W with _ | ⟨A0, _ | ⟨A1, _ | ⟨A2, W⟩⟩⟩
  · simp at hh
  · simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hh hl
    exact absurd (hl.symm.trans hh) hne
  · simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons, List.getLast?_singleton] at hh hl
    subst hh hl
    simpa using hWc
  · simp at hlen

/-- In a connected set, an element that is not alone has a comparable neighbor. -/
theorem exists_comp_of_conn {P : Type} [PartialOrder P] {D : Set P} (hD : IsConnSet D) {u w : P} (hu : u ∈ D)
    (hw : w ∈ D) (hwu : w ≠ u) : ∃ v ∈ D, v ≠ u ∧ Comp u v := by
  obtain ⟨u', hu', v, hv, hQu, hvu, hc⟩ := S4.isConnSet_cross hD (fun x => x = u) hu hw rfl hwu
  subst hQu
  exact ⟨v, hv, hvu, hc⟩

theorem not_comp_of_anti {P : Type} [PartialOrder P] {S : Set P} (hS : IsAntichainSet S) {u v : P} (hu : u ∈ S)
    (hv : v ∈ S) (hne : u ≠ v) : ¬ Comp u v := by
  rintro (h | h)
  · exact hS hu hv hne h.le
  · exact hS hv hu (Ne.symm hne) h.le

variable {n : ℕ}

/-- An element comparable to a lower-level element lies above it. -/
theorem lt_of_comp_level {x z : Pn n} (hc : Comp x z) (hl : PnElem.level x < PnElem.level z) : x < z :=
  hc.resolve_right fun h => absurd (lt_level h) (lt_asymm hl)

theorem comp_a_cases (s : Pn n) (i : Fin n) (hs : s ∉ tgtA n) (hc : Comp s (PnElem.a i)) :
    s ∈ pairMinA n ∪ lowA n ∨ s ∈ upA n ∪ tops n := by
  cases s with
  | m E => exact Or.inl (Or.inl ⟨E, rfl⟩)
  | y k => exact Or.inl (Or.inr ⟨k, rfl⟩)
  | w k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | t k l => exact Or.inr (Or.inr ⟨k, l, rfl⟩)
  | a k => exact absurd ⟨k, rfl⟩ hs
  | _ => simp [comp_iff_ple, ple] at hc

theorem comp_b_cases (s : Pn n) (j : Fin n) (hs : s ∉ tgtB n) (hc : Comp s (PnElem.b j)) :
    s ∈ pairMinB n ∪ lowB n ∨ s ∈ upB n ∪ tops n := by
  cases s with
  | m' E => exact Or.inl (Or.inl ⟨E, rfl⟩)
  | y' k => exact Or.inl (Or.inr ⟨k, rfl⟩)
  | w' k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | t k l => exact Or.inr (Or.inr ⟨k, l, rfl⟩)
  | b k => exact absurd ⟨k, rfl⟩ hs
  | _ => simp [comp_iff_ple, ple] at hc

theorem level_lowA {s : Pn n} (hs : s ∈ pairMinA n ∪ lowA n) : PnElem.level s < 2 := by
  rcases hs with ⟨E, rfl⟩ | ⟨i, rfl⟩ <;> simp [PnElem.level]

theorem level_lowB {s : Pn n} (hs : s ∈ pairMinB n ∪ lowB n) : PnElem.level s < 2 := by
  rcases hs with ⟨E, rfl⟩ | ⟨i, rfl⟩ <;> simp [PnElem.level]

theorem level_upA {s : Pn n} (hs : s ∈ upA n ∪ tops n) : 2 < PnElem.level s := by
  rcases hs with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> simp [PnElem.level]

theorem level_upB {s : Pn n} (hs : s ∈ upB n ∪ tops n) : 2 < PnElem.level s := by
  rcases hs with ⟨i, rfl⟩ | ⟨i, j, rfl⟩ <;> simp [PnElem.level]

theorem level_a (i : Fin n) : PnElem.level (PnElem.a i : Pn n) = 2 := rfl

theorem level_b (j : Fin n) : PnElem.level (PnElem.b j : Pn n) = 2 := rfl

theorem lowA_lt_upA {s z : Pn n} (hs : s ∈ pairMinA n ∪ lowA n) (hz : z ∈ upA n ∪ tops n) : s < z := by
  refine (lem_6_2_ii_proved n).2.2.2.2 s ?_ z ?_
  · rcases hs with hs | hs
    · exact Or.inl (Or.inl (Or.inl hs))
    · exact Or.inl (Or.inr hs)
  · rcases hz with hz | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inr hz

theorem lowB_lt_upB {s z : Pn n} (hs : s ∈ pairMinB n ∪ lowB n) (hz : z ∈ upB n ∪ tops n) : s < z := by
  refine (lem_6_2_ii_proved n).2.2.2.2 s ?_ z ?_
  · rcases hs with hs | hs
    · exact Or.inl (Or.inl (Or.inr hs))
    · exact Or.inr hs
  · rcases hz with hz | hz
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz

/-! ### Lemma 6.8 for `A` -/

section SideA

variable {X : Set (Pn n)}

/-- `S = ∅`: type (D). -/
theorem nbrA_D (hA : IsAntichainSet (tgtA n)) (hconn : IsConnSet (symmDiff (tgtA n) X)) (hXA : X ⊆ tgtA n)
    (hne : X ≠ tgtA n) : IsTypeD n X := by
  obtain ⟨r, hrA, hrX⟩ : ∃ r ∈ tgtA n, r ∉ X := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hXA hcon)
  have hR : ∀ r' ∈ tgtA n, r' ∉ X → r' = r := by
    intro r' hr'A hr'X
    by_contra hr'r
    obtain ⟨v, hv, hvr, hc⟩ := exists_comp_of_conn hconn (Set.mem_symmDiff.2 (Or.inl ⟨hrA, hrX⟩))
      (Set.mem_symmDiff.2 (Or.inl ⟨hr'A, hr'X⟩)) hr'r
    rcases Set.mem_symmDiff.1 hv with ⟨hvA, -⟩ | ⟨hvX, -⟩
    · exact not_comp_of_anti hA hrA hvA (Ne.symm hvr) hc
    · exact not_comp_of_anti hA hrA (hXA hvX) (Ne.symm hvr) hc
  obtain ⟨i, rfl⟩ := hrA
  refine ⟨i, Set.ext fun x => ⟨fun hx => ⟨hXA hx, fun hxa => hrX (Set.mem_singleton_iff.1 hxa ▸ hx)⟩,
    fun ⟨hxA, hxa⟩ => ?_⟩⟩
  by_contra hxX
  exact hxa (Set.mem_singleton_iff.2 (hR x hxA hxX))

/-- `R = ∅`: type (E). -/
theorem nbrA_E (hX : IsAntichainSet X) (hconn : IsConnSet (symmDiff (tgtA n) X)) (hAX : tgtA n ⊆ X)
    (hne : X ≠ tgtA n) : IsTypeE n X := by
  obtain ⟨s, hsX, hsA⟩ : ∃ s ∈ X, s ∉ tgtA n := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hcon hAX)
  have hS : ∀ s' ∈ X, s' ∉ tgtA n → s' = s := by
    intro s' hs'X hs'A
    by_contra hs's
    obtain ⟨v, hv, hvs, hc⟩ := exists_comp_of_conn hconn (Set.mem_symmDiff.2 (Or.inr ⟨hsX, hsA⟩))
      (Set.mem_symmDiff.2 (Or.inr ⟨hs'X, hs'A⟩)) hs's
    rcases Set.mem_symmDiff.1 hv with ⟨hvA, hvX⟩ | ⟨hvX, -⟩
    · exact hvX (hAX hvA)
    · exact not_comp_of_anti hX hsX hvX (Ne.symm hvs) hc
  refine ⟨s, ⟨hsA, fun u hu => not_comp_of_anti hX hsX (hAX hu) (fun e => hsA (e ▸ hu))⟩, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxA : x ∈ tgtA n
    · exact Or.inr hxA
    · exact Or.inl (hS x hx hxA)
  · rintro (rfl | hxA)
    · exact hsX
    · exact hAX hxA

/-- `X = (A \ R) ∪ S` with `R = A \ X`, `S = X \ A`. -/
theorem eq_diff_union (X : Set (Pn n)) :
    X = (tgtA n \ (tgtA n \ X)) ∪ (X \ tgtA n) := by
  ext x
  by_cases hxA : x ∈ tgtA n <;> by_cases hxX : x ∈ X <;> simp [hxA, hxX]

/-- `R, S ≠ ∅` and `S` low: type (L). -/
theorem nbrA_L (hX : IsAntichainSet X) (hR0 : (tgtA n \ X).Nonempty) (hS0 : (X \ tgtA n).Nonempty)
    (hnbr : ∀ s ∈ X \ tgtA n, ∃ r ∈ tgtA n \ X, Comp s r) (hlow : ∀ s ∈ X \ tgtA n, s ∈ pairMinA n ∪ lowA n) :
    IsTypeL n X := by
  refine ⟨tgtA n \ X, X \ tgtA n, hR0, Set.sdiff_subset, hS0, hlow, fun s hs => ⟨?_, ?_⟩, eq_diff_union X⟩
  · obtain ⟨r, hr, hc⟩ := hnbr s hs
    obtain ⟨i, rfl⟩ := hr.1
    exact ⟨_, hr, lt_of_comp_level hc (by rw [level_a]; exact level_lowA (hlow s hs))⟩
  · intro r hr hlt
    have hrX : r ∈ X := by
      by_contra hrX
      exact hr.2 ⟨hr.1, hrX⟩
    exact not_comp_of_anti hX hs.1 hrX (fun e => hs.2 (e ▸ hr.1)) (Or.inl hlt)

/-- `R, S ≠ ∅` and `S` high: type (H). -/
theorem nbrA_H (hA : IsAntichainSet (tgtA n)) (hX : IsAntichainSet X)
    (hconn : IsConnSet (symmDiff (tgtA n) X)) {r0 : Pn n} (hr0 : r0 ∈ tgtA n \ X) (hS0 : (X \ tgtA n).Nonempty)
    (hnbr : ∀ s ∈ X \ tgtA n, ∃ r ∈ tgtA n \ X, Comp s r) (hhigh : ∀ s ∈ X \ tgtA n, s ∈ upA n ∪ tops n) :
    IsTypeH n X := by
  -- every element of `S` lies above its neighbor in `R`
  have habove : ∀ s ∈ X \ tgtA n, ∀ r ∈ tgtA n, Comp s r → r < s := by
    intro s hs r hr hc
    obtain ⟨i, rfl⟩ := hr
    exact lt_of_comp_level (Or.symm hc) (by rw [level_a]; exact level_upA (hhigh s hs))
  -- `R = {r0}`
  have hR : ∀ r1 ∈ tgtA n \ X, r1 = r0 := by
    intro r1 hr1
    by_contra hr10
    obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ := S4.isConnSet_cross hconn
      (fun x => x = r0 ∨ (x ∈ X \ tgtA n ∧ r0 < x)) (Set.mem_symmDiff.2 (Or.inl hr0))
      (Set.mem_symmDiff.2 (Or.inl hr1)) (Or.inl rfl)
      (by rintro (h | ⟨h, -⟩); exacts [hr10 h, h.2 hr1.1])
    simp only [not_or, not_and] at hQv
    rcases hQu with rfl | ⟨huS, hlt⟩
    · rcases Set.mem_symmDiff.1 hv with hvR | hvS
      · exact not_comp_of_anti hA hr0.1 hvR.1 (Ne.symm hQv.1) huv
      · exact hQv.2 hvS (habove v hvS u hr0.1 (Or.symm huv))
    · rcases Set.mem_symmDiff.1 hv with hvR | hvS
      · have hvu := habove u huS v hvR.1 huv
        obtain ⟨i, hi, huniq⟩ := (lem_6_2_iv_proved n).1 u (hhigh u huS)
        obtain ⟨k, rfl⟩ := hr0.1
        obtain ⟨l, rfl⟩ := hvR.1
        exact hQv.1 (by rw [huniq l hvu, huniq k hlt])
      · exact not_comp_of_anti hX huS.1 hvS.1 (fun e => hQv.2 (e ▸ hvS) (e ▸ hlt)) huv
  obtain ⟨i, hi⟩ := hr0.1
  subst hi
  -- `S ⊆ {w_i, t_i1, …, t_in}`
  have hSup : ∀ s ∈ X \ tgtA n, s = PnElem.w i ∨ ∃ j, s = PnElem.t i j := by
    intro s hs
    obtain ⟨r, hr, hc⟩ := hnbr s hs
    rw [hR r hr] at hc
    exact ((lem_6_2_i_proved n i).2.2.1 s).1 (habove s hs _ ⟨i, rfl⟩ hc)
  have hXeq : X = (tgtA n \ {PnElem.a i}) ∪ (X \ tgtA n) := by
    have hRi : tgtA n \ X = {PnElem.a i} :=
      Set.ext fun x => ⟨fun hx => Set.mem_singleton_iff.2 (hR x hx), fun hx => (Set.mem_singleton_iff.1 hx) ▸ hr0⟩
    conv_lhs => rw [eq_diff_union X, hRi]
  refine ⟨i, X \ tgtA n, ?_, hXeq⟩
  by_cases hw : (PnElem.w i : Pn n) ∈ X \ tgtA n
  · left
    refine Set.ext fun s => ⟨fun hs => ?_, fun hs => (Set.mem_singleton_iff.1 hs) ▸ hw⟩
    rcases hSup s hs with rfl | ⟨j, rfl⟩
    · rfl
    · have hlt : (PnElem.w i : Pn n) < PnElem.t i j := lt_iff_ple.2 ⟨rfl, fun e => by cases e⟩
      exact absurd (Or.inl hlt) (not_comp_of_anti hX hw.1 hs.1 (ne_of_lt hlt))
  · right
    refine ⟨hS0, fun s hs => ?_⟩
    rcases hSup s hs with rfl | ⟨j, rfl⟩
    · exact absurd hs hw
    · exact ⟨j, rfl⟩

end SideA

theorem lem_6_8 (n : ℕ) (X : Set (Pn n)) (hX : X ∈ nbhdC (tgtA n)) (hne : X ≠ tgtA n) :
    IsTypeD n X ∨ IsTypeE n X ∨ IsTypeL n X ∨ IsTypeH n X := by
  obtain ⟨hA, hXa, hconn⟩ := conn_of_mem_nbhdC hX hne
  by_cases hXA : X ⊆ tgtA n
  · exact Or.inl (nbrA_D hA hconn hXA hne)
  obtain ⟨s0, hs0⟩ : (X \ tgtA n).Nonempty := Set.nonempty_of_not_subset hXA
  by_cases hAX : tgtA n ⊆ X
  · exact Or.inr (Or.inl (nbrA_E hXa hconn hAX hne))
  obtain ⟨r0, hr0⟩ : (tgtA n \ X).Nonempty := Set.nonempty_of_not_subset hAX
  have hnbr : ∀ s ∈ X \ tgtA n, ∃ r ∈ tgtA n \ X, Comp s r := by
    intro s hs
    obtain ⟨v, hv, -, hc⟩ := exists_comp_of_conn hconn (Set.mem_symmDiff.2 (Or.inr hs))
      (Set.mem_symmDiff.2 (Or.inl hr0)) (fun e => hs.2 (e ▸ hr0.1))
    rcases Set.mem_symmDiff.1 hv with hvR | hvS
    · exact ⟨v, hvR, hc⟩
    · exact absurd hc (not_comp_of_anti hXa hs.1 hvS.1 (fun e => by subst e; exact (hc.elim (lt_irrefl _) (lt_irrefl _))))
  have hcases : ∀ s ∈ X \ tgtA n, s ∈ pairMinA n ∪ lowA n ∨ s ∈ upA n ∪ tops n := by
    intro s hs
    obtain ⟨r, hr, hc⟩ := hnbr s hs
    obtain ⟨i, rfl⟩ := hr.1
    exact comp_a_cases s i hs.2 hc
  by_cases hlow : ∀ s ∈ X \ tgtA n, s ∈ pairMinA n ∪ lowA n
  · exact Or.inr (Or.inr (Or.inl (nbrA_L hXa ⟨r0, hr0⟩ ⟨s0, hs0⟩ hnbr hlow)))
  push Not at hlow
  obtain ⟨s1, hs1, hs1low⟩ := hlow
  have hs1up := (hcases s1 hs1).resolve_left hs1low
  have hhigh : ∀ s ∈ X \ tgtA n, s ∈ upA n ∪ tops n := by
    intro s hs
    refine (hcases s hs).resolve_left fun hsl => ?_
    exact not_comp_of_anti hXa hs.1 hs1.1 (ne_of_lt (lowA_lt_upA hsl hs1up)) (Or.inl (lowA_lt_upA hsl hs1up))
  exact Or.inr (Or.inr (Or.inr (nbrA_H hA hXa hconn hr0 ⟨s0, hs0⟩ hnbr hhigh)))

/-! ### Lemma 6.8 for `B` (the same proof with `A` and `B` exchanged) -/

section SideB

variable {Y : Set (Pn n)}

theorem eq_diff_union_gen (T Y : Set (Pn n)) : Y = (T \ (T \ Y)) ∪ (Y \ T) := by
  ext x
  by_cases hxT : x ∈ T <;> by_cases hxY : x ∈ Y <;> simp [hxT, hxY]

theorem nbrB_D (hB : IsAntichainSet (tgtB n)) (hconn : IsConnSet (symmDiff (tgtB n) Y)) (hYB : Y ⊆ tgtB n)
    (hne : Y ≠ tgtB n) : IsTypeD' n Y := by
  obtain ⟨r, hrB, hrY⟩ : ∃ r ∈ tgtB n, r ∉ Y := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hYB hcon)
  have hR : ∀ r' ∈ tgtB n, r' ∉ Y → r' = r := by
    intro r' hr'B hr'Y
    by_contra hr'r
    obtain ⟨v, hv, hvr, hc⟩ := exists_comp_of_conn hconn (Set.mem_symmDiff.2 (Or.inl ⟨hrB, hrY⟩))
      (Set.mem_symmDiff.2 (Or.inl ⟨hr'B, hr'Y⟩)) hr'r
    rcases Set.mem_symmDiff.1 hv with ⟨hvB, -⟩ | ⟨hvY, -⟩
    · exact not_comp_of_anti hB hrB hvB (Ne.symm hvr) hc
    · exact not_comp_of_anti hB hrB (hYB hvY) (Ne.symm hvr) hc
  obtain ⟨j, rfl⟩ := hrB
  refine ⟨j, Set.ext fun x => ⟨fun hx => ⟨hYB hx, fun hxb => hrY (Set.mem_singleton_iff.1 hxb ▸ hx)⟩,
    fun ⟨hxB, hxb⟩ => ?_⟩⟩
  by_contra hxY
  exact hxb (Set.mem_singleton_iff.2 (hR x hxB hxY))

theorem nbrB_E (hY : IsAntichainSet Y) (hconn : IsConnSet (symmDiff (tgtB n) Y)) (hBY : tgtB n ⊆ Y)
    (hne : Y ≠ tgtB n) : IsTypeE' n Y := by
  obtain ⟨s, hsY, hsB⟩ : ∃ s ∈ Y, s ∉ tgtB n := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hcon hBY)
  have hS : ∀ s' ∈ Y, s' ∉ tgtB n → s' = s := by
    intro s' hs'Y hs'B
    by_contra hs's
    obtain ⟨v, hv, hvs, hc⟩ := exists_comp_of_conn hconn (Set.mem_symmDiff.2 (Or.inr ⟨hsY, hsB⟩))
      (Set.mem_symmDiff.2 (Or.inr ⟨hs'Y, hs'B⟩)) hs's
    rcases Set.mem_symmDiff.1 hv with ⟨hvB, hvY⟩ | ⟨hvY, -⟩
    · exact hvY (hBY hvB)
    · exact not_comp_of_anti hY hsY hvY (Ne.symm hvs) hc
  refine ⟨s, ⟨hsB, fun u hu => not_comp_of_anti hY hsY (hBY hu) (fun e => hsB (e ▸ hu))⟩, ?_⟩
  ext x
  constructor
  · intro hx
    by_cases hxB : x ∈ tgtB n
    · exact Or.inr hxB
    · exact Or.inl (hS x hx hxB)
  · rintro (rfl | hxB)
    · exact hsY
    · exact hBY hxB

theorem nbrB_L (hY : IsAntichainSet Y) (hR0 : (tgtB n \ Y).Nonempty) (hS0 : (Y \ tgtB n).Nonempty)
    (hnbr : ∀ s ∈ Y \ tgtB n, ∃ r ∈ tgtB n \ Y, Comp s r) (hlow : ∀ s ∈ Y \ tgtB n, s ∈ pairMinB n ∪ lowB n) :
    IsTypeL' n Y := by
  refine ⟨tgtB n \ Y, Y \ tgtB n, hR0, Set.sdiff_subset, hS0, hlow, fun s hs => ⟨?_, ?_⟩,
    eq_diff_union_gen (tgtB n) Y⟩
  · obtain ⟨r, hr, hc⟩ := hnbr s hs
    obtain ⟨j, rfl⟩ := hr.1
    exact ⟨_, hr, lt_of_comp_level hc (by rw [level_b]; exact level_lowB (hlow s hs))⟩
  · intro r hr hlt
    have hrY : r ∈ Y := by
      by_contra hrY
      exact hr.2 ⟨hr.1, hrY⟩
    exact not_comp_of_anti hY hs.1 hrY (fun e => hs.2 (e ▸ hr.1)) (Or.inl hlt)

theorem nbrB_H (hB : IsAntichainSet (tgtB n)) (hY : IsAntichainSet Y)
    (hconn : IsConnSet (symmDiff (tgtB n) Y)) {r0 : Pn n} (hr0 : r0 ∈ tgtB n \ Y) (hS0 : (Y \ tgtB n).Nonempty)
    (hnbr : ∀ s ∈ Y \ tgtB n, ∃ r ∈ tgtB n \ Y, Comp s r) (hhigh : ∀ s ∈ Y \ tgtB n, s ∈ upB n ∪ tops n) :
    IsTypeH' n Y := by
  have habove : ∀ s ∈ Y \ tgtB n, ∀ r ∈ tgtB n, Comp s r → r < s := by
    intro s hs r hr hc
    obtain ⟨j, rfl⟩ := hr
    exact lt_of_comp_level (Or.symm hc) (by rw [level_b]; exact level_upB (hhigh s hs))
  have hR : ∀ r1 ∈ tgtB n \ Y, r1 = r0 := by
    intro r1 hr1
    by_contra hr10
    obtain ⟨u, hu, v, hv, hQu, hQv, huv⟩ := S4.isConnSet_cross hconn
      (fun x => x = r0 ∨ (x ∈ Y \ tgtB n ∧ r0 < x)) (Set.mem_symmDiff.2 (Or.inl hr0))
      (Set.mem_symmDiff.2 (Or.inl hr1)) (Or.inl rfl)
      (by rintro (h | ⟨h, -⟩); exacts [hr10 h, h.2 hr1.1])
    simp only [not_or, not_and] at hQv
    rcases hQu with rfl | ⟨huS, hlt⟩
    · rcases Set.mem_symmDiff.1 hv with hvR | hvS
      · exact not_comp_of_anti hB hr0.1 hvR.1 (Ne.symm hQv.1) huv
      · exact hQv.2 hvS (habove v hvS u hr0.1 (Or.symm huv))
    · rcases Set.mem_symmDiff.1 hv with hvR | hvS
      · have hvu := habove u huS v hvR.1 huv
        obtain ⟨j, hj, huniq⟩ := (lem_6_2_iv_proved n).2.2.2.2.1 u (hhigh u huS)
        obtain ⟨k, rfl⟩ := hr0.1
        obtain ⟨l, rfl⟩ := hvR.1
        exact hQv.1 (by rw [huniq l hvu, huniq k hlt])
      · exact not_comp_of_anti hY huS.1 hvS.1 (fun e => hQv.2 (e ▸ hvS) (e ▸ hlt)) huv
  obtain ⟨j, hj⟩ := hr0.1
  subst hj
  have hSup : ∀ s ∈ Y \ tgtB n, s = PnElem.w' j ∨ ∃ i, s = PnElem.t i j := by
    intro s hs
    obtain ⟨r, hr, hc⟩ := hnbr s hs
    rw [hR r hr] at hc
    exact ((lem_6_2_i_proved n j).2.2.2.2.2.2.1 s).1 (habove s hs _ ⟨j, rfl⟩ hc)
  have hYeq : Y = (tgtB n \ {PnElem.b j}) ∪ (Y \ tgtB n) := by
    have hRj : tgtB n \ Y = {PnElem.b j} :=
      Set.ext fun x => ⟨fun hx => Set.mem_singleton_iff.2 (hR x hx), fun hx => (Set.mem_singleton_iff.1 hx) ▸ hr0⟩
    conv_lhs => rw [eq_diff_union_gen (tgtB n) Y, hRj]
  refine ⟨j, Y \ tgtB n, ?_, hYeq⟩
  by_cases hw : (PnElem.w' j : Pn n) ∈ Y \ tgtB n
  · left
    refine Set.ext fun s => ⟨fun hs => ?_, fun hs => (Set.mem_singleton_iff.1 hs) ▸ hw⟩
    rcases hSup s hs with rfl | ⟨i, rfl⟩
    · rfl
    · have hlt : (PnElem.w' j : Pn n) < PnElem.t i j := lt_iff_ple.2 ⟨rfl, fun e => by cases e⟩
      exact absurd (Or.inl hlt) (not_comp_of_anti hY hw.1 hs.1 (ne_of_lt hlt))
  · right
    refine ⟨hS0, fun s hs => ?_⟩
    rcases hSup s hs with rfl | ⟨i, rfl⟩
    · exact absurd hs hw
    · exact ⟨i, rfl⟩

end SideB

theorem lem_6_8_B (n : ℕ) (Y : Set (Pn n)) (hY : Y ∈ nbhdC (tgtB n)) (hne : Y ≠ tgtB n) :
    IsTypeD' n Y ∨ IsTypeE' n Y ∨ IsTypeL' n Y ∨ IsTypeH' n Y := by
  obtain ⟨hB, hYa, hconn⟩ := conn_of_mem_nbhdC hY hne
  by_cases hYB : Y ⊆ tgtB n
  · exact Or.inl (nbrB_D hB hconn hYB hne)
  obtain ⟨s0, hs0⟩ : (Y \ tgtB n).Nonempty := Set.nonempty_of_not_subset hYB
  by_cases hBY : tgtB n ⊆ Y
  · exact Or.inr (Or.inl (nbrB_E hYa hconn hBY hne))
  obtain ⟨r0, hr0⟩ : (tgtB n \ Y).Nonempty := Set.nonempty_of_not_subset hBY
  have hnbr : ∀ s ∈ Y \ tgtB n, ∃ r ∈ tgtB n \ Y, Comp s r := by
    intro s hs
    obtain ⟨v, hv, -, hc⟩ := exists_comp_of_conn hconn (Set.mem_symmDiff.2 (Or.inr hs))
      (Set.mem_symmDiff.2 (Or.inl hr0)) (fun e => hs.2 (e ▸ hr0.1))
    rcases Set.mem_symmDiff.1 hv with hvR | hvS
    · exact ⟨v, hvR, hc⟩
    · exact absurd hc (not_comp_of_anti hYa hs.1 hvS.1 (fun e => by subst e; exact (hc.elim (lt_irrefl _) (lt_irrefl _))))
  have hcases : ∀ s ∈ Y \ tgtB n, s ∈ pairMinB n ∪ lowB n ∨ s ∈ upB n ∪ tops n := by
    intro s hs
    obtain ⟨r, hr, hc⟩ := hnbr s hs
    obtain ⟨j, rfl⟩ := hr.1
    exact comp_b_cases s j hs.2 hc
  by_cases hlow : ∀ s ∈ Y \ tgtB n, s ∈ pairMinB n ∪ lowB n
  · exact Or.inr (Or.inr (Or.inl (nbrB_L hYa ⟨r0, hr0⟩ ⟨s0, hs0⟩ hnbr hlow)))
  push Not at hlow
  obtain ⟨s1, hs1, hs1low⟩ := hlow
  have hs1up := (hcases s1 hs1).resolve_left hs1low
  have hhigh : ∀ s ∈ Y \ tgtB n, s ∈ upB n ∪ tops n := by
    intro s hs
    refine (hcases s hs).resolve_left fun hsl => ?_
    exact not_comp_of_anti hYa hs.1 hs1.1 (ne_of_lt (lowB_lt_upB hsl hs1up)) (Or.inl (lowB_lt_upB hsl hs1up))
  exact Or.inr (Or.inr (Or.inr (nbrB_H hB hYa hconn hr0 ⟨s0, hs0⟩ hnbr hhigh)))

end LeeDiam.S6C
