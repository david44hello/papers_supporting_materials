/-
LeeDiam/Sec4/Caption.lean — the caption of Table 2 of paper 004 (Tame bases, sec_chain.tex v1.50 l. 84): the
differences of the moves of the three tame-base walks, explicitly.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Every difference is a symmetric difference of two sets in different rows, hence their union (`symmDiff_rows`).
-/
import LeeDiam.Sec4.TableRows

namespace LeeDiam.S4

open Band

variable {k : ℕ}

theorem row_single {x : Band k} {r : Fin 3} (hx : x.2 = r) : ∀ z ∈ ({x} : Set (Band k)), z.2 = r := by
  rintro z rfl
  exact hx

theorem row_pair {x y : Band k} {r : Fin 3} (hx : x.2 = r) (hy : y.2 = r) :
    ∀ z ∈ ({x, y} : Set (Band k)), z.2 = r := by
  rintro z (rfl | rfl)
  · exact hx
  · exact hy

/-- Two sets in different rows are disjoint, so their symmetric difference is their union. -/
theorem symmDiff_rows {X Y : Set (Band k)} {r s : Fin 3} (hrs : r ≠ s) (hX : ∀ x ∈ X, x.2 = r)
    (hY : ∀ y ∈ Y, y.2 = s) : symmDiff X Y = X ∪ Y :=
  Disjoint.symmDiff_eq_sup (Set.disjoint_left.2 fun x hx hy => hrs ((hX x hx).symm.trans (hY x hy)))

theorem table_2_caption_line1 (hk : 1 ≤ k) :
    moveDiff [{b ⟨0, hk⟩}, {c ⟨0, hk⟩}, (∅ : Set (Band k))] 0 = {b ⟨0, hk⟩, c ⟨0, hk⟩} ∧
    moveDiff [{b ⟨0, hk⟩}, {c ⟨0, hk⟩}, (∅ : Set (Band k))] 1 = {c ⟨0, hk⟩} := by
  refine ⟨?_, ?_⟩
  · show symmDiff {b ⟨0, hk⟩} {c ⟨0, hk⟩} = _
    exact symmDiff_singletons (b_ne_c _ _)
  · show symmDiff {c ⟨0, hk⟩} (∅ : Set (Band k)) = _
    rw [← Set.bot_eq_empty, symmDiff_bot]

theorem table_2_caption_lines23 (hk : 2 ≤ k) :
    moveDiff [∅, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨0, by omega⟩, b ⟨1, hk⟩} : Set (Band k))] 0 = {a ⟨0, by omega⟩} ∧
    moveDiff [∅, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨0, by omega⟩, b ⟨1, hk⟩} : Set (Band k))] 1 = {a ⟨0, by omega⟩, c ⟨0, by omega⟩, c ⟨1, hk⟩} ∧
    moveDiff [∅, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨0, by omega⟩, b ⟨1, hk⟩} : Set (Band k))] 2 =
      {c ⟨0, by omega⟩, c ⟨1, hk⟩, b ⟨0, by omega⟩, b ⟨1, hk⟩} ∧
    moveDiff [{b ⟨0, by omega⟩}, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨1, hk⟩} : Set (Band k))] 0 = {b ⟨0, by omega⟩, a ⟨0, by omega⟩} ∧
    moveDiff [{b ⟨0, by omega⟩}, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨1, hk⟩} : Set (Band k))] 1 = {a ⟨0, by omega⟩, c ⟨0, by omega⟩, c ⟨1, hk⟩} ∧
    moveDiff [{b ⟨0, by omega⟩}, {a ⟨0, by omega⟩}, {c ⟨0, by omega⟩, c ⟨1, hk⟩},
      ({b ⟨1, hk⟩} : Set (Band k))] 2 = {c ⟨0, by omega⟩, c ⟨1, hk⟩, b ⟨1, hk⟩} := by
  have h01 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hac : symmDiff ({a ⟨0, by omega⟩} : Set (Band k)) {c ⟨0, by omega⟩, c ⟨1, hk⟩} =
      {a ⟨0, by omega⟩, c ⟨0, by omega⟩, c ⟨1, hk⟩} := by
    rw [symmDiff_rows h01 (row_single (a_snd _)) (row_pair (c_snd _) (c_snd _)), Set.singleton_union]
  refine ⟨?_, hac, ?_, ?_, hac, ?_⟩
  · show symmDiff (∅ : Set (Band k)) {a ⟨0, by omega⟩} = _
    rw [← Set.bot_eq_empty, bot_symmDiff]
  · show symmDiff ({c ⟨0, by omega⟩, c ⟨1, hk⟩} : Set (Band k)) {b ⟨0, by omega⟩, b ⟨1, hk⟩} = _
    rw [symmDiff_rows h12.symm (row_pair (c_snd _) (c_snd _)) (row_pair (b_snd _) (b_snd _)), Set.insert_union,
      Set.singleton_union]
  · show symmDiff ({b ⟨0, by omega⟩} : Set (Band k)) {a ⟨0, by omega⟩} = _
    exact symmDiff_singletons (a_ne_b _ _).symm
  · show symmDiff ({c ⟨0, by omega⟩, c ⟨1, hk⟩} : Set (Band k)) {b ⟨1, hk⟩} = _
    rw [symmDiff_rows h12.symm (row_pair (c_snd _) (c_snd _)) (row_single (b_snd _)), Set.insert_union,
      Set.singleton_union]

end LeeDiam.S4

namespace LeeDiam

theorem table_2_caption_line1_proved {k : ℕ} (hk : 1 ≤ k) :
    moveDiff [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] 0 = {Band.b ⟨0, hk⟩, Band.c ⟨0, hk⟩} ∧
    moveDiff [{Band.b ⟨0, hk⟩}, {Band.c ⟨0, hk⟩}, (∅ : Set (Band k))] 1 = {Band.c ⟨0, hk⟩} :=
  S4.table_2_caption_line1 hk

theorem table_2_caption_lines23_proved {k : ℕ} (hk : 2 ≤ k) :
    moveDiff [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] 0 = {Band.a ⟨0, by omega⟩} ∧
    moveDiff [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] 1 =
      {Band.a ⟨0, by omega⟩, Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩} ∧
    moveDiff [∅, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} : Set (Band k))] 2 =
      {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩, Band.b ⟨0, by omega⟩, Band.b ⟨1, hk⟩} ∧
    moveDiff [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] 0 = {Band.b ⟨0, by omega⟩, Band.a ⟨0, by omega⟩} ∧
    moveDiff [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] 1 = {Band.a ⟨0, by omega⟩, Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩} ∧
    moveDiff [{Band.b ⟨0, by omega⟩}, {Band.a ⟨0, by omega⟩}, {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩},
      ({Band.b ⟨1, hk⟩} : Set (Band k))] 2 = {Band.c ⟨0, by omega⟩, Band.c ⟨1, hk⟩, Band.b ⟨1, hk⟩} :=
  S4.table_2_caption_lines23 hk

end LeeDiam
