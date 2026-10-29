/-
Cereceda/Bip/Sides.lean — Section 3 of the paper (short v3.90): a single-sink instance is connected (l. 451); Lemma 3.5
(sides, l. 455-458) and the joiner and leaver facts of its proof (l. 462-466).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Lemma 3.5 is proved by strong induction on the rank (the instance order), as in the paper; the step derives four facts (a leaver
is away from the sink, a joiner other than `s` on the sink's side, no `(2,1)` on the sink's side, no `(1,2)` away from
it) and a finite check closes it. The hypothesis "single-sink" (`NoRoots`) is not used.
-/
import Cereceda.Bip.Basic

namespace Cereceda

open Finset

namespace Bip

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The patterns of Lemma 3.5 on the side `S_0` of the sink (other than the sink itself). -/
def patS0 : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 1), (2, 2), (1, 0), (2, 0), (1, 2)}

/-- The patterns of Lemma 3.5 on the other side `S_1`. -/
def patS1 : Finset (Fin 4 × Fin 4) := {(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (2, 1)}

theorem mem_patS0_of (a b : Fin 4) (ha : a ≠ 3) (hb : b ≠ 3) (h1 : ¬ (a = 0 ∧ b ≠ 0)) (h2 : ¬ (a = 2 ∧ b = 1)) :
    (a, b) ∈ patS0 := by
  revert a b
  decide

theorem mem_patS1_of (a b : Fin 4) (ha : a ≠ 3) (hb : b ≠ 3) (h1 : ¬ (a ≠ 0 ∧ b = 0)) (h2 : ¬ (a = 1 ∧ b = 2)) :
    (a, b) ∈ patS1 := by
  revert a b
  decide

theorem fin2_eq_of_ne_ne {a b c : Fin 2} (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  revert a b c
  decide

/-- The statement of Lemma 3.5 at one vertex. -/
def SidesAt (I : Instance W) (α β : W → Fin 4) (side : W → Fin 2) (v : W) : Prop :=
  (v ≠ I.sink → side v = side I.sink → (α v, β v) ∈ patS0) ∧ (side v ≠ side I.sink → (α v, β v) ∈ patS1)

section Sides

variable {I : Instance W} {α β : W → Fin 4} (hg : I.g = 0) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β)
  {side : W → Fin 2} (hside : IsProperFn I.graph side)

include hα hβ hside in
/-- A leaver lies away from the sink (given Lemma 3.5 at the out-neighbours). -/
theorem leaver_side {v : W} (ih : ∀ u ∈ I.out v, SidesAt I α β side u) (h0 : α v = 0) (hb : β v ≠ 0) :
    side v ≠ side I.sink := by
  obtain ⟨u, hu, hαu, hβu⟩ := (lem_3_3_proved I α β hα hβ).1 v ⟨h0, hb⟩
  have hsu : side u = side I.sink := by
    by_contra hne
    have hmem := (ih u hu).2 hne
    rw [hβu] at hmem
    revert hmem hαu
    generalize α u = a
    revert a
    decide
  rw [← hsu]
  exact hside v u (adj_of_mem_out hu)

include hα hβ hside in
/-- A joiner other than the sink lies on the side of the sink. -/
theorem joiner_side {v : W} (ih : ∀ u ∈ I.out v, SidesAt I α β side u) (hv : v ≠ I.sink) (ha : α v ≠ 0)
    (h0 : β v = 0) : side v = side I.sink := by
  obtain ⟨u, hu, hαu, hβu⟩ := (lem_3_3_proved I α β hα hβ).2 v hv ⟨ha, h0⟩
  have hus : u ≠ I.sink := by
    intro h
    rw [h, hα.1] at hαu
    exact x_ne_zero I hαu
  have hsu : side u ≠ side I.sink := by
    intro heq
    have hmem := (ih u hu).1 hus heq
    rw [hαu] at hmem
    revert hmem hβu
    generalize β u = b
    revert b
    decide
  exact fin2_eq_of_ne_ne (hside v u (adj_of_mem_out hu)) hsu

include hα hβ hside in
/-- No vertex on the side of the sink has the pattern `(2, 1)`. -/
theorem not_21_side0 {v : W} (ih : ∀ u ∈ I.out v, SidesAt I α β side u) (hv : v ≠ I.sink)
    (hs : side v = side I.sink) : ¬ (α v = 2 ∧ β v = 1) := by
  rintro ⟨h2, h1⟩
  have h1L : (1 : Fin 4) ∈ I.L v := h1 ▸ (hβ.2 v hv).1
  obtain ⟨p, hp, hαp⟩ := greedy_below I hα hv h1L (by rw [h2]; decide)
  have hβp : β p ≠ 1 := fun e => greedy_out_ne I hβ hp (e.trans h1.symm)
  have hsp : side p ≠ side I.sink := by
    rw [← hs]
    exact (hside v p (adj_of_mem_out hp)).symm
  have hmem := (ih p hp).2 hsp
  rw [hαp] at hmem
  revert hmem hβp
  generalize β p = b
  revert b
  decide

include hg hα hβ hside in
/-- No vertex away from the sink has the pattern `(1, 2)`. -/
theorem not_12_side1 {v : W} (ih : ∀ u ∈ I.out v, SidesAt I α β side u) (hv : v ≠ I.sink)
    (hs : side v ≠ side I.sink) : ¬ (α v = 1 ∧ β v = 2) := by
  rintro ⟨h1, h2⟩
  have h1L : (1 : Fin 4) ∈ I.L v := h1 ▸ (hα.2 v hv).1
  obtain ⟨p, hp, hβp⟩ := greedy_below I hβ hv h1L (by rw [h2]; decide)
  have hαp : α p ≠ 1 := fun e => greedy_out_ne I hα hp (e.trans h1.symm)
  have hsp : side p = side I.sink := fin2_eq_of_ne_ne (hside p v (adj_of_mem_out hp).symm) hs
  have hps : p ≠ I.sink := by
    intro h
    rw [h, hβ.1, hg] at hβp
    exact absurd hβp (by decide)
  have hmem := (ih p hp).1 hps hsp
  rw [hβp] at hmem
  revert hmem hαp
  generalize α p = a
  revert a
  decide

include hg hα hβ hside in
/-- Lemma 3.5 at every vertex. -/
theorem sides (v : W) : SidesAt I α β side v := by
  induction hn : I.rank v using Nat.strong_induction_on generalizing v with
  | _ n ihn =>
    have ih : ∀ u ∈ I.out v, SidesAt I α β side u := fun u hu =>
      ihn (I.rank u) (hn ▸ I.out_before v u hu) u rfl
    by_cases hv : v = I.sink
    · exact ⟨fun h => absurd hv h, fun h => absurd (hv ▸ rfl) h⟩
    · have ha3 := greedy_ne_three I hα hv
      have hb3 := greedy_ne_three I hβ hv
      refine ⟨fun _ hs => ?_, fun hs => ?_⟩
      · refine mem_patS0_of _ _ ha3 hb3 ?_ (not_21_side0 hα hβ hside ih hv hs)
        exact fun h => leaver_side hα hβ hside ih h.1 h.2 hs
      · refine mem_patS1_of _ _ ha3 hb3 ?_ (not_12_side1 hg hα hβ hside ih hv hs)
        exact fun h => hs (joiner_side hα hβ hside ih hv h.1 h.2)

end Sides

/-- Every vertex reaches the sink when there are no root vertices. -/
theorem reach_sink (I : Instance W) (hnr : I.NoRoots) (v : W) : I.graph.Reachable v I.sink := by
  induction hn : I.rank v using Nat.strong_induction_on generalizing v with
  | _ n ihn =>
    by_cases hv : v = I.sink
    · rw [hv]
    · have hne : (I.out v).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        exact fun h => hnr v ⟨hv, h⟩
      obtain ⟨u, hu⟩ := hne
      exact (adj_of_mem_out hu).reachable.trans (ihn (I.rank u) (hn ▸ I.out_before v u hu) u rfl)

end Bip

/-- Section 3, v3.90 l. 451: a single-sink instance (`NoRoots`) is connected (every vertex reaches `s`). -/
theorem sec3_connected_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots) :
    I.graph.Connected := by
  have : Nonempty W := ⟨I.sink⟩
  exact ⟨fun u v => (Bip.reach_sink I hnr u).trans (Bip.reach_sink I hnr v).symm⟩

/-- **Lemma 3.5** (lem:sides), v3.90 l. 455-458 (with `g = 0`). -/
theorem lem_3_5_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots) (hg0 : I.g = 0)
    (side : W → Fin 2) (hside : IsProperFn I.graph side) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (v : W) :
    (v ≠ I.sink → side v = side I.sink →
      (α v, β v) ∈ ({(0, 0), (1, 1), (2, 2), (1, 0), (2, 0), (1, 2)} : Finset (Fin 4 × Fin 4))) ∧
    (side v ≠ side I.sink →
      (α v, β v) ∈ ({(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (2, 1)} : Finset (Fin 4 × Fin 4))) := by
  have _hnr := hnr  -- the paper's hypothesis "single-sink"; the proof does not need it
  exact Bip.sides hg0 hα hβ hside v

/-- Proof of Lemma 3.5, v3.90 l. 462-466: joiners lie on the side of `s`, leavers on the other side, and a vertex that
is not fixed and is on `0` neither in `α` nor in `β` has the pattern `(1,2)` on `S_0` and `(2,1)` on `S_1`. -/
theorem lem_3_5_equiv_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hg0 : I.g = 0) (side : W → Fin 2) (hside : IsProperFn I.graph side) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, IsJoiner α β v → side v = side I.sink) ∧ (∀ v, IsLeaver α β v → side v ≠ side I.sink) ∧
    (∀ v, v ≠ I.sink → ¬ IsFixed α β v → α v ≠ 0 → β v ≠ 0 →
      (side v = side I.sink → α v = 1 ∧ β v = 2) ∧ (side v ≠ side I.sink → α v = 2 ∧ β v = 1)) := by
  have _hnr := hnr  -- the paper's hypothesis "single-sink"; the proof does not need it
  have hS := fun v => Bip.sides hg0 hα hβ hside v
  refine ⟨fun v ⟨ha, h0⟩ => ?_, fun v ⟨h0, hb⟩ => ?_, fun v hv hfix ha hb => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · by_contra hne
    have hmem := (hS v).2 hne
    rw [h0] at hmem
    revert hmem ha
    generalize α v = a
    revert a
    decide
  · have hv : v ≠ I.sink := by
      intro h
      rw [h, hα.1] at h0
      exact Bip.x_ne_zero I h0
    intro heq
    have hmem := (hS v).1 hv heq
    rw [h0] at hmem
    revert hmem hb
    generalize β v = b
    revert b
    decide
  · have hmem := (hS v).1 hv hs
    unfold IsFixed at hfix
    revert hmem hfix ha hb
    generalize α v = a
    generalize β v = b
    revert a b
    decide
  · have hmem := (hS v).2 hs
    unfold IsFixed at hfix
    revert hmem hfix ha hb
    generalize α v = a
    generalize β v = b
    revert a b
    decide

end Cereceda
