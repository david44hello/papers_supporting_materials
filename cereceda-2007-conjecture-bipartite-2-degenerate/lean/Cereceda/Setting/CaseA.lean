/-
Cereceda/Setting/CaseA.lean — facts on the two greedy colourings of an instance (case 0 < g of Lemma 2.3).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Facts used by the paper's route of Lemma 2.3 (Setting/CaseAPaper.lean, Setting/CaseAPaperCounts.lean), by
Setting/Misc.lean and by Setting/CaseASteps.lean: the length of a list of moves as a sum of move counts; greedy
colourings are proper, a vertex other than the sink is never on `3`, Claims 1 and 2 of the paper's proof
(v3.90 l. 313-315, 321-322); `α v = 0 ↔ β v = 0` (the set `U` of the paper, v3.90 l. 308-310; `K` here).
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance
import Cereceda.Setting.Heights

namespace Cereceda

open Finset

namespace CaseA

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ### Move counts -/

/-- The length of a list of moves is the sum of the numbers of moves of the vertices. -/
theorem length_eq_sum_movesOf (ms : List (W × Fin 4)) : ms.length = ∑ v, movesOf ms v := by
  induction ms with
  | nil => simp [movesOf]
  | cons m ms ih =>
    simp only [movesOf, List.countP_cons, List.length_cons] at ih ⊢
    rw [sum_add_distrib, ← ih]
    simp

/-! ### Greedy colourings of an instance -/

section Greedy

variable {I : Instance W}

theorem adj_iff {u v : W} : I.graph.Adj u v ↔ u ≠ v ∧ (v ∈ I.out u ∨ u ∈ I.out v) := by
  simp [Skeleton.graph, SimpleGraph.fromRel_adj]

theorem leastFree_unique {L used : Finset (Fin 4)} {y y' : Fin 4} (h : IsLeastFree L used y)
    (h' : IsLeastFree L used y') : y = y' := by
  rcases lt_trichotomy y y' with hlt | heq | hgt
  · exact absurd (h'.2.2 y h.1 hlt) h.2.1
  · exact heq
  · exact absurd (h.2.2 y' h'.1 hgt) h'.2.1

theorem ne_sink_of_mem_out {v u : W} (hu : u ∈ I.out v) : v ≠ I.sink := by
  rintro rfl
  rw [I.sink_out] at hu
  exact Finset.notMem_empty u hu

variable {c0 : Fin 4} {c : W → Fin 4}

theorem greedy_proper (hc : I.IsGreedy c0 c) {u v : W} (huv : I.graph.Adj u v) : c u ≠ c v := by
  rcases (adj_iff.1 huv).2 with hvu | huv'
  · intro h
    exact (hc.2 u (ne_sink_of_mem_out hvu)).2.1 (mem_image.2 ⟨v, hvu, h.symm⟩)
  · intro h
    exact (hc.2 v (ne_sink_of_mem_out huv')).2.1 (mem_image.2 ⟨u, huv', h⟩)

/-- A vertex other than the sink is never on `3`: its list has two colours more than it has out-neighbours. -/
theorem greedy_ne_three (hc : I.IsGreedy c0 c) {v : W} (hv : v ≠ I.sink) : c v ≠ 3 := by
  intro h3
  obtain ⟨hmem, -, hleast⟩ := hc.2 v hv
  rw [h3] at hmem hleast
  have hsub : (I.L v).erase 3 ⊆ (I.out v).image c := fun z hz => by
    obtain ⟨hz3, hzL⟩ := mem_erase.1 hz
    exact hleast z hzL (by omega)
  have h1 := card_le_card hsub
  have h2 : ((I.out v).image c).card ≤ (I.out v).card := card_image_le
  have h3' := card_erase_of_mem hmem
  have h4 := I.L_card v
  omega

theorem greedy_zero_iff (hc : I.IsGreedy c0 c) {v : W} (hv : v ≠ I.sink) :
    c v = 0 ↔ 0 ∈ I.L v ∧ ∀ u ∈ I.out v, c u ≠ 0 := by
  obtain ⟨hmem, hnot, hleast⟩ := hc.2 v hv
  constructor
  · intro h0
    rw [h0] at hmem hnot
    exact ⟨hmem, fun u hu hu0 => hnot (mem_image.2 ⟨u, hu, hu0⟩)⟩
  · rintro ⟨h0L, hall⟩
    by_contra hne
    obtain ⟨u, hu, hu0⟩ := mem_image.1 (hleast 0 h0L (Fin.pos_iff_ne_zero.2 hne))
    exact hall u hu hu0

theorem greedy_zero_nbr (hc : I.IsGreedy c0 c) {v : W} (hv : v ≠ I.sink) (hcv : c v ≠ 0)
    (h0 : 0 ∈ I.L v) : ∃ w ∈ I.out v, c w = 0 := by
  by_contra hno
  push Not at hno
  exact hcv ((greedy_zero_iff hc hv).2 ⟨h0, hno⟩)

theorem L_all_of_two (v : W) (h2 : 2 ≤ (I.out v).card) (z : Fin 4) : z ∈ I.L v := by
  have h := I.L_card v
  have hL : I.L v = univ := eq_univ_of_card _ (le_antisymm (card_le_univ _) (by simp; omega))
  rw [hL]
  exact mem_univ z

/-- (Claim 1, v3.90 l. 313-315) A vertex not on `0` with an out-neighbour `p` not on `0`: all its other out-neighbours are on `0`. -/
theorem parent_others_zero (hc : I.IsGreedy c0 c) {v p : W} (hv : v ≠ I.sink) (hcv : c v ≠ 0)
    (hp : p ∈ I.out v) (hcp : c p ≠ 0) : ∀ u ∈ I.out v, u ≠ p → c u = 0 := by
  intro u hu hup
  by_contra hcu
  have h2 : 2 ≤ (I.out v).card := one_lt_card_iff.2 ⟨p, u, hp, hu, fun h => hup h.symm⟩
  obtain ⟨w, hw, hcw⟩ := greedy_zero_nbr hc hv hcv (L_all_of_two v h2 0)
  have h3 : 2 < (I.out v).card := two_lt_card_iff.2 ⟨p, u, w, hp, hu, hw, fun h => hup h.symm,
    fun h => hcp (by rw [h]; exact hcw), fun h => hcu (by rw [h]; exact hcw)⟩
  have := I.out_card v
  omega

/-- (Claim 2, v3.90 l. 321-322) A vertex not on `0` with an out-neighbour not on `0` has the colours `1, 2, 3` in its list. -/
theorem parent_lists (hc : I.IsGreedy c0 c) {v p : W} (hv : v ≠ I.sink) (hcv : c v ≠ 0)
    (hp : p ∈ I.out v) (hcp : c p ≠ 0) : ∀ z, z ≠ 0 → z ∈ I.L v := by
  intro z hz
  by_cases h0 : (0 : Fin 4) ∈ I.L v
  · obtain ⟨w, hw, hcw⟩ := greedy_zero_nbr hc hv hcv h0
    have hwp : p ≠ w := fun h => hcp (by rw [h]; exact hcw)
    exact L_all_of_two v (one_lt_card_iff.2 ⟨p, w, hp, hw, hwp⟩) z
  · have hsub : I.L v ⊆ univ.erase 0 := fun y hy => mem_erase.2 ⟨fun h => h0 (h ▸ hy), mem_univ y⟩
    have h1 : 0 < (I.out v).card := card_pos.2 ⟨p, hp⟩
    have h2 := I.L_card v
    have h3 : (univ.erase (0 : Fin 4)).card = 3 := by decide
    have heq := eq_of_subset_of_card_le hsub (by omega)
    rw [heq]
    exact mem_erase.2 ⟨hz, mem_univ z⟩

end Greedy

/-! ### `K = α⁻¹(0) = β⁻¹(0)` -/

section ZeroSet

variable {I : Instance W} {α β : W → Fin 4}

/-- `K = α⁻¹(0) = β⁻¹(0)`, by induction along the instance order. -/
theorem zero_iff (hg : 0 < I.g) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∀ v, α v = 0 ↔ β v = 0 := by
  suffices h : ∀ n, ∀ v, I.rank v = n → (α v = 0 ↔ β v = 0) from fun v => h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn
    by_cases hv : v = I.sink
    · subst hv
      have := I.g_lt_x
      rw [hα.1, hβ.1]
      constructor <;> intro h <;> omega
    · rw [greedy_zero_iff hα hv, greedy_zero_iff hβ hv]
      refine and_congr_right fun _ => forall₂_congr fun u hu => ?_
      exact not_congr (ih (I.rank u) (hn ▸ I.out_before v u hu) u rfl)

end ZeroSet

end CaseA

end Cereceda
