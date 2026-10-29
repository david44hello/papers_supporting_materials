/-
Cereceda/Intro/TextSteps.lean — a vertex of degree at most 2 can be recoloured with four colours (short v3.90
l. 147-148).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic

namespace Cereceda

open Finset

namespace TextSteps

/-! ### A vertex of degree at most 2 can be recoloured with four colours -/

/-- A 2-degenerate graph on a nonempty vertex set has a vertex of degree at most 2. -/
theorem exists_degree_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hd : IsDegenerate G 2) : ∃ v, G.degree v ≤ 2 := by
  obtain ⟨v, -, hv⟩ := hd Finset.univ Finset.univ_nonempty
  refine ⟨v, ?_⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  exact hv

/-- A colour missing at `v` and at all neighbours of `v`. -/
theorem exists_free_colour {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 4)) (v : V) (hv : G.degree v ≤ 2) :
    ∃ y : Fin 4, y ≠ c v ∧ ∀ u, G.Adj v u → c u ≠ y := by
  set used : Finset (Fin 4) := insert (c v) ((G.neighborFinset v).image c) with hused
  have hcard : used.card < Fintype.card (Fin 4) := by
    calc used.card ≤ ((G.neighborFinset v).image c).card + 1 := Finset.card_insert_le _ _
      _ ≤ (G.neighborFinset v).card + 1 := by gcongr; exact Finset.card_image_le
      _ ≤ 2 + 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]; omega
      _ < Fintype.card (Fin 4) := by simp
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := used) (t := Finset.univ)
    (by rwa [Finset.card_univ])
  refine ⟨y, fun h => hy (h ▸ Finset.mem_insert_self _ _), fun u hu h => hy ?_⟩
  rw [← h]
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem c ((SimpleGraph.mem_neighborFinset G v u).2 hu))

/-- The colouring `c` with `v` recoloured to a colour `y` missing at all neighbours of `v`. -/
def recolour {V : Type} [DecidableEq V] (G : SimpleGraph V) (c : G.Coloring (Fin 4)) (v : V) (y : Fin 4) (hy : ∀ u, G.Adj v u → c u ≠ y) :
    G.Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk (Function.update c v y) (by
    intro a b hab
    by_cases ha : a = v
    · subst ha
      have hb : b ≠ a := G.ne_of_adj hab |>.symm
      rw [Function.update_self, Function.update_of_ne hb]
      exact (hy b hab).symm
    · by_cases hb : b = v
      · subst hb
        rw [Function.update_self, Function.update_of_ne ha]
        exact hy a hab.symm
      · rw [Function.update_of_ne ha, Function.update_of_ne hb]
        exact c.valid hab)

theorem recolour_apply {V : Type} [DecidableEq V] (G : SimpleGraph V) (c : G.Coloring (Fin 4)) (v : V) (y : Fin 4) (hy : ∀ u, G.Adj v u → c u ≠ y) (w : V) :
    recolour G c v y hy w = Function.update c v y w :=
  rfl

end TextSteps

open TextSteps

/-- Short v3.90 l. 147-148, after the list (the hypothesis of [BFHR25, Thm. 1.3], class (ii)): for every
`2`-degenerate graph, "such a graph has a vertex of degree at most $2$, and with four colours such a vertex can always
be recoloured" — a recolouring is an edge of `recolGraph G 4` that changes only `v`. -/
theorem intro_low_degree_recolour_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hd : IsDegenerate G 2) :
    (∃ v, G.degree v ≤ 2) ∧ ∀ (c : G.Coloring (Fin 4)) (v : V), G.degree v ≤ 2 →
      ∃ c' : G.Coloring (Fin 4), (recolGraph G 4).Adj c c' ∧ ∀ w, w ≠ v → c' w = c w := by
  refine ⟨exists_degree_le G hd, fun c v hv => ?_⟩
  obtain ⟨y, hyv, hy⟩ := exists_free_colour G c v hv
  have hrest : ∀ w, w ≠ v → recolour G c v y hy w = c w := fun w hw => by
    rw [recolour_apply, Function.update_of_ne hw]
  refine ⟨recolour G c v y hy, ⟨v, ?_, fun w hw => (hrest w hw).symm⟩, hrest⟩
  rw [recolour_apply, Function.update_self]
  exact hyv.symm

end Cereceda
