/-
Cereceda/Setting/DegeneracyForm.lean — degeneracy facts and the two equivalent forms of Conjecture 1.1 (short v3.90 l. 64-78).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Degeneracy

namespace Cereceda

open Finset

namespace DegeneracyForm

variable {V : Type} [DecidableEq V] (G : SimpleGraph V)

/-- The colouring obtained from `c` by giving the vertex `v` the colour `y` (proper since `G` has no edges). -/
def recolourAt {k : ℕ} (h : ∀ u v, ¬ G.Adj u v) (c : G.Coloring (Fin k)) (v : V) (y : Fin k) :
    G.Coloring (Fin k) :=
  SimpleGraph.Coloring.mk (Function.update (⇑c) v y) (fun hadj => absurd hadj (h _ _))

theorem recolourAt_apply {k : ℕ} (h : ∀ u v, ¬ G.Adj u v) (c : G.Coloring (Fin k)) (v : V) (y : Fin k) (w : V) :
    recolourAt G h c v y w = Function.update (⇑c) v y w := rfl

/-- Recolouring one vertex `v` to a new colour is an edge of `R_k(G)`. -/
theorem adj_recolourAt {k : ℕ} (h : ∀ u v, ¬ G.Adj u v) (c : G.Coloring (Fin k)) (v : V) (y : Fin k)
    (hy : c v ≠ y) : (recolGraph G k).Adj c (recolourAt G h c v y) := by
  refine ⟨v, ?_, fun w hwv => ?_⟩
  · rw [recolourAt_apply, Function.update_self]
    exact hy
  · rw [recolourAt_apply, Function.update_of_ne hwv]

/-- After recolouring `v` to `c' v`, the vertices where the colouring differs from `c'` are those where `c` did,
minus `v`. -/
theorem diff_recolourAt [Fintype V] {k : ℕ} (h : ∀ u v, ¬ G.Adj u v) (c c' : G.Coloring (Fin k)) (v : V) :
    univ.filter (fun w => recolourAt G h c v (c' v) w ≠ c' w) =
      (univ.filter (fun w => c w ≠ c' w)).erase v := by
  ext w
  rw [mem_filter, mem_erase, mem_filter, recolourAt_apply]
  by_cases hwv : w = v
  · subst hwv
    simp
  · rw [Function.update_of_ne hwv]
    simp [hwv]

/-- In `R_k(G)` for an edgeless `G`, the distance between two colourings is at most the number of vertices where
they differ: change the differing vertices one at a time. -/
theorem edist_le_card_diff [Fintype V] {k : ℕ} (h : ∀ u v, ¬ G.Adj u v) :
    ∀ (m : ℕ) (c c' : G.Coloring (Fin k)), (univ.filter (fun w => c w ≠ c' w)).card = m →
      (recolGraph G k).edist c c' ≤ m := by
  intro m
  induction m with
  | zero =>
    intro c c' hm
    have hcc : c = c' := by
      refine RelHom.ext fun w => ?_
      by_contra hw
      have hmem : w ∈ univ.filter (fun w => c w ≠ c' w) := by simpa using hw
      rw [card_eq_zero.mp hm] at hmem
      exact absurd hmem (notMem_empty w)
    rw [hcc, SimpleGraph.edist_self]
    rfl
  | succ m ih =>
    intro c c' hm
    obtain ⟨v, hv⟩ : (univ.filter (fun w => c w ≠ c' w)).Nonempty := card_pos.mp (by omega)
    have hcv : c v ≠ c' v := (mem_filter.mp hv).2
    have hstep : (recolGraph G k).edist c (recolourAt G h c v (c' v)) = 1 :=
      SimpleGraph.edist_eq_one_iff_adj.mpr (adj_recolourAt G h c v (c' v) hcv)
    have hrest : (recolGraph G k).edist (recolourAt G h c v (c' v)) c' ≤ m := by
      apply ih
      rw [diff_recolourAt, card_erase_of_mem hv, hm]
      rfl
    calc (recolGraph G k).edist c c'
        ≤ (recolGraph G k).edist c (recolourAt G h c v (c' v)) +
            (recolGraph G k).edist (recolourAt G h c v (c' v)) c' := SimpleGraph.edist_triangle
      _ ≤ 1 + (m : ℕ∞) := by rw [hstep]; exact add_le_add le_rfl hrest
      _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; exact add_comm _ _

/-- For `d ≥ 1` and `k ≥ d + 2`, the right-hand form of Conjecture 1.1 at degeneracy `d'` gives a constant for every
`d'` (a trivial one when `d'` is out of the range `1 ≤ d' ≤ d`). -/
theorem exists_const_each (d k : ℕ) (hk : d + 2 ≤ k)
    (h : ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], degeneracy G = d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) :
    ∀ d' : ℕ, ∃ C : ℕ, 1 ≤ d' → d' ≤ d → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], degeneracy G = d' →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  intro d'
  by_cases hd' : 1 ≤ d' ∧ d' ≤ d
  · obtain ⟨C, hC⟩ := h d' hd'.1 k (by omega)
    exact ⟨C, fun _ _ => hC⟩
  · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hd'⟩

/-- `exists_const_each` for the two forms restricted to graphs with at least one edge. -/
theorem exists_const_each_edge (d k : ℕ) (hk : d + 2 ≤ k)
    (h : ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], (∃ u v, G.Adj u v) → degeneracy G = d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) :
    ∀ d' : ℕ, ∃ C : ℕ, 1 ≤ d' → d' ≤ d → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], (∃ u v, G.Adj u v) → degeneracy G = d' →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞) := by
  intro d'
  by_cases hd' : 1 ≤ d' ∧ d' ≤ d
  · obtain ⟨C, hC⟩ := h d' hd'.1 k (by omega)
    exact ⟨C, fun _ _ => hC⟩
  · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hd'⟩

/-- `n ≤ C n²` when `1 ≤ C`. -/
theorem card_le_mul_sq (n C : ℕ) (hC : 1 ≤ C) : n ≤ C * n ^ 2 := by
  have h1 : n ≤ n ^ 2 := by rw [sq]; exact Nat.le_mul_self n
  calc n ≤ n ^ 2 := h1
    _ = 1 * n ^ 2 := (one_mul _).symm
    _ ≤ C * n ^ 2 := Nat.mul_le_mul_right _ hC

end DegeneracyForm

/-- `G` is `n`-degenerate, `n` its number of vertices: in any nonempty vertex set every vertex has fewer than `n`
neighbours. This makes the set in the definition of the degeneracy (v3.90 l. 64-65, "The degeneracy of a graph is
the least `d` for which it is `d`-degenerate") nonempty, so the least `d` exists. -/
theorem isDegenerate_card {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsDegenerate G (Fintype.card V) := by
  intro s hs
  obtain ⟨v, hv⟩ := hs
  exact ⟨v, hv, (card_filter_le _ _).trans (card_le_univ s)⟩

/-- A `d`-degenerate graph is `d'`-degenerate for every `d' ≥ d` (used with v3.90 l. 64-65: "The degeneracy of a
graph is the least `d` for which it is `d`-degenerate"). -/
theorem isDegenerate_mono {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {d d' : ℕ}
    (h : IsDegenerate G d) (hle : d ≤ d') : IsDegenerate G d' := by
  intro s hs
  obtain ⟨v, hv, hcard⟩ := h s hs
  exact ⟨v, hv, hcard.trans hle⟩

/-- v3.90 l. 64-65: "The degeneracy of a graph is the least `d` for which it is `d`-degenerate" — the graph is
`d`-degenerate for `d` = its degeneracy (the least such `d` exists). -/
theorem isDegenerate_degeneracy {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsDegenerate G (degeneracy G) :=
  Nat.sInf_mem (s := {d | IsDegenerate G d}) ⟨Fintype.card V, isDegenerate_card G⟩

/-- v3.90 l. 64-65: "The degeneracy of a graph is the least `d` for which it is `d`-degenerate" — it is at most every
`d` for which the graph is `d`-degenerate (the upper half of l. 77, "a `d`-degenerate graph with an edge has degeneracy
between `1` and `d`"). -/
theorem degeneracy_le {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (h : IsDegenerate G d) :
    degeneracy G ≤ d :=
  Nat.sInf_le h

/-- A graph of degeneracy `0` has no edges (so a graph with an edge has degeneracy at least `1`: the lower half of
v3.90 l. 77, "a `d`-degenerate graph with an edge has degeneracy between `1` and `d`"). Proof: the set `{u, v}` has a
vertex with no neighbour in it. -/
theorem not_adj_of_degeneracy_eq_zero {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : degeneracy G = 0) (u v : V) : ¬ G.Adj u v := by
  intro huv
  have h0 : IsDegenerate G 0 := h ▸ isDegenerate_degeneracy G
  obtain ⟨w, hw, hcard⟩ := h0 {u, v} (insert_nonempty u {v})
  have hempty := card_eq_zero.mp (Nat.le_zero.mp hcard)
  rcases mem_insert.mp hw with rfl | hw'
  · have hmem : v ∈ ({w, v} : Finset V).filter (G.Adj w) := by simp [huv]
    rw [hempty] at hmem
    exact notMem_empty v hmem
  · rw [mem_singleton.mp hw'] at hempty
    have hmem : u ∈ ({u, v} : Finset V).filter (G.Adj v) := by simp [huv.symm]
    rw [hempty] at hmem
    exact notMem_empty u hmem

/-- For a graph without edges, `diam R_k(G) ≤ n` (every function is a proper colouring; change the differing
vertices one at a time). This is the case of degeneracy `0`, which the paper leaves out ("For graphs with at least one
edge, the two forms are equivalent", v3.90 l. 76-77) and which the Lean-only all-graphs equivalence `conj_forms_equiv`
needs. Proved directly, no cited result. -/
theorem ediam_le_card_of_edgeless {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ)
    (h : ∀ u v, ¬ G.Adj u v) : (recolGraph G k).ediam ≤ (Fintype.card V : ℕ∞) := by
  refine SimpleGraph.ediam_le_of_edist_le fun c c' => ?_
  refine (DegeneracyForm.edist_le_card_diff G h _ c c' rfl).trans ?_
  exact_mod_cast card_le_univ _

/-- Beyond the paper's sentence (v3.90 l. 76-78 claims the equivalence for graphs with at least one edge:
`conj_forms_equiv_edge`): the two forms are equivalent for all graphs. The left side is Conjecture 1.1 as stated
(l. 72-75, the body of `CerecedaConjecture`), the right side is Cereceda's form with `degeneracy G = d`.
Left to right: degeneracy `d` gives `d`-degenerate. Right to left: a `d`-degenerate `G` has degeneracy `d' ≤ d`; for
`d' ≥ 1` use the constant of the right side for `(d', k)` (`k ≥ d + 2 ≥ d' + 2`); the constant for `d` is `1` plus
the sum of these constants for `d' = 1, …, d`.
For all graphs Lean also needs the edgeless case (the reason the paper restricts its sentence to graphs with an edge): a
`d`-degenerate graph can have degeneracy `0` (no edges), and the right side says nothing about it (it needs `d ≥ 1`). There
`ediam_le_card_of_edgeless` gives `diam R_k(G) ≤ n ≤ n² ≤ C n²` (as `C ≥ 1`). -/
theorem conj_forms_equiv :
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], IsDegenerate G d → (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) ↔
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], degeneracy G = d → (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) := by
  constructor
  · intro hL d hd k hk
    obtain ⟨C, hC⟩ := hL d hd k hk
    refine ⟨C, fun V _ _ G _ hdeg => hC V G ?_⟩
    exact hdeg ▸ isDegenerate_degeneracy G
  · intro hR d hd k hk
    choose Cf hCf using DegeneracyForm.exists_const_each d k hk hR
    refine ⟨1 + ∑ d' ∈ range (d + 1), Cf d', fun V _ _ G _ hG => ?_⟩
    have hle : degeneracy G ≤ d := degeneracy_le G hG
    rcases Nat.eq_zero_or_pos (degeneracy G) with h0 | hpos
    · refine (ediam_le_card_of_edgeless G k (not_adj_of_degeneracy_eq_zero G h0)).trans ?_
      exact_mod_cast DegeneracyForm.card_le_mul_sq _ _ (by omega)
    · refine (hCf (degeneracy G) hpos hle V G rfl).trans ?_
      have hsum : Cf (degeneracy G) ≤ ∑ d' ∈ range (d + 1), Cf d' :=
        single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega))
      exact_mod_cast Nat.mul_le_mul_right _ (by omega)

/-- v3.90 l. 77: "a `d`-degenerate graph with an edge has degeneracy between `1` and `d`" (degeneracy `0` means no
edges). -/
theorem degeneracy_between {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (he : ∃ u v, G.Adj u v) (h : IsDegenerate G d) : 1 ≤ degeneracy G ∧ degeneracy G ≤ d := by
  refine ⟨?_, degeneracy_le G h⟩
  rcases Nat.eq_zero_or_pos (degeneracy G) with h0 | h0
  · obtain ⟨u, v, huv⟩ := he
    exact absurd huv (not_adj_of_degeneracy_eq_zero G h0 u v)
  · exact h0

/-- v3.90 l. 76-78: "Cereceda states it with `d` equal to the degeneracy of `G`. For graphs with at least one edge, the
two forms are equivalent: a `d`-degenerate graph with an edge has degeneracy between `1` and `d`, so `C` can be taken as
the largest of the constants that Cereceda's form gives for these degeneracies and the same `k`." Both forms restricted
to graphs with at least one edge. Left to right: degeneracy `d` gives `d`-degenerate. Right to left, as the paper: `degeneracy_between`, and `C` = the largest of
the constants for `(d', k)`, `1 ≤ d' ≤ d` (each exists as `k ≥ d + 2 ≥ d' + 2`). -/
theorem conj_forms_equiv_edge :
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (∃ u v, G.Adj u v) → IsDegenerate G d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) ↔
    (∀ d : ℕ, 1 ≤ d → ∀ k : ℕ, d + 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (∃ u v, G.Adj u v) → degeneracy G = d →
        (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)) := by
  constructor
  · intro hL d hd k hk
    obtain ⟨C, hC⟩ := hL d hd k hk
    exact ⟨C, fun V _ _ G _ he hdeg => hC V G he (hdeg ▸ isDegenerate_degeneracy G)⟩
  · intro hR d hd k hk
    choose Cf hCf using DegeneracyForm.exists_const_each_edge d k hk hR
    refine ⟨(Icc 1 d).sup Cf, fun V _ _ G _ he hG => ?_⟩
    obtain ⟨hpos, hle⟩ := degeneracy_between G he hG
    refine (hCf (degeneracy G) hpos hle V G he rfl).trans ?_
    have hmax : Cf (degeneracy G) ≤ (Icc 1 d).sup Cf := le_sup (f := Cf) (mem_Icc.mpr ⟨hpos, hle⟩)
    exact_mod_cast Nat.mul_le_mul_right _ hmax

end Cereceda
