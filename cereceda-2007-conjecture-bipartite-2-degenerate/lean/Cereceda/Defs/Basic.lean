/-
Cereceda/Defs/Basic.lean — graph-level definitions for the paper
"The Cereceda (2007) conjecture holds for bipartite 2-degenerate graphs" (Dave Goel), short version v3.90
(short_v3.90.tex; statement numbers and line numbers as in v3.90).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: every definition here is read by the reviewers against the paper.
Colours are `Fin k`; the paper's colours `0 < 1 < 2 < 3` are `Fin 4`.
-/
import Mathlib

namespace Cereceda

open Finset

section Graph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The `k`-recolouring graph `R_k(G)` (paper, Section 1): its vertices are the proper `k`-colourings of `G`
(Mathlib's `G.Coloring (Fin k)`); two colourings are adjacent if they differ at exactly one vertex. -/
def recolGraph (G : SimpleGraph V) (k : ℕ) : SimpleGraph (G.Coloring (Fin k)) where
  Adj c c' := ∃ v, c v ≠ c' v ∧ ∀ w, w ≠ v → c w = c' w
  symm := ⟨fun _ _ ⟨v, hv, hw⟩ => ⟨v, hv.symm, fun w hwv => (hw w hwv).symm⟩⟩
  loopless := ⟨fun _ ⟨_, hv, _⟩ => hv rfl⟩

/-- `G` is `d`-degenerate (paper, v3.90 l. 38-39: "each of its non-empty subgraphs has a vertex of degree at most `d`"),
stated for the
induced subgraph on every nonempty vertex set `s`: some `v ∈ s` has at most `d` neighbours in `s`.
(`Statements.degenerate_iff_subgraph` proves that this equals the form for every non-empty subgraph.) -/
def IsDegenerate (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ s : Finset V, s.Nonempty → ∃ v ∈ s, (s.filter (G.Adj v)).card ≤ d

/-- An order `v_1, …, v_n` of `V`, given as a bijection `ρ : V ≃ Fin n` (`ρ v = i - 1` for `v = v_i`).
The later neighbours (out-neighbours, paper Section 2) of `v`: the neighbours `u` of `v` with `ρ v < ρ u`. -/
def laterNbrs (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n) (v : V) : Finset V :=
  univ.filter (fun u => G.Adj v u ∧ ρ v < ρ u)

/-- The order `ρ` gives every vertex at most `d` later neighbours (paper Section 2, with `d = 2`). -/
def IsDegOrder (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) {n : ℕ} (ρ : V ≃ Fin n) : Prop :=
  ∀ v, (laterNbrs G ρ v).card ≤ d

/-- An arc goes from a vertex to each of its out-neighbours (later neighbours) (paper Section 2). -/
def Arc (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) (u v : V) : Prop :=
  G.Adj u v ∧ ρ u < ρ v

open Classical in
/-- Definition 2.1 (cones). For `w = v_t`, the cone `C_t` is the set of vertices `v_j`, `j ≤ t`, from which `v_t`
can be reached along arcs inside `{v_1, …, v_t}`. -/
noncomputable def cone (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) (w : V) : Finset V :=
  univ.filter (fun u => ρ u ≤ ρ w ∧
    Relation.ReflTransGen (fun a b => Arc G ρ a b ∧ ρ a ≤ ρ w ∧ ρ b ≤ ρ w) u w)

end Graph

section Moves

variable {W : Type} [Fintype W] [DecidableEq W]

/-- `c` is a proper colouring of `H` (adjacent vertices get different colours). -/
def IsProperFn {α : Type} (H : SimpleGraph W) (c : W → α) : Prop :=
  ∀ u v, H.Adj u v → c u ≠ c v

/-- A move `m = (v, y)` from the colouring `c` (paper Def 2.2, v3.90 l. 265: "a move gives one vertex another colour of its
list, one that none of its neighbours has"): the colour really changes, the new colour `y` is allowed at `v`
(`A v` is the list of `v`), and no neighbour of `v` in `H` has the colour `y` at that time. -/
def LegalMove (H : SimpleGraph W) (A : W → Finset (Fin 4)) (c : W → Fin 4) (m : W × Fin 4) : Prop :=
  m.2 ≠ c m.1 ∧ m.2 ∈ A m.1 ∧ ∀ u, H.Adj m.1 u → c u ≠ m.2

/-- `IsSeq H A c ms c'`: the list of moves `ms`, applied in order from `c`, is a sequence (every move legal at its time)
and it ends at `c'`. -/
def IsSeq (H : SimpleGraph W) (A : W → Finset (Fin 4)) : (W → Fin 4) → List (W × Fin 4) → (W → Fin 4) → Prop
  | c, [], c' => c' = c
  | c, m :: ms, c' => LegalMove H A c m ∧ IsSeq H A (Function.update c m.1 m.2) ms c'

/-- The colouring reached from `c` by applying the moves `ms` in order. -/
def applyMoves (c : W → Fin 4) (ms : List (W × Fin 4)) : W → Fin 4 :=
  ms.foldl (fun c m => Function.update c m.1 m.2) c

/-- The number of moves of the vertex `v` in the list of moves `ms`. -/
def movesOf (ms : List (W × Fin 4)) (v : W) : ℕ :=
  ms.countP (fun m => m.1 = v)

/-- The residue of a colour (paper, before Lemma 2.4: the residue of the colours `1, 2, 3` is `1, 2, 0`). -/
def res (y : Fin 4) : ZMod 3 := (y.val : ZMod 3)

/-- A height of the colouring `c` on the graph `T` (paper, before Lemma 2.4): an integer function `h` with
`h v ≡ res (c v) (mod 3)` and `|h u - h v| = 1` on every edge. -/
def IsHeight (T : SimpleGraph W) (c : W → Fin 4) (h : W → ℤ) : Prop :=
  (∀ v, ((h v : ℤ) : ZMod 3) = res (c v)) ∧ ∀ u v, T.Adj u v → |h u - h v| = 1

/-- The allowed colours of Lemma 2.4 on a tree with root `r`: `P` at `r`, the colours `1, 2, 3` elsewhere. -/
def treeLists (r : W) (P : Finset (Fin 4)) (v : W) : Finset (Fin 4) :=
  if v = r then P else {1, 2, 3}

end Moves

end Cereceda
