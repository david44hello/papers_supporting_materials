/-
Cereceda/Defs/Instance.lean — instances (paper Definition 2.2), greedy colourings, classes, cone instances.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against paper Definition 2.2 (v3.90 l. 251-267) and the proof of Lemma 2.5 (v3.90 l. 358-388,
with the cone instances at l. 269-272).
-/
import Cereceda.Defs.Basic

namespace Cereceda

open Finset

/-- The arcs of an instance (paper Def 2.2, the part that does not depend on lists or colours): vertices `W` in an
instance order (`rank`, injective), the sink first; every vertex `v` has a set `out v` (`N⁺(v)`) of at most two
out-neighbours among the vertices before it; the sink has none. -/
structure Skeleton (W : Type) [Fintype W] [DecidableEq W] where
  sink : W
  rank : W → ℕ
  rank_inj : Function.Injective rank
  sink_first : ∀ v, rank sink ≤ rank v
  out : W → Finset W
  out_before : ∀ v, ∀ u ∈ out v, rank u < rank v
  out_card : ∀ v, (out v).card ≤ 2
  sink_out : out sink = ∅

/-- An instance (paper Def 2.2): a skeleton with lists `L v ⊆ {0,1,2,3}`, `|L v| ≥ |N⁺(v)| + 2`; the sink has the
list `{g, x}` with `g < x` (the main case is `g = 0`). -/
structure Instance (W : Type) [Fintype W] [DecidableEq W] extends Skeleton W where
  L : W → Finset (Fin 4)
  L_card : ∀ v, (out v).card + 2 ≤ (L v).card
  g : Fin 4
  x : Fin 4
  g_lt_x : g < x
  L_sink : L sink = {g, x}

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The graph of a skeleton (paper Def 2.2): the edges are the pairs `{v, u}` with `u ∈ N⁺(v)`. -/
def Skeleton.graph (S : Skeleton W) : SimpleGraph W :=
  SimpleGraph.fromRel (fun v u => u ∈ S.out v)

/-- A root vertex: a vertex other than the sink without out-neighbours (a single-sink instance, paper Def 2.2, has
none: `Skeleton.IsSingleSink`). -/
def Skeleton.IsRoot (S : Skeleton W) (v : W) : Prop :=
  v ≠ S.sink ∧ S.out v = ∅

/-- The skeleton has no root vertices. -/
def Skeleton.NoRoots (S : Skeleton W) : Prop :=
  ∀ v, ¬ S.IsRoot v

/-- Single-sink (paper Def 2.2, v3.90 l. 256): the sink is the only vertex without out-neighbours (the sink has none,
field `sink_out`). The same as `NoRoots`: `def_2_2_singleSink_iff` in Statements.lean. -/
def Skeleton.IsSingleSink (S : Skeleton W) : Prop :=
  ∀ v, S.out v = ∅ → v = S.sink

/-- `y` is the least colour of the list `L` that is not in `used`. -/
def IsLeastFree (L used : Finset (Fin 4)) (y : Fin 4) : Prop :=
  y ∈ L ∧ y ∉ used ∧ ∀ z ∈ L, z < y → z ∈ used

/-- The greedy colouring with sink colour `c0` (paper Def 2.2): `c sink = c0`, and every other vertex takes the
least colour of its list that none of its out-neighbours has. `α` is `IsGreedy I I.x`, `β` is `IsGreedy I I.g`. -/
def Instance.IsGreedy (I : Instance W) (c0 : Fin 4) (c : W → Fin 4) : Prop :=
  c I.sink = c0 ∧ ∀ v, v ≠ I.sink → IsLeastFree (I.L v) ((I.out v).image c) (c v)

/-- A sequence of the instance (paper Def 2.2): moves along the instance graph within the lists. -/
def Instance.IsSeq (I : Instance W) (c : W → Fin 4) (ms : List (W × Fin 4)) (c' : W → Fin 4) : Prop :=
  Cereceda.IsSeq I.graph I.L c ms c'

/-- The forest `F` of the proof of Lemma 2.3 (v3.90 l. 310-319) for a colouring `c`, as a graph on all of
`W`: the edges of the instance graph whose two ends are not on `0`. The tree `T` of that proof is the set of vertices
reachable from the sink in this graph. -/
def Instance.fGraph (I : Instance W) (c : W → Fin 4) : SimpleGraph W where
  Adj u v := I.graph.Adj u v ∧ c u ≠ 0 ∧ c v ≠ 0
  symm := ⟨fun _ _ ⟨h, hu, hv⟩ => ⟨h.symm, hv, hu⟩⟩
  loopless := ⟨fun _ ⟨h, _, _⟩ => I.graph.irrefl h⟩

/-- A class of instances "closed under changing the lists" (paper Lemma 2.5, v3.90 l. 351-352): membership depends
only on the skeleton (vertices, instance order, out-neighbours), not on the lists or the colours: a predicate on
skeletons. -/
abbrev InstanceClass : Type 1 :=
  ∀ (W : Type) [Fintype W] [DecidableEq W], Skeleton W → Prop

section Cone

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertices of the cone of `w`, as a type. -/
abbrev ConeV (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) (w : V) : Type :=
  {u // u ∈ cone G ρ w}

omit [DecidableEq V] in
theorem mem_cone_self (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) (w : V) : w ∈ cone G ρ w := by
  classical
  simp only [cone, mem_filter, mem_univ, true_and]
  exact ⟨le_rfl, Relation.ReflTransGen.refl⟩

omit [DecidableEq V] in
theorem le_of_mem_cone {G : SimpleGraph V} {n : ℕ} {ρ : V ≃ Fin n} {w u : V} (hu : u ∈ cone G ρ w) :
    ρ u ≤ ρ w := by
  classical
  simp only [cone, mem_filter, mem_univ, true_and] at hu
  exact hu.1

/-- The skeleton of the instance on the cone `C_t` with sink `v_t = w` (used in the proof of Lemma 2.5), short v3.90
l. 269-271: "the instance on `C_t` has the vertices of `C_t` in decreasing order of index (the reverse of the
degeneracy ordering) as its instance order, so its sink is `v_t`; the out-neighbours of a vertex `v ∈ C_t` in the
instance are the vertices of `N⁺_G(v) ∩ C_t`". In Lean: `rank u = ρ w - ρ u` (decreasing index, `v_t` first), and
`out u` is the set of the vertices `v` of `C_t` with `G.Adj u v` and `ρ u < ρ v` (the later neighbours of `u`, i.e.
`N⁺_G(u)`, that lie in `C_t`). Only the data fields (`sink`, `rank`, `out`) are trust surface; the other fields are
proofs. -/
noncomputable def coneSkeleton (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n)
    (hρ : IsDegOrder G 2 ρ) (w : V) : Skeleton (ConeV G ρ w) where
  sink := ⟨w, mem_cone_self G ρ w⟩
  rank u := (ρ w).val - (ρ u.1).val
  rank_inj := by
    intro u u' huu
    simp only at huu
    have h1 := le_of_mem_cone u.2
    have h2 := le_of_mem_cone u'.2
    have h3 : (ρ u.1).val = (ρ u'.1).val := by
      simp only [Fin.le_iff_val_le_val] at h1 h2
      omega
    exact Subtype.ext (ρ.injective (Fin.ext h3))
  sink_first := fun _ => by simp
  out u := (cone G ρ w).attach.filter (fun v => G.Adj u.1 v.1 ∧ ρ u.1 < ρ v.1)
  out_before := by
    intro u v hv
    simp only [mem_filter, mem_attach, true_and] at hv
    have h1 := le_of_mem_cone v.2
    simp only [Fin.le_iff_val_le_val, Fin.lt_def] at h1 hv
    omega
  out_card := by
    intro u
    refine le_trans ?_ (hρ u.1)
    refine Finset.card_le_card_of_injOn (fun v => v.1) ?_ ?_
    · intro v hv
      simp only [coe_filter, mem_attach, true_and, Set.mem_ofPred_eq] at hv
      simp only [laterNbrs, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
      exact hv
    · intro v _ v' _ h
      exact Subtype.ext h
  sink_out := by
    ext v
    simp only [mem_filter, mem_attach, true_and, Finset.notMem_empty, iff_false, not_and]
    intro _ hlt
    exact absurd (le_of_mem_cone v.2) (not_le.mpr hlt)

end Cone

end Cereceda
