/-
Cereceda/Intro/Examples.lean — `K_{d+1}` (short v3.90 l. 67-68: `R_{d+1}(K_{d+1})` is disconnected;
`intro_complete_disconnected_proved`), `K_{2,m}` (degeneracy, edge count), trees (`tree_isDegenerate`), and two
results of an earlier proof route
of Section 1 (not in v3.90): `K_{2,m}` has average degree above `4 − ε` (`intro_K2m_proved`), and trees, even
cycles and grids are bipartite and `2`-degenerate (`intro_class_examples_proved`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Setting.Degeneracy

namespace Cereceda

open Finset

namespace Examples

section Potential

variable {V : Type} [Fintype V]

/-- If every vertex `v` has at most `d` neighbours `u` with `f u ≤ f v`, then `G` is `d`-degenerate: in a nonempty
set, a vertex with the largest `f` has at most `d` neighbours in the set. -/
theorem isDegenerate_of_potential (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (f : V → ℕ)
    (h : ∀ v, (univ.filter (fun u => G.Adj v u ∧ f u ≤ f v)).card ≤ d) : IsDegenerate G d := by
  intro s hs
  obtain ⟨v, hv, hmax⟩ := s.exists_max_image f hs
  refine ⟨v, hv, le_trans (card_le_card ?_) (h v)⟩
  intro u hu
  rw [mem_filter] at hu
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hu.2, hmax u hu.1⟩

/-- A graph in which every vertex has at most `d` neighbours is `d`-degenerate. -/
theorem isDegenerate_of_card_le (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (h : ∀ v, (univ.filter (G.Adj v)).card ≤ d) : IsDegenerate G d :=
  isDegenerate_of_potential G d (fun _ => 0) fun v =>
    le_trans (card_le_card fun u hu => by
      simp only [mem_filter] at hu ⊢
      exact ⟨hu.1, hu.2.1⟩) (h v)

omit [Fintype V] in
theorem isDegenerate_mono (G : SimpleGraph V) [DecidableRel G.Adj] {d d' : ℕ} (hdd : d ≤ d')
    (h : IsDegenerate G d) : IsDegenerate G d' := fun s hs =>
  let ⟨v, hv, hc⟩ := h s hs
  ⟨v, hv, hc.trans hdd⟩

end Potential

/-! ### `K_{d+1}` -/

theorem top_isDegenerate (d : ℕ) : IsDegenerate (⊤ : SimpleGraph (Fin (d + 1))) d :=
  isDegenerate_of_card_le _ d fun v => by
    have hset : univ.filter ((⊤ : SimpleGraph (Fin (d + 1))).Adj v) = univ.erase v := by
      ext u
      simp [ne_comm]
    rw [hset, card_erase_of_mem (mem_univ v)]
    simp

/-- A proper `(d+1)`-colouring of `K_{d+1}` is injective, hence onto. -/
theorem top_coloring_surjective {d : ℕ} (c : (⊤ : SimpleGraph (Fin (d + 1))).Coloring (Fin (d + 1))) :
    Function.Surjective c := by
  apply Finite.surjective_of_injective
  intro a b hab
  by_contra hne
  exact c.valid ((SimpleGraph.top_adj a b).mpr hne) hab

/-- `R_{d+1}(K_{d+1})` has no edges: if `c'` differs from `c` only at `v`, the colour `c' v` is `c w` for some
`w ≠ v`, and then `c' w = c w = c' v` on the edge `w v`. -/
theorem recol_top_not_adj {d : ℕ} (c c' : (⊤ : SimpleGraph (Fin (d + 1))).Coloring (Fin (d + 1))) :
    ¬ (recolGraph (⊤ : SimpleGraph (Fin (d + 1))) (d + 1)).Adj c c' := by
  rintro ⟨v, hv, hw⟩
  obtain ⟨w, hw'⟩ := top_coloring_surjective c (c' v)
  have hwv : w ≠ v := by
    rintro rfl
    exact hv hw'
  exact c'.valid ((SimpleGraph.top_adj w v).mpr hwv) ((hw w hwv).symm.trans hw')

/-- The colouring of `K_{d+1}` by a permutation of the colours. -/
def topColoring {d : ℕ} (e : Equiv.Perm (Fin (d + 1))) :
    (⊤ : SimpleGraph (Fin (d + 1))).Coloring (Fin (d + 1)) :=
  SimpleGraph.Coloring.mk e fun {u v} h heq => ((SimpleGraph.top_adj u v).mp h) (e.injective heq)

theorem eq_of_reachable_of_no_adj {α : Type} {H : SimpleGraph α} (hno : ∀ a b, ¬ H.Adj a b) {a b : α}
    (h : H.Reachable a b) : a = b := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hno _ _)

/-! ### `K_{2,m}` -/

theorem K2m_isDegenerate (m : ℕ) [DecidableRel (completeBipartiteGraph (Fin 2) (Fin m)).Adj] :
    IsDegenerate (completeBipartiteGraph (Fin 2) (Fin m)) 2 := by
  apply isDegenerate_of_potential _ 2 (fun x => Sum.elim (fun _ => 0) (fun _ => 1) x)
  intro v
  cases v with
  | inl i =>
    refine le_trans (card_le_card (t := ∅) ?_) (by simp)
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    cases u <;> simp at hu
  | inr j =>
    refine le_trans (card_le_card (t := univ.map Function.Embedding.inl) ?_) (by simp)
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    cases u with
    | inl i => simp
    | inr j' => simp at hu

theorem K2m_card_edges (m : ℕ) [Fintype (completeBipartiteGraph (Fin 2) (Fin m)).edgeSet] :
    (completeBipartiteGraph (Fin 2) (Fin m)).edgeFinset.card = 2 * m := by
  have h := SimpleGraph.encard_edgeSet_completeBipartiteGraph (W₁ := Fin 2) (W₂ := Fin m)
  rw [← SimpleGraph.coe_edgeFinset, Set.encard_coe_eq_coe_finsetCard] at h
  simp at h
  exact_mod_cast h

/-! ### Trees, even cycles, grids -/

section Tree

variable {V : Type} [Fintype V] [DecidableEq V]

/-- In a tree with root `r`, a vertex `v` has at most one neighbour `u` with `dist r u ≤ dist r v`: such a `u` is
nearer to `r`, so it lies on the shortest path from `r` to `v`, so it is the vertex before `v` on that path. -/
theorem tree_parent_unique {T : SimpleGraph V} [DecidableRel T.Adj] (hT : T.IsTree) (r v : V) :
    (univ.filter (fun u => T.Adj v u ∧ T.dist r u ≤ T.dist r v)).card ≤ 1 := by
  obtain ⟨p, hp, hplen⟩ := (hT.connected r v).exists_path_of_dist
  refine le_trans (card_le_card (t := {p.penultimate}) ?_) (by simp)
  intro w hw
  simp only [mem_filter, mem_univ, true_and] at hw
  obtain ⟨hvw, hle⟩ := hw
  have hlt : T.dist r w < T.dist r v := lt_of_le_of_ne hle (hT.dist_ne_of_adj r hvw).symm
  rw [mem_singleton]
  apply hT.isAcyclic.eq_penultimate_of_adj_end hp hvw
  by_contra hwp
  obtain ⟨q, hq, hqlen⟩ := (hT.connected r w).exists_path_of_dist
  have hvq : v ∈ q.support :=
    hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp hvw.symm hwp
  have h1 := SimpleGraph.dist_le (q.takeUntil v hvq)
  have h2 := q.length_takeUntil_le_length hvq
  omega

/-- A tree is `1`-degenerate (potential: distance from a root). -/
theorem tree_isDegenerate {T : SimpleGraph V} [DecidableRel T.Adj] (hT : T.IsTree) : IsDegenerate T 1 := by
  obtain ⟨r⟩ := hT.connected.nonempty
  exact isDegenerate_of_potential T 1 (T.dist r) (tree_parent_unique hT r)

end Tree

/-- Every vertex of a cycle graph has at most `2` neighbours. -/
theorem cycle_isDegenerate (n : ℕ) [DecidableRel (SimpleGraph.cycleGraph n).Adj] :
    IsDegenerate (SimpleGraph.cycleGraph n) 2 := by
  apply isDegenerate_of_card_le
  intro v
  rcases n with _ | _ | k
  · exact v.elim0
  · refine le_trans (card_le_card (t := ∅) ?_) (by simp)
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    exact absurd hu SimpleGraph.cycleGraph_one_adj
  · refine le_trans (card_le_card (t := {v - 1, v + 1}) ?_) card_le_two
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    have hmem : u ∈ (SimpleGraph.cycleGraph (k + 2)).neighborSet v := hu
    rw [SimpleGraph.cycleGraph_neighborSet] at hmem
    simpa using hmem

/-- The grid `P_a □ P_b` is bipartite: colour `(i, j)` by the parity of `i + j`. -/
theorem grid_isBipartite (a b : ℕ) : (SimpleGraph.pathGraph a □ SimpleGraph.pathGraph b).IsBipartite :=
  ⟨SimpleGraph.Coloring.mk (fun x => (⟨(x.1.val + x.2.val) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) (by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ h heq
    simp only [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff] at h heq
    omega)⟩

/-- The grid `P_a □ P_b` is `2`-degenerate (potential `i + j`): the neighbours of `(i, j)` with a smaller or equal
potential are among `(i - 1, j)` and `(i, j - 1)`, told apart by whether the first coordinate changes. -/
theorem grid_isDegenerate (a b : ℕ) [DecidableRel (SimpleGraph.pathGraph a □ SimpleGraph.pathGraph b).Adj] :
    IsDegenerate (SimpleGraph.pathGraph a □ SimpleGraph.pathGraph b) 2 := by
  apply isDegenerate_of_potential _ 2 (fun x => x.1.val + x.2.val)
  intro v
  refine le_trans (card_le_card_of_injOn (t := (univ : Finset Bool)) (fun u => decide (u.1 = v.1))
    (fun _ _ => mem_coe.mpr (mem_univ _)) ?_) (by simp)
  obtain ⟨v1, v2⟩ := v
  rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy hxy
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, SimpleGraph.boxProd_adj,
    SimpleGraph.pathGraph_adj, Fin.ext_iff] at hx hy
  simp only [decide_eq_decide, Fin.ext_iff] at hxy
  simp only [Prod.mk.injEq, Fin.ext_iff]
  omega

end Examples

theorem intro_complete_disconnected_proved (d : ℕ) (hd : 1 ≤ d) :
    IsDegenerate (⊤ : SimpleGraph (Fin (d + 1))) d ∧
      ¬ (recolGraph (⊤ : SimpleGraph (Fin (d + 1))) (d + 1)).Connected := by
  refine ⟨Examples.top_isDegenerate d, fun hconn => ?_⟩
  let a : Fin (d + 1) := ⟨0, by omega⟩
  let b : Fin (d + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := fun h => absurd (congrArg Fin.val h) (by simp [a, b])
  have heq := Examples.eq_of_reachable_of_no_adj Examples.recol_top_not_adj
    (hconn.preconnected (Examples.topColoring 1) (Examples.topColoring (Equiv.swap a b)))
  have h0 := DFunLike.congr_fun heq a
  change (1 : Equiv.Perm (Fin (d + 1))) a = Equiv.swap a b a at h0
  rw [Equiv.Perm.one_apply, Equiv.swap_apply_left] at h0
  exact hab h0

open Classical in
theorem intro_K2m_proved (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, IsDegenerate (completeBipartiteGraph (Fin 2) (Fin m)) 2 ∧
      4 - ε < 2 * ((completeBipartiteGraph (Fin 2) (Fin m)).edgeFinset.card : ℝ) / (2 + m) := by
  refine ⟨⌈8 / ε⌉₊, Examples.K2m_isDegenerate _, ?_⟩
  rw [Examples.K2m_card_edges]
  have hm : 8 / ε ≤ (⌈8 / ε⌉₊ : ℝ) := Nat.le_ceil _
  have hm' : 8 ≤ (⌈8 / ε⌉₊ : ℝ) * ε := (div_le_iff₀ hε).mp hm
  rw [lt_div_iff₀ (by positivity)]
  push_cast
  nlinarith

open Classical in
theorem intro_class_examples_proved :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (T : SimpleGraph V), T.IsTree →
      T.IsBipartite ∧ IsDegenerate T 2) ∧
    (∀ m : ℕ, 2 ≤ m →
      (SimpleGraph.cycleGraph (2 * m)).IsBipartite ∧ IsDegenerate (SimpleGraph.cycleGraph (2 * m)) 2) ∧
    (∀ a b : ℕ, (SimpleGraph.pathGraph a □ SimpleGraph.pathGraph b).IsBipartite ∧
      IsDegenerate (SimpleGraph.pathGraph a □ SimpleGraph.pathGraph b) 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ T hT
    exact ⟨hT.isBipartite, Examples.isDegenerate_mono T (by norm_num) (Examples.tree_isDegenerate hT)⟩
  · intro m _
    exact ⟨SimpleGraph.IsBipartite.cycleGraph_of_even (even_two_mul m), Examples.cycle_isDegenerate _⟩
  · intro a b
    exact ⟨Examples.grid_isBipartite a b, Examples.grid_isDegenerate a b⟩

end Cereceda
