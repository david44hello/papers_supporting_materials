/-
Cereceda/Intro/DistanceHereditary.lean — proof of the row `intro_dh_chordal_bipartite` (short v3.90 l. 176-178): a
bipartite distance-hereditary graph is chordal bipartite. Route: deleting one vertex of a chordless cycle of length at
least 6 leaves a connected induced path whose ends are at distance 2 in the graph; Lean shows that they are at
distance at least 3 in the path (the paper says at least 4), which is enough.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Classes

namespace Cereceda

variable {V : Type} [Fintype V] [DecidableEq V]

namespace DH

open SimpleGraph

variable {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
/-- In a path, the only edge at the first vertex goes to the second vertex. -/
theorem start_edge {a b y : V} {q : G.Walk a b} (hq : q.IsPath) (he : s(a, y) ∈ q.edges) : y = q.getVert 1 := by
  cases q with
  | nil => simp at he
  | cons hac r =>
    rw [Walk.cons_isPath_iff] at hq
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he | he
    · show y = r.getVert 0
      rw [Walk.getVert_zero]
      exact Sym2.congr_right.mp he
    · exact absurd (Walk.fst_mem_support_of_mem_edges r he) hq.2

omit [Fintype V] [DecidableEq V] in
/-- In a path, the only edge at the last vertex comes from the next-to-last vertex. -/
theorem end_edge {a b y : V} {q : G.Walk a b} (hq : q.IsPath) (he : s(y, b) ∈ q.edges) :
    y = q.getVert (q.length - 1) := by
  have h1 := start_edge (y := y) hq.reverse (by rw [Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap]; exact he)
  rwa [Walk.getVert_reverse] at h1

omit [Fintype V] [DecidableEq V] in
/-- A cycle `v a ... b v` of length at least 6 (written as `cons h (q.concat h2)`) has a chord, if `G` is
distance-hereditary. -/
theorem chord_of_concat (hdh : IsDistanceHereditary G) {v a b : V} (h : G.Adj v a) (q : G.Walk a b)
    (h2 : G.Adj b v) (hcyc : (Walk.cons h (q.concat h2)).IsCycle) (hlen : 6 ≤ (Walk.cons h (q.concat h2)).length) :
    ∃ x ∈ (Walk.cons h (q.concat h2)).support, ∃ y ∈ (Walk.cons h (q.concat h2)).support,
      G.Adj x y ∧ s(x, y) ∉ (Walk.cons h (q.concat h2)).edges := by
  by_contra hno
  have chord : ∀ x ∈ (Walk.cons h (q.concat h2)).support, ∀ y ∈ (Walk.cons h (q.concat h2)).support,
      G.Adj x y → s(x, y) ∈ (Walk.cons h (q.concat h2)).edges :=
    fun x hx y hy hxy => Classical.byContradiction fun hne => hno ⟨x, hx, y, hy, hxy, hne⟩
  -- the path `q` and the vertex `v` off it
  rw [Walk.cons_isCycle_iff] at hcyc
  have hrev := hcyc.1.reverse
  rw [Walk.reverse_concat, Walk.cons_isPath_iff, Walk.support_reverse, List.mem_reverse] at hrev
  have hq : q.IsPath := (Walk.isPath_reverse_iff q).mp hrev.1
  have hv : v ∉ q.support := hrev.2
  have hlen4 : 4 ≤ q.length := by
    simp only [Walk.length_cons, Walk.length_concat] at hlen
    omega
  have wsup : ∀ {x}, x ∈ q.support → x ∈ (Walk.cons h (q.concat h2)).support := fun hx => by
    simp [Walk.support_cons, Walk.support_concat, hx]
  -- with no chord, an edge of `G` between two vertices of `q` is an edge of `q`
  have qedge : ∀ x ∈ q.support, ∀ z ∈ q.support, G.Adj x z → s(x, z) ∈ q.edges := by
    intro x hx z hz hxz
    have he := chord x (wsup hx) z (wsup hz) hxz
    simp only [Walk.edges_cons, Walk.edges_concat, List.concat_eq_append, List.mem_cons, List.mem_append] at he
    rcases he with he | he | he | he
    · rcases Sym2.eq_iff.mp he with ⟨e, -⟩ | ⟨-, e⟩
      · exact (hv (e ▸ hx)).elim
      · exact (hv (e ▸ hz)).elim
    · exact he
    · rcases Sym2.eq_iff.mp he with ⟨-, e⟩ | ⟨e, -⟩
      · exact (hv (e ▸ hz)).elim
      · exact (hv (e ▸ hx)).elim
    · simp at he
  have inj := hq.getVert_injOn
  have mem : ∀ i, i ≤ q.length → i ∈ {i | i ≤ q.length} := fun _ hi => hi
  have ha : a ∈ q.support := q.start_mem_support
  have hb : b ∈ q.support := q.end_mem_support
  have hab : a ≠ b := by
    intro e
    have := inj (mem 0 (Nat.zero_le _)) (mem _ le_rfl)
      (by rw [Walk.getVert_zero, Walk.getVert_length]; exact e)
    omega
  have hnab : ¬ G.Adj a b := by
    intro hadj
    have e1 := start_edge hq (qedge a ha b hb hadj)
    have := inj (mem 1 (by omega)) (mem _ le_rfl) (by rw [← e1, Walk.getVert_length])
    omega
  have hnomid : ∀ y ∈ q.support, G.Adj a y → G.Adj y b → False := by
    intro y hy hay hyb
    have e1 := start_edge hq (qedge a ha y hy hay)
    have e2 := end_edge hq (qedge y hy b hb hyb)
    have := inj (mem 1 (by omega)) (mem (q.length - 1) (by omega)) (by rw [← e1, ← e2])
    omega
  -- the subgraph induced on the vertices of `q`
  have hSmem : ∀ x, x ∈ q.toSubgraph.verts ↔ x ∈ q.support := fun x =>
    Set.ext_iff.mp (Walk.verts_toSubgraph q) x
  have hconn : (G.induce q.toSubgraph.verts).Connected :=
    SimpleGraph.Connected.mono (fun x y hxy => q.toSubgraph.adj_sub hxy) q.toSubgraph_connected.coe
  have adj : ∀ {x y : q.toSubgraph.verts}, (G.induce q.toSubgraph.verts).Adj x y → G.Adj x.1 y.1 := fun hxy => hxy
  have no_short : ∀ (x y : q.toSubgraph.verts) (r : (G.induce q.toSubgraph.verts).Walk x y),
      x.1 = a → y.1 = b → 3 ≤ r.length := by
    intro x y r hx hy
    cases r with
    | nil => exact absurd (hx.symm.trans hy) hab
    | @cons _ z _ h1 r1 =>
      cases r1 with
      | nil =>
        have e := adj h1
        rw [hx, hy] at e
        exact absurd e hnab
      | @cons _ z' _ h2' r2 =>
        cases r2 with
        | nil =>
          have e1 := adj h1
          have e2 := adj h2'
          rw [hx] at e1
          rw [hy] at e2
          exact (hnomid z.1 ((hSmem _).mp z.2) e1 e2).elim
        | cons h3 r3 =>
          simp only [Walk.length_cons]
          omega
  have haS : a ∈ q.toSubgraph.verts := (hSmem a).mpr ha
  have hbS : b ∈ q.toSubgraph.verts := (hSmem b).mpr hb
  have hd : (G.induce q.toSubgraph.verts).dist ⟨a, haS⟩ ⟨b, hbS⟩ = G.dist a b :=
    hdh q.toSubgraph.verts hconn ⟨a, haS⟩ ⟨b, hbS⟩
  obtain ⟨r, hr⟩ := (hconn.preconnected ⟨a, haS⟩ ⟨b, hbS⟩).exists_walk_length_eq_dist
  have h3 := no_short ⟨a, haS⟩ ⟨b, hbS⟩ r rfl rfl
  have hG : G.dist a b ≤ 2 := SimpleGraph.dist_le (Walk.cons h.symm (Walk.cons h2.symm Walk.nil))
  omega

end DH

omit [Fintype V] [DecidableEq V] in
theorem intro_dh_chordal_bipartite_proved (G : SimpleGraph V) (hbip : G.IsBipartite) (hdh : IsDistanceHereditary G) :
    IsChordalBipartite G := by
  refine ⟨hbip, fun v w hcyc hlen => ?_⟩
  match w, hcyc, hlen with
  | .nil, _, hlen => simp at hlen
  | .cons _ .nil, _, hlen => simp at hlen
  | .cons h (.cons h3 p'), hcyc, hlen =>
    obtain ⟨b, q, h2, hq⟩ := SimpleGraph.Walk.exists_cons_eq_concat h3 p'
    rw [hq] at hcyc hlen ⊢
    exact DH.chord_of_concat hdh h q h2 hcyc hlen

end Cereceda
