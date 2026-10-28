/-
EulerFlow/Reduction/OneCycle.lean — Remark 9.7 for every graph that is one cycle (tex l.859-861): if all edges and
all vertices of `G` lie on one directed cycle `Q`, then `G` is even and `(p,q)`-flow-connected ("any two different
`(p,q)`-flows of it differ by a non-zero constant along the cycle, which is one step").
-/
import EulerFlow.Graph.AgreeOutside
import EulerFlow.Reduction.Split

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E] {G : MGraph V E}

omit [Fintype E] [DecidableEq E] in
/-- The ends of `e` at `v`, counted through the dart of `e`: one end is the dart's tail, the other its head. -/
theorem endCount_eq_dart (v : V) (d : E × Bool) :
    G.endCount v d.1 = (if G.dartTail d = v then 1 else 0) + (if G.dartHead d = v then 1 else 0) := by
  obtain ⟨e, b⟩ := d
  cases b <;> simp [endCount, dartTail, dartHead, endVertex, add_comm]

/-- A graph all of whose edges lie on one directed cycle is even: at every vertex the cycle enters as often as it
leaves. -/
theorem isEven_of_one_cycle (Q : G.DirCycle) (hE : ∀ e, ∃ d ∈ Q.darts, d.1 = e) (v : V) : Even (G.degree v) := by
  have hnd := Q.edges_nodup
  have hfin : (Q.darts.map Prod.fst).toFinset = univ := by
    ext e; simp only [List.mem_toFinset, List.mem_map, mem_univ, iff_true]; exact hE e
  rw [degree_eq_sum_endCount, ← hfin, List.sum_toFinset _ hnd, List.map_map]
  have : (Q.darts.map ((fun e => G.endCount v e) ∘ Prod.fst)) =
      Q.darts.map (fun d => (if G.dartTail d = v then 1 else 0) + (if G.dartHead d = v then 1 else 0)) :=
    List.map_congr_left fun d _ => endCount_eq_dart v d
  rw [this, List.sum_map_add]
  have hperm : ((Q.darts.map G.dartHead).map fun w => if w = v then 1 else 0).sum =
      ((Q.darts.map G.dartTail).map fun w => if w = v then 1 else 0).sum :=
    (Q.heads_perm_tails.map _).sum_eq
  simp only [List.map_map] at hperm
  rw [show (Q.darts.map fun d => if G.dartHead d = v then 1 else 0) =
      Q.darts.map ((fun w => if w = v then 1 else 0) ∘ G.dartHead) from rfl, hperm]
  exact ⟨_, rfl⟩

end MGraph

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Remark 9.7 for every graph that is one cycle (tex l.859-861), exactly the Statements type. -/
theorem rem_9_7_one_cycle_proved (p q : ℕ) (_hq : 1 ≤ q) (_hpq : 2 * q < p) (G : MGraph V E) (Q : G.DirCycle)
    (hE : ∀ e, ∃ d ∈ Q.darts, d.1 = e) (_hV : ∀ v, ∃ d ∈ Q.darts, G.dartTail d = v) :
    G.IsEven ∧ G.PQFlowConnected p q := by
  refine ⟨isEven_of_one_cycle Q hE, fun f₁ f₂ => ?_⟩
  -- every edge is on `Q`, so the two flows agree off `Q` and differ by `t χ_Q` (tex l.860-861)
  have hout : ∀ e, Q.chi e = 0 → f₁.1 e = f₂.1 e := by
    intro e h0
    obtain ⟨d, hd, rfl⟩ := hE e
    exact absurd h0 ((Q.chi_ne_zero_iff d.1).2 (List.mem_map.2 ⟨d, hd, rfl⟩))
  obtain ⟨t, ht⟩ := (sec2_agree_outside_cycle_proved G Q f₁.1 f₂.1 f₁.2.1 f₂.2.1).1 hout
  by_cases heq : f₁ = f₂
  · rw [heq]
  by_cases ht0 : t = 0
  · exact absurd (Subtype.ext (by rw [ht, ht0]; funext e; simp)) heq
  refine SimpleGraph.Adj.reachable ?_
  rw [pqFlowGraph, stepGraph, SimpleGraph.fromRel_adj]
  exact ⟨heq, Or.inl ⟨Q, t, ht0, ht0, ht⟩⟩

end EulerFlow
