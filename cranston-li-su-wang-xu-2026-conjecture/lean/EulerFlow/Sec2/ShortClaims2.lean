/-
EulerFlow/Sec2/ShortClaims2.lean — in-text claims that the SHORT paper's release 1.53 adds (Section 1): an even graph
has a nowhere-zero 3-flow; the even graph with two vertices and six parallel edges has a nowhere-zero 3-flow (three
edges with value 1, three with value -1) and its two vertices are joined by six edge-disjoint paths; at a vertex of
degree 2 of a loopless graph the two ends form a balanced pair in every flow; a triangle is A-connected (|A| ≥ 4)
with the sign of the paper's definition (leaving minus entering), for any directions of its edges; Section 4: the
small edges contain a cycle.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import EulerFlow.Concrete.Dipole
import EulerFlow.Concrete.Small
import EulerFlow.Reduction.Reduce
import EulerFlow.Reduction.Triangle
import EulerFlow.Sec4.Prop44

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
/-- Every even graph has a nowhere-zero `3`-flow: the constant integer flow with value `1` of an Eulerian
orientation (its values are `1` and `-1`). -/
theorem even_has_three_flow_proved (G : MGraph V E) (hev : G.IsEven) : ∃ F : E → ℤ, G.IsIFlow (Ik 3) F := by
  obtain ⟨D, hD⟩ := exists_eulerOrient (G := G) hev
  refine ⟨constFlow 1 D, isIFlow_constFlow (fun y hy => ?_) hD ?_⟩
  · simpa [Ik, abs_neg] using hy
  · simp [Ik]

/-- The integer map on the six edges of `dipole 6` (all directed from `0` to `1`): value `1` on the first three
edges and `-1` on the other three. -/
def dipoleThreeFlow : Fin 6 → ℤ := fun i => if i.val < 3 then 1 else -1

theorem dipoleThreeFlow_isIFlow : (dipole 6).IsIFlow (Ik 3) dipoleThreeFlow := by
  refine ⟨fun v => ?_, fun e => ?_⟩
  · fin_cases v <;> decide
  · show 1 ≤ |dipoleThreeFlow e| ∧ |dipoleThreeFlow e| ≤ 3 - 1
    fin_cases e <;> decide

/-- The path of `dipole n` along its single edge `i`, from `0` to `1`. -/
def dipoleEdgePath {n : ℕ} (i : Fin n) : (dipole n).Path 0 1 where
  darts := [(i, false)]
  ne_nil := by simp
  chain := List.isChain_singleton _
  starts := rfl
  ends := rfl
  verts_nodup := by simp [MGraph.dartTail, MGraph.endVertex, dipole]

theorem dipole_six_paths :
    ∃ Ps : List ((dipole 6).Path 0 1), Ps.length = 6 ∧ Ps.Pairwise Path.EdgeDisjoint := by
  refine ⟨(List.finRange 6).map dipoleEdgePath, by simp, ?_⟩
  rw [List.pairwise_map]
  refine (List.nodup_finRange 6).imp ?_
  intro i j hij d hd d' hd'
  simp only [dipoleEdgePath, List.mem_singleton] at hd hd'
  subst hd hd'
  exact hij

/-- The six-parallel-edge graph has a nowhere-zero `3`-flow with values `1` on three edges and `-1` on the other
three, and its two vertices are joined by six edge-disjoint paths. -/
theorem intro_example_flow_paths_proved :
    (∃ F : Fin 6 → ℤ, (dipole 6).IsIFlow (Ik 3) F ∧
      (Finset.univ.filter fun i => F i = 1).card = 3 ∧ (Finset.univ.filter fun i => F i = -1).card = 3) ∧
    ∃ Ps : List ((dipole 6).Path 0 1), Ps.length = 6 ∧ Ps.Pairwise Path.EdgeDisjoint :=
  ⟨⟨dipoleThreeFlow, dipoleThreeFlow_isIFlow, by decide, by decide⟩, dipole_six_paths⟩

omit [Fintype V] in
/-- At a vertex `v` of degree `2` of a loopless graph, the two ends at `v` belong to two different edges and form a
balanced pair in every flow. -/
theorem degree_two_balanced_proved (G : MGraph V E) (hG : G.Loopless) {v : V} (hv : G.degree v = 2) :
    ∃ e e' : E, e ≠ e' ∧ G.IsAt e v ∧ G.IsAt e' v ∧ ∀ {A : Type} [AddCommGroup A] (f : E → A), G.IsFlow f →
      dirVal f (G.endAt e v) + dirVal f (G.endAt e' v) = 0 := by
  obtain ⟨e, e', hd, hbal⟩ := splitData_of_degree_two hG hv
  exact ⟨e, e', hd.ne, hd.at₁, hd.at₂, hbal⟩

/-- A triangle is `A`-connected when `|A| ≥ 4`, with the sign of the definition after [JLPT] in the paper: for every
`β` with sum `0` there is a nowhere-zero `x` such that at every vertex the sum of `x` on the leaving edges minus the
sum on the entering edges is `β(v)`. (`intro_triangle_A_connected_proved` uses entering minus leaving; apply it to
`-β`.) -/
theorem triangle_A_connected_out_in_proved {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A)
    (β : Fin 3 → A) (hβ : ∑ v, β v = 0) :
    ∃ x : Fin 3 → A, (∀ e, x e ≠ 0) ∧ ∀ v, ∑ e ∈ Finset.univ.filter (fun e => (cycleGraph 3).src e = v), x e -
      ∑ e ∈ Finset.univ.filter (fun e => (cycleGraph 3).tgt e = v), x e = β v := by
  obtain ⟨x, hx, hb⟩ := intro_triangle_A_connected_proved hA (-β) (by simp [Finset.sum_neg_distrib, hβ])
  refine ⟨x, hx, fun v => ?_⟩
  have h := congrFun hb v
  simp only [MGraph.boundary, Pi.neg_apply] at h
  rw [← neg_sub, h, neg_neg]

/-- A triangle is `A`-connected when `|A| ≥ 4` for ANY reference directions of its edges (`reorient R` reverses the
edges `e` with `R e`): from `triangle_A_connected_out_in_proved`, negate the value of every reversed edge. -/
theorem triangle_A_connected_any_dir_proved {A : Type} [AddCommGroup A] [Fintype A] (hA : 4 ≤ Fintype.card A)
    (R : Fin 3 → Bool) (β : Fin 3 → A) (hβ : ∑ v, β v = 0) :
    ∃ x : Fin 3 → A, (∀ e, x e ≠ 0) ∧ ∀ v,
      ∑ e ∈ Finset.univ.filter (fun e => ((cycleGraph 3).reorient R).src e = v), x e -
      ∑ e ∈ Finset.univ.filter (fun e => ((cycleGraph 3).reorient R).tgt e = v), x e = β v := by
  obtain ⟨x, hx, hb⟩ := triangle_A_connected_out_in_proved hA β hβ
  refine ⟨fun e => if R e then -x e else x e, fun e => by dsimp only; split_ifs <;> simp [hx e], fun v => ?_⟩
  rw [← hb v]
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [MGraph.reorient]
  by_cases hR : R e
  · simp only [hR, ↓reduceIte]
    split_ifs <;> abel
  · simp only [hR, Bool.false_eq_true, ↓reduceIte]

/-- Section 4 plan: in a graph with an edge in which every degree is `0` or `4`, if every directed cycle has an edge
that is not small (the edges that are not small form a forest), then the small edges contain a directed cycle.
(Proof from review B r3, Appendix A: the first half of `prop_4_4_main`.) -/
theorem sec4_small_cycle_proved {A : Type} [AddCommGroup A] (D : CyclicDecomp A) (G : MGraph V E)
    (hE : Nonempty E) (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) (f : E → A)
    (hforest : ∀ Q : G.DirCycle, ∃ d ∈ Q.darts, f d.1 ∈ D.S) :
    ∃ Q : G.DirCycle, ∀ d ∈ Q.darts, f d.1 ∈ D.S := by
  classical
  set W := Finset.univ.filter (fun v => G.degree v = 4) with hW
  have hend_deg : ∀ e, G.degree (G.src e) = 4 ∧ G.degree (G.tgt e) = 4 := by
    intro e
    have hpos : ∀ i : E × Bool, 0 < G.degree (G.endVertex i) := fun i =>
      Finset.card_pos.mpr ⟨i, by simp⟩
    have h1 := hpos (e, false)
    have h2 := hpos (e, true)
    simp only [endVertex, Bool.false_eq_true, ite_false, ite_true] at h1 h2
    refine ⟨?_, ?_⟩
    · rcases hdeg (G.src e) with h | h <;> omega
    · rcases hdeg (G.tgt e) with h | h <;> omega
  have hend : ∀ (S : Finset E), ∀ e ∈ S, G.src e ∈ W ∧ G.tgt e ∈ W := fun S e _ => by
    simp [hW, (hend_deg e).1, (hend_deg e).2]
  have hWne : W.Nonempty := by
    obtain ⟨e⟩ := hE; exact ⟨G.src e, by simp [hW, (hend_deg e).1]⟩
  have hcardE : Fintype.card E = 2 * W.card := by
    have h := Sec4.sum_degree (G := G)
    have : ∑ v, G.degree v = ∑ v ∈ W, 4 := by
      rw [hW, Finset.sum_filter]; congr 1; ext v; rcases hdeg v with h | h <;> simp [h]
    rw [this, Finset.sum_const, smul_eq_mul] at h; omega
  set Sn := Finset.univ.filter (fun e => f e ∉ D.S)
  set Ss := Finset.univ.filter (fun e => f e ∈ D.S)
  have hSn : Sn.card < W.card := card_lt_of_acyclic Sn W hWne (hend Sn) (by
    intro Q hQ
    obtain ⟨d, hd, hds⟩ := hforest Q
    have := hQ d hd
    simp [Sn] at this
    exact this hds)
  have hsplit : Sn.card + Ss.card = Fintype.card E := by
    rw [add_comm, Finset.card_filter_add_card_filter_not]; rfl
  have hSsne : Ss.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨Q, hQ⟩ := exists_dirCycle_of_card_le Ss W hSsne (hend Ss) (by omega)
  exact ⟨Q, fun d hd => by simpa [Ss] using hQ d hd⟩

end EulerFlow
