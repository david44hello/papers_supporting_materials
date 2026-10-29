/-
Cereceda/Setting/CaseASteps.lean — proof of Lemma 2.3: F is a forest; T is reached from s by child arcs (short v3.90 l. 316-332).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof plan. (A) On a cycle of `F`, take the vertex `w` of largest rank and rotate the cycle to start at `w`. The second
and the penultimate vertices of the cycle are distinct neighbours of `w` in `F` of smaller rank, hence out-neighbours of
`w` not on `0`; this contradicts (F1) (`lem_2_3_F1_proved`). (B) Along a walk of `F` from the sink, the property
"reached from `s` by child arcs" is kept: an edge to the parent of the current vertex goes back to the vertex we came
from (F1), and an edge to a child adds one child arc. The last child arc into `v ≠ s` gives the parent of `v`.
-/
import Cereceda.Defs.Intro
import Cereceda.Defs.Instance
import Cereceda.Setting.Small
import Cereceda.Setting.CaseA
import Cereceda.Setting.Misc

namespace Cereceda

open Finset

namespace CaseASteps

variable {W : Type} [Fintype W] [DecidableEq W] {I : Instance W} {c0 : Fin 4} {c : W → Fin 4}

/-- A neighbour in `F` of `w` with rank at most that of `w` is an out-neighbour of `w` not on `0`. -/
lemma mem_filter_of_adj_rank {w u : W} (hwu : (I.fGraph c).Adj w u) (hr : I.rank u ≤ I.rank w) :
    u ∈ (I.out w).filter (fun u => c u ≠ 0) := by
  obtain ⟨hgr, -, hcu⟩ := hwu
  rcases (CaseA.adj_iff.1 hgr).2 with hu | hw
  · exact mem_filter.2 ⟨hu, hcu⟩
  · exact absurd (I.out_before u w hw) (not_lt.2 hr)

/-- Along a walk of `F`, "reached from the sink by child arcs" is kept (each vertex has at most one parent). -/
lemma child_walk (hc : I.IsGreedy c0 c) {u v : W} (q : (I.fGraph c).Walk u v) :
    Relation.ReflTransGen (fun p w => p ∈ I.out w ∧ c p ≠ 0 ∧ c w ≠ 0) I.sink u →
      Relation.ReflTransGen (fun p w => p ∈ I.out w ∧ c p ≠ 0 ∧ c w ≠ 0) I.sink v := by
  induction q with
  | nil => exact id
  | @cons a b _ hadj q ih =>
    intro ha
    apply ih
    obtain ⟨hgr, hca, hcb⟩ := hadj
    rcases (CaseA.adj_iff.1 hgr).2 with hb | ha'
    · rcases ha.cases_tail with h | ⟨p, hp, hpa⟩
      · rw [h, I.sink_out] at hb
        exact absurd hb (Finset.notMem_empty _)
      · have hbp : b = p := by
          by_contra hne
          exact hcb (CaseA.parent_others_zero hc (CaseA.ne_sink_of_mem_out hb) hca hpa.1 hpa.2.1 b hb hne)
        rw [hbp]
        exact hp
    · exact Relation.ReflTransGen.tail ha ⟨ha', hca, hcb⟩

end CaseASteps

/-- Proof of Lemma 2.3, short v3.90 l. 316-317: "Thus `F` induces a forest in which each vertex has at most one parent
(an out-neighbour in `F`): on a cycle in `F`, the vertex that comes last in the instance order would have two
out-neighbours in `F`." -/
theorem lem_2_3_forest_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) : (I.fGraph c).IsAcyclic := by
  intro v p hp
  obtain ⟨w, hw, hmax⟩ := p.support.toFinset.exists_max_image I.rank ⟨v, by simp⟩
  rw [List.mem_toFinset] at hw
  have hq : (p.rotate w hw).IsCycle := hp.rotate hw
  have hle : ∀ u ∈ (p.rotate w hw).support, I.rank u ≤ I.rank w := fun u hu =>
    hmax u (List.mem_toFinset.2 ((SimpleGraph.Walk.mem_support_rotate_iff p w hw).1 hu))
  have ha := (p.rotate w hw).adj_snd hq.not_nil
  have hb := (p.rotate w hw).adj_penultimate hq.not_nil
  have h1 := lem_2_3_F1_proved I c0 c hc w ha.2.1
  exact hq.snd_ne_penultimate (Finset.card_le_one.1 h1 _
    (CaseASteps.mem_filter_of_adj_rank ha (hle _ (SimpleGraph.Walk.getVert_mem_support _ _))) _
    (CaseASteps.mem_filter_of_adj_rank hb.symm (hle _ (SimpleGraph.Walk.getVert_mem_support _ _))))

/-- Proof of Lemma 2.3, short v3.90 l. 329-332: "The sink is the only vertex of `T` without a parent: `T` is a tree, so it
has `|T| - 1` edges; each edge joins a vertex to its parent, and each vertex has at most one parent, so exactly
`|T| - 1` vertices of `T` have a parent, and `s` has none. So every vertex of `T` other than `s` is reached from `s` by
passing repeatedly from a vertex to one of its children" (`T` = the vertices reachable from the sink in `F`). -/
theorem lem_2_3_tree_children_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4)
    (c : W → Fin 4) (hc : I.IsGreedy c0 c) (v : W) (hv : (I.fGraph c).Reachable I.sink v) :
    (v ≠ I.sink → ∃ p ∈ I.out v, c p ≠ 0) ∧
      Relation.ReflTransGen (fun p w => p ∈ I.out w ∧ c p ≠ 0 ∧ c w ≠ 0) I.sink v := by
  obtain ⟨q⟩ := hv
  have h := CaseASteps.child_walk hc q Relation.ReflTransGen.refl
  refine ⟨fun hvs => ?_, h⟩
  rcases h.cases_tail with h' | ⟨p, -, hp⟩
  · exact absurd h' hvs
  · exact ⟨p, hp.1, hp.2.1⟩

end Cereceda
