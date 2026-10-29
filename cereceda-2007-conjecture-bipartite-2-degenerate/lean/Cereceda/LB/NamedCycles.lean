/-
Cereceda/LB/NamedCycles.lean — the cycles named in Section 4: the 4-cycle `a v_1 v_2 v_3 a` of `H_ℓ` (short v3.90
l. 583-584) and the 6-cycle `a_1 v_1 v_2 v_3 v_4 v_5 a_1` of `J_ℓ` (l. 679); so neither graph is a forest.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.LB.Facts
import Cereceda.LB.GirthJ

namespace Cereceda.NamedCycles

open SimpleGraph

/-- The closed walk `inr 0, inl 0, inl 1, inl 2, inr 0` of `H_n` (paper: a v_1 v_2 v_3 a). -/
def Hgraph_fourCycle (n : ℕ) (hn : 3 ≤ n) : (Hgraph n).Walk (.inr 0) (.inr 0) :=
  .cons (v := .inl ⟨0, by omega⟩) ((FactsAux.adj_inr_inl _ _ _).mpr (Fin.ext (by simp))) <|
  .cons (v := .inl ⟨1, by omega⟩) ((FactsAux.adj_inl_inl _ _ _).mpr (.inl rfl)) <|
  .cons (v := .inl ⟨2, by omega⟩) ((FactsAux.adj_inl_inl _ _ _).mpr (.inl rfl)) <|
  .cons (v := .inr 0) ((FactsAux.adj_inl_inr _ _ _).mpr (Fin.ext (by simp))) .nil

lemma Hgraph_fourCycle_length (n : ℕ) (hn : 3 ≤ n) : (Hgraph_fourCycle n hn).length = 4 := rfl

lemma Hgraph_fourCycle_support (n : ℕ) (hn : 3 ≤ n) :
    (Hgraph_fourCycle n hn).support =
      [.inr 0, .inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, .inl ⟨2, by omega⟩, .inr 0] := rfl

lemma Hgraph_fourCycle_isCycle (n : ℕ) (hn : 3 ≤ n) : (Hgraph_fourCycle n hn).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]
    simp [Hgraph_fourCycle]
  · simp [Hgraph_fourCycle]
  · simp [Hgraph_fourCycle]

lemma Jgraph_sixCycle_support (n : ℕ) (hn : 5 ≤ n) :
    (GirthAux.Jgraph_sixCycle n hn).support =
      [.inr 1, .inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, .inl ⟨2, by omega⟩, .inl ⟨3, by omega⟩,
        .inl ⟨4, by omega⟩, .inr 1] := rfl

/-- A graph with a cycle is not acyclic (not a forest). -/
lemma not_isAcyclic_of_isCycle {V : Type} {G : SimpleGraph V} {v : V} {w : G.Walk v v} (hw : w.IsCycle) :
    ¬ G.IsAcyclic := fun h => h w hw

end Cereceda.NamedCycles

namespace Cereceda

open SimpleGraph NamedCycles

/-- Paper (short v3.90, Section 4.1, l. 583-584): "For ℓ ≥ 3 it contains the 4-cycle a v_1 v_2 v_3 a, so it is not
a forest". Lean's `v_i` is `Sum.inl (i-1)` and `a` is `Sum.inr 0`. -/
theorem sec4_Hgraph_four_cycle_proved (n : ℕ) (hn : 3 ≤ n) :
    ∃ w : (Hgraph n).Walk (.inr 0) (.inr 0), w.IsCycle ∧ w.length = 4 ∧
      w.support = [.inr 0, .inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, .inl ⟨2, by omega⟩, .inr 0] ∧
      ¬ (Hgraph n).IsAcyclic :=
  ⟨Hgraph_fourCycle n hn, Hgraph_fourCycle_isCycle n hn, Hgraph_fourCycle_length n hn,
    Hgraph_fourCycle_support n hn, not_isAcyclic_of_isCycle (Hgraph_fourCycle_isCycle n hn)⟩

/-- Paper (short v3.90, Section 4.2, l. 679): "Finally, a_1 v_1 v_2 v_3 v_4 v_5 a_1 is a 6-cycle; so J_ℓ is not a
forest". Lean's `v_i` is `Sum.inl (i-1)` and `a_1` is `Sum.inr 1`. -/
theorem sec4_Jgraph_six_cycle_proved (n : ℕ) (hn : 5 ≤ n) :
    ∃ w : (Jgraph n).Walk (.inr 1) (.inr 1), w.IsCycle ∧ w.length = 6 ∧
      w.support = [.inr 1, .inl ⟨0, by omega⟩, .inl ⟨1, by omega⟩, .inl ⟨2, by omega⟩, .inl ⟨3, by omega⟩,
        .inl ⟨4, by omega⟩, .inr 1] ∧ ¬ (Jgraph n).IsAcyclic :=
  ⟨GirthAux.Jgraph_sixCycle n hn, GirthAux.Jgraph_sixCycle_isCycle n hn, GirthAux.Jgraph_sixCycle_length n hn,
    Jgraph_sixCycle_support n hn, not_isAcyclic_of_isCycle (GirthAux.Jgraph_sixCycle_isCycle n hn)⟩

end Cereceda
