/-
EulerFlow/Sec2/ShortClaims4.lean — two in-text claims of the SHORT paper: A-connectedness differs from
A-flow-connectedness (the graph with two vertices and one edge is A-flow-connected, as it has no flow, but it is not
A-connected: for β = 0 the edge would need the value 0); a graph with no edge has exactly one flow.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import EulerFlow.Defs.Constructions

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- The graph with two vertices and one edge has no flow: at the vertex `0` the edge leaves and nothing enters. -/
theorem dipole_one_no_flow {A : Type} [AddCommGroup A] (f : Fin 1 → A) : ¬ (dipole 1).IsNZFlow f := by
  rintro ⟨hflow, hnz⟩
  have h := hflow 0
  simp [dipole] at h
  exact hnz 0 h

/-- SHORT l.157-158: the graph with two vertices and one edge is `A`-flow-connected but not `A`-connected. -/
theorem A_connected_differs_proved (A : Type) [AddCommGroup A] :
    (dipole 1).FlowConnected A ∧
    ¬ ∀ β : Fin 2 → A, ∑ v, β v = 0 → ∃ x : Fin 1 → A, (∀ e, x e ≠ 0) ∧ ∀ v,
      ∑ e ∈ Finset.univ.filter (fun e => (dipole 1).src e = v), x e -
      ∑ e ∈ Finset.univ.filter (fun e => (dipole 1).tgt e = v), x e = β v := by
  refine ⟨fun f => absurd f.2 (dipole_one_no_flow f.1), fun h => ?_⟩
  obtain ⟨x, hx, hb⟩ := h 0 (by simp)
  have h0 := hb 0
  simp [dipole] at h0
  exact hx 0 h0

omit [Fintype V] [DecidableEq E] in
/-- SHORT l.335: a graph with no edge has exactly one flow (the empty map), for every `A`. -/
theorem no_edge_proved (A : Type) [AddCommGroup A] (G : MGraph V E) [IsEmpty E] :
    ∃! f : E → A, G.IsNZFlow f :=
  ⟨fun e => isEmptyElim e, ⟨fun v => by simp [Finset.univ_eq_empty], fun e => isEmptyElim e⟩,
    fun g _ => funext fun e => isEmptyElim e⟩

end EulerFlow
