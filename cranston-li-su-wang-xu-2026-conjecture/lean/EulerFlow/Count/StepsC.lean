/-
EulerFlow/Count/StepsC.lean — paper 002, Section 7 (tex l.534-555): the multi-step counts behind Theorem 2.5, stated
on the paper's multi-step graph (`multiStepGraph`: a multi-step is `IsMultiStep`).
Route: every multi-step in `h`-form (`CircStep`) is a multi-step, as `circ_decomp` splits `h` into edge-disjoint
directed cycles; so `msGraph ≤ multiStepGraph`, and the counts of Count/StepsA.lean and Count/StepsB.lean carry over
with the same lengths.
-/
import EulerFlow.Count.StepsB

namespace EulerFlow

namespace Count

open Finset MGraph

variable {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E] {A : Type} [AddCommGroup A]

/-- A multi-step in `h`-form is a multi-step with the same value: `circ_decomp` splits `h` into edge-disjoint
directed cycles. -/
lemma isMultiStep_of_circStep {G : MGraph V E} {f f' : E → A} (hstep : CircStep G f f') :
    ∃ t, G.IsMultiStep t f f' := by
  obtain ⟨t, ht, h, hval, hfl, ⟨e, he⟩, heq⟩ := hstep
  obtain ⟨Qs, hpw, -, hsum, -⟩ := circ_decomp h hval hfl
  refine ⟨t, ht, Qs, ?_, hpw, ?_⟩
  · rintro rfl; apply he; rw [← hsum e]; simp
  · rw [heq]; funext y; simp only [Pi.add_apply, hsum]

/-- Every edge of `msGraph` is an edge of the paper's multi-step graph. -/
lemma msGraph_le_multiStepGraph (G : MGraph V E) : msGraph G A ≤ G.multiStepGraph A := by
  intro f f' hadj
  rw [msGraph, SimpleGraph.fromRel_adj] at hadj
  unfold MGraph.multiStepGraph
  rw [SimpleGraph.fromRel_adj]
  exact ⟨hadj.1, hadj.2.imp isMultiStep_of_circStep isMultiStep_of_circStep⟩

variable [Fintype V]

/-- `sec7_c_bound` (Section 7, tex l.534-543): `c(G) ≤ M(M+3)/2`. -/
theorem sec7_c_bound_proved [Fintype A] (a : A) (ha : a ≠ 0) (G : MGraph V E) (hev : G.IsEven)
    (hdeg : ∀ v, G.degree v ≤ 4) (f : {f : E → A // G.IsNZFlow f}) :
    ∃ D : E → Bool, G.IsEulerOrient D ∧ ∃ hnz : G.IsNZFlow (constFlow a D),
      ∃ w : (G.multiStepGraph A).Walk f ⟨_, hnz⟩, 2 * w.length ≤ Fintype.card E * (Fintype.card E + 3) := by
  obtain ⟨D, hD, w, hw⟩ := count_bound a ha _ V E G rfl hev hdeg f
  exact ⟨D, hD, _, w.mapLe (msGraph_le_multiStepGraph G), by rw [SimpleGraph.Walk.length_mapLe]; exact hw⟩

/-- `sec7_multistep_bound` (Section 7, tex l.545-546): at most `M² + 3M + 1` multi-steps. -/
theorem sec7_multistep_bound_proved [Fintype A] (G : MGraph V E) (hev : G.IsEven) (hdeg : ∀ v, G.degree v ≤ 4)
    (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.multiStepGraph A).Walk f f', w.length ≤ Fintype.card E ^ 2 + 3 * Fintype.card E + 1 := by
  obtain ⟨w, hw⟩ := ms_bound G hev hdeg f f'
  exact ⟨w.mapLe (msGraph_le_multiStepGraph G), by rw [SimpleGraph.Walk.length_mapLe]; exact hw⟩

/-- `sec7_multistep_bound_loopless` (Section 7, tex l.553-555): `|A| ≥ 4`, no loop: at most `16M² + 12M + 1`
multi-steps; the `Φ`-induction with `k = 4M`, as `Φ ≤ 2M` (the sum of the degrees). -/
theorem sec7_multistep_bound_loopless_proved [Fintype A] (hA : 4 ≤ Fintype.card A) (G : MGraph V E)
    (hev : G.IsEven) (hG : G.Loopless) (f f' : {f : E → A // G.IsNZFlow f}) :
    ∃ w : (G.multiStepGraph A).Walk f f', w.length ≤ 16 * Fintype.card E ^ 2 + 12 * Fintype.card E + 1 := by
  have hphi : G.phi ≤ 2 * Fintype.card E := by
    rw [← MGraph.Sec4.sum_degree (G := G)]
    exact Finset.sum_le_sum fun v _ => Nat.sub_le _ _
  obtain ⟨w, hw⟩ := ms_bound_loopless hA _ V E G rfl hG hev (4 * Fintype.card E) (by omega) f f'
  exact ⟨w.mapLe (msGraph_le_multiStepGraph G), by
    rw [SimpleGraph.Walk.length_mapLe]; exact hw.trans (le_of_eq (by ring))⟩

end Count

end EulerFlow
