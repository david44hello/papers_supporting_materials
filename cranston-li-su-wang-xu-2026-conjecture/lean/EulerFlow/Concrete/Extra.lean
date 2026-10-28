/-
EulerFlow/Concrete/Extra.lean — small facts for review r2: the one-cycle graph is even; (p,1)-flows are ℤ_p-flows.
-/
import EulerFlow.Concrete.Small

namespace EulerFlow

open MGraph

/-- The graph that is one cycle is even: every vertex has degree `2` (a loop counts twice). -/
theorem cycleGraph_isEven (n : ℕ) : (cycleGraph n).IsEven := by
  intro v
  haveI : NeZero n := ⟨by rintro rfl; exact v.elim0⟩
  have hset : (Finset.univ.filter fun i : Fin n × Bool => (cycleGraph n).endVertex i = v) =
      {(v, false), ((finRotate n).symm v, true)} := by
    ext ⟨e, b⟩
    cases b <;> simp [endVertex, cycleGraph]
    exact eq_sub_iff_add_eq.symm
  unfold degree
  rw [hset, Finset.card_pair (by simp)]
  exact even_two

/-- For `q = 1`, `(p,q)`-flow-connected is `ℤ_p`-flow-connected (tex l.705-706). -/
theorem pq_one_iff {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (p : ℕ) (hp : 2 < p)
    (G : MGraph V E) : G.PQFlowConnected p 1 ↔ G.FlowConnected (ZMod p) := by
  show (G.stepGraph (Ipq p 1) {x | x ≠ 0}).Preconnected ↔ (G.stepGraph {x | x ≠ 0} {x | x ≠ 0}).Preconnected
  rw [(sec9_I_one_proved p hp).1]

end EulerFlow
