/-
EulerFlow/Sec2/Basic.lean — equations (2.1) and (2.2) of paper 002 (tex l.155-164).
-/
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow.MGraph.Sec2

open Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}

set_option linter.unusedSectionVars false

/-- The outward values at `v` sum to (leaving sum) − (entering sum). -/
theorem sum_dirVal_ends {A : Type} [AddCommGroup A] (f : E → A) (v : V) :
    ∑ i ∈ univ.filter (fun i : E × Bool => G.endVertex i = v), dirVal f i =
      ∑ e ∈ univ.filter (fun e => G.src e = v), f e - ∑ e ∈ univ.filter (fun e => G.tgt e = v), f e := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endVertex, dirVal, Bool.false_eq_true, ite_false, ite_true]
  rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
  have : ∑ x : E, (if G.tgt x = v then -f x else 0) = -∑ x : E, (if G.tgt x = v then f x else 0) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext x; split_ifs <;> simp
  rw [this]; abel

/-- Equation (2.1) (tex l.155-159). -/
theorem kirchhoff_iff {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) :
    G.IsFlow f ↔ ∀ v, ∑ i ∈ Finset.univ.filter (fun i : E × Bool => G.endVertex i = v), dirVal f i = 0 := by
  simp only [sum_dirVal_ends, sub_eq_zero]
  rfl

/-- Equation (2.2) (tex l.160-164). -/
theorem ends {A : Type} [AddCommGroup A] (G : MGraph V E) (f : E → A) (t : A) (Q : G.DirCycle) (v : V)
    (d d' : E × Bool) (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    dirVal (f + fun e => Q.chi e • t) (d'.1, !d'.2) = dirVal f (d'.1, !d'.2) - t ∧
    dirVal (f + fun e => Q.chi e • t) d = dirVal f d + t ∧
    ∀ i, G.endVertex i = v → i ≠ d → i ≠ (d'.1, !d'.2) → dirVal (f + fun e => Q.chi e • t) i = dirVal f i := by
  refine ⟨Q.dirVal_step_flip f t hd', Q.dirVal_step_mem f t hd, fun i hiv hid hid' => ?_⟩
  have hoff := Q.other_end_not_mem hd hd' hdv hd'v hiv hid hid'
  exact Q.dirVal_step_off f t hoff.1 hoff.2

end EulerFlow.MGraph.Sec2
