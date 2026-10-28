/-
EulerFlow/Reduction/Basic.lean — small facts used throughout Section 3 of paper 002: flows form a group, the
chi-sum of a list of directed cycles, and transport of reachability along a map of step graphs.
-/
import EulerFlow.Reduction.Split
import EulerFlow.Graph.Orient

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [Fintype E]

theorem boundary_add {M : Type} [AddCommGroup M] (x y : E → M) (z : V) :
    G.boundary (x + y) z = G.boundary x z + G.boundary y z := by
  simp only [boundary, Pi.add_apply, Finset.sum_add_distrib]; abel

theorem boundary_zero {M : Type} [AddCommGroup M] (z : V) : G.boundary (0 : E → M) z = 0 := by
  simp [boundary]

theorem boundary_smul (x : E → ℤ) (t : ℤ) (z : V) : G.boundary (fun e => t * x e) z = t * G.boundary x z := by
  simp only [boundary, ← Finset.mul_sum, mul_sub]

theorem isFlow_zero {M : Type} [AddCommGroup M] : G.IsFlow (0 : E → M) := by
  rw [isFlow_iff_boundary]; exact boundary_zero

variable [DecidableEq E]

/-- The chi-sum `χ_{Q_1} + ⋯ + χ_{Q_r}` of a list of directed cycles. -/
def chiSum (Qs : List G.DirCycle) : E → ℤ := fun e => (Qs.map fun Q => Q.chi e).sum

theorem isFlow_chiSum (Qs : List G.DirCycle) : G.IsFlow (chiSum Qs) := isFlow_sum_chi Qs

/-- Transport of reachability: a map that sends adjacent vertices to reachable ones sends reachable vertices to
reachable ones. -/
theorem reachable_map {α β : Type} {H₁ : SimpleGraph α} {H₂ : SimpleGraph β} (φ : α → β)
    (hφ : ∀ a b, H₁.Adj a b → H₂.Reachable (φ a) (φ b)) {a b : α} (hab : H₁.Reachable a b) :
    H₂.Reachable (φ a) (φ b) := by
  obtain ⟨w⟩ := hab
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (hφ _ _ hadj).trans ih

/-- An adjacency of a step graph, unfolded: one of the two flows is the other plus `t χ_Q`. -/
theorem stepGraph_adj {A : Type} [AddCommGroup A] {I T : Set A} {f f' : {f : E → A // G.IsIFlow I f}}
    (h : (G.stepGraph I T).Adj f f') :
    (∃ Q : G.DirCycle, ∃ t ∈ T, t ≠ 0 ∧ f'.1 = f.1 + fun e => Q.chi e • t) ∨
      (∃ Q : G.DirCycle, ∃ t ∈ T, t ≠ 0 ∧ f.1 = f'.1 + fun e => Q.chi e • t) := by
  rw [stepGraph, SimpleGraph.fromRel_adj] at h
  exact h.2

/-- Transport of `T`-joinedness: if a map of `I`-flows sends every step `f ↦ f + t χ_Q` to a difference
`h·t` with `h` a `{-1,0,1}`-valued integer flow, it sends `T`-joined flows to `T`-joined flows. -/
theorem reachable_transport {V' E' : Type} [DecidableEq V'] [Fintype E'] [DecidableEq E'] {G' : MGraph V' E'}
    {A : Type} [AddCommGroup A] {I T : Set A}
    (φ : {f : E' → A // G'.IsIFlow I f} → {f : E → A // G.IsIFlow I f})
    (hφ : ∀ (f : {f : E' → A // G'.IsIFlow I f}) (Q : G'.DirCycle) (t : A) (hft : G'.IsIFlow I (f.1 + fun e => Q.chi e • t)),
      ∃ h : E → ℤ, (∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) ∧ G.IsFlow h ∧
        (φ ⟨_, hft⟩).1 = (φ f).1 + fun e => h e • t)
    {a b : {f : E' → A // G'.IsIFlow I f}} (hab : (G'.stepGraph I T).Reachable a b) :
    (G.stepGraph I T).Reachable (φ a) (φ b) := by
  refine reachable_map φ (fun f f' hadj => ?_) hab
  rcases stepGraph_adj hadj with ⟨Q, t, ht, ht0, hf'⟩ | ⟨Q, t, ht, ht0, hf⟩
  · have hft : G'.IsIFlow I (f.1 + fun e => Q.chi e • t) := hf' ▸ f'.2
    obtain ⟨h, hv, hc, hφf⟩ := hφ f Q t hft
    have : f' = ⟨_, hft⟩ := Subtype.ext hf'
    subst this
    exact reachable_of_circ _ _ h hv hc t ht ht0 hφf
  · have hft : G'.IsIFlow I (f'.1 + fun e => Q.chi e • t) := hf ▸ f.2
    obtain ⟨h, hv, hc, hφf⟩ := hφ f' Q t hft
    have : f = ⟨_, hft⟩ := Subtype.ext hf
    subst this
    exact (reachable_of_circ _ _ h hv hc t ht ht0 hφf).symm

end MGraph

end EulerFlow
