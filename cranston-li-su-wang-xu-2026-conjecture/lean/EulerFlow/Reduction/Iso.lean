/-
EulerFlow/Reduction/Iso.lean — flows, steps and multi-steps are invariant under a graph isomorphism: an edge
bijection `eE : E₁ ≃ E₂` and an injective vertex map `fV : V₁ → V₂` that respect the reference ends. (The vertices
of `G₂` outside the image of `fV` carry no edge.) Used for "G = G⁺/Δ" in the proof of Theorem 2.3 (tex l.455).
-/
import EulerFlow.Reduction.Basic

namespace EulerFlow

open Finset

namespace MGraph

variable {V₁ E₁ V₂ E₂ : Type} [DecidableEq V₁] [Fintype E₁] [DecidableEq E₁] [DecidableEq V₂] [Fintype E₂]
  [DecidableEq E₂] {G₁ : MGraph V₁ E₁} {G₂ : MGraph V₂ E₂}

/-- An isomorphism of `G₁` onto its image in `G₂`, bijective on the edges. -/
structure EdgeIso (G₁ : MGraph V₁ E₁) (G₂ : MGraph V₂ E₂) where
  eE : E₁ ≃ E₂
  fV : V₁ → V₂
  inj : Function.Injective fV
  src : ∀ e, G₂.src (eE e) = fV (G₁.src e)
  tgt : ∀ e, G₂.tgt (eE e) = fV (G₁.tgt e)

variable (φ : EdgeIso G₁ G₂)
include φ

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem EdgeIso.boundary_comp {M : Type} [AddCommGroup M] (x : E₂ → M) (z : V₁) :
    G₂.boundary x (φ.fV z) = G₁.boundary (fun e => x (φ.eE e)) z := by
  rw [boundary_eq_sum_bdryTerm, boundary_eq_sum_bdryTerm, ← φ.eE.sum_comp]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [bdryTerm, φ.src, φ.tgt, φ.inj.eq_iff]

omit [DecidableEq V₁] [DecidableEq E₁] [DecidableEq E₂] in
theorem EdgeIso.boundary_off {M : Type} [AddCommGroup M] (x : E₂ → M) (w : V₂) (hw : ∀ z, φ.fV z ≠ w) :
    G₂.boundary x w = 0 := by
  rw [boundary_eq_sum_bdryTerm, ← φ.eE.sum_comp]
  refine Finset.sum_eq_zero fun e _ => ?_
  simp [bdryTerm, φ.src, φ.tgt, hw]

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem EdgeIso.isFlow_iff {M : Type} [AddCommGroup M] (x : E₂ → M) :
    G₂.IsFlow x ↔ G₁.IsFlow (fun e => x (φ.eE e)) := by
  simp only [isFlow_iff_boundary]
  refine ⟨fun h z => (φ.boundary_comp x z).symm.trans (h _), fun h w => ?_⟩
  by_cases hw : ∃ z, φ.fV z = w
  · obtain ⟨z, rfl⟩ := hw; rw [φ.boundary_comp]; exact h z
  · push Not at hw; exact φ.boundary_off x w hw

omit [DecidableEq E₁] [DecidableEq E₂] in
theorem EdgeIso.isIFlow_iff {M : Type} [AddCommGroup M] {I : Set M} (x : E₂ → M) :
    G₂.IsIFlow I x ↔ G₁.IsIFlow I (fun e => x (φ.eE e)) := by
  rw [IsIFlow, IsIFlow, φ.isFlow_iff]
  exact and_congr Iff.rfl ⟨fun h e => h _, fun h e => by simpa using h (φ.eE.symm e)⟩

/-- `T`-joinedness passes along an isomorphism. -/
theorem EdgeIso.preconnected {A : Type} [AddCommGroup A] {I T : Set A} (h : (G₁.stepGraph I T).Preconnected) :
    (G₂.stepGraph I T).Preconnected := by
  intro g₁ g₂
  let ψ : {f : E₁ → A // G₁.IsIFlow I f} → {f : E₂ → A // G₂.IsIFlow I f} :=
    fun f => ⟨fun e => f.1 (φ.eE.symm e), (φ.isIFlow_iff _).2 (by simpa using f.2)⟩
  have key := reachable_transport ψ (fun f Q t hft => ⟨fun e => Q.chi (φ.eE.symm e), fun e => Q.chi_mem _,
    (φ.isFlow_iff _).2 (by simpa using Q.isFlow_chi), rfl⟩)
    (h ⟨_, (φ.isIFlow_iff _).1 g₁.2⟩ ⟨_, (φ.isIFlow_iff _).1 g₂.2⟩)
  have e₁ : ψ ⟨_, (φ.isIFlow_iff _).1 g₁.2⟩ = g₁ := Subtype.ext (funext fun e => by simp [ψ])
  have e₂ : ψ ⟨_, (φ.isIFlow_iff _).1 g₂.2⟩ = g₂ := Subtype.ext (funext fun e => by simp [ψ])
  rw [e₁, e₂] at key
  exact key

/-- `A`-flow-connectedness passes along an isomorphism. -/
theorem EdgeIso.flowConnected {A : Type} [AddCommGroup A] (h : G₁.FlowConnected A) : G₂.FlowConnected A :=
  φ.preconnected h

/-- A multi-step passes along an isomorphism, with the same value. -/
theorem EdgeIso.isMultiStep {A : Type} [AddCommGroup A] {t : A} {f f' : E₁ → A} (h : G₁.IsMultiStep t f f') :
    G₂.IsMultiStep t (fun e => f (φ.eE.symm e)) (fun e => f' (φ.eE.symm e)) := by
  obtain ⟨ht, Qs, hne, hpw, hf⟩ := h
  let S : E₂ → ℤ := fun e => chiSum Qs (φ.eE.symm e)
  have hS : G₂.IsFlow S := (φ.isFlow_iff _).2 (by simpa [S] using isFlow_chiSum Qs)
  have hSv : ∀ e, S e = -1 ∨ S e = 0 ∨ S e = 1 := fun e => sum_chi_mem Qs hpw _
  have hS0 : S ≠ 0 := by
    intro h0; apply sum_chi_ne_zero Qs hpw hne; funext e
    have := congrFun h0 (φ.eE e); simpa [S, chiSum] using this
  obtain ⟨Qs₂, hpw₂, -, hsum₂, -⟩ := circ_decomp S hSv hS
  refine ⟨ht, Qs₂, ?_, hpw₂, ?_⟩
  · rintro rfl; apply hS0; funext e; rw [← hsum₂ e]; simp
  · rw [hf]; funext e; simp only [Pi.add_apply, hsum₂, S, chiSum]

end MGraph

end EulerFlow
