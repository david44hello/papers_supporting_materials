/-
EulerFlow/Reduction/Reorient.lean — the step graphs do not depend on the reference directions (tex l.129: "Fix a
reference direction of every edge"): reversing the reference direction of the edges with `R e = true` and negating
the values there is an isomorphism of step graphs.
-/
import EulerFlow.Reduction.Basic

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E] {G : MGraph V E} {R : E → Bool}

/-- A map written in the old reference directions, rewritten in the new ones. -/
def flipOn {M : Type} [Neg M] (R : E → Bool) (x : E → M) : E → M := fun e => if R e then -x e else x e

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem flipOn_flipOn {M : Type} [InvolutiveNeg M] (x : E → M) : flipOn R (flipOn R x) = x := by
  funext e; unfold flipOn; split_ifs <;> simp

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
theorem reorient_reorient : (G.reorient R).reorient R = G := by
  cases G with
  | mk src tgt =>
    simp only [reorient, MGraph.mk.injEq]
    constructor <;> funext e <;> by_cases h : R e <;> simp [h]

omit [DecidableEq E] in
theorem boundary_flipOn {M : Type} [AddCommGroup M] (x : E → M) (z : V) :
    (G.reorient R).boundary (flipOn R x) z = G.boundary x z := by
  rw [boundary_eq_sum_bdryTerm, boundary_eq_sum_bdryTerm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : R e <;> simp only [bdryTerm, reorient, flipOn, h, ite_true, ite_false, Bool.false_eq_true]
  by_cases hs : G.src e = z <;> by_cases ht : G.tgt e = z <;> simp [hs, ht]

omit [DecidableEq E] in
theorem isIFlow_flipOn_iff {M : Type} [AddCommGroup M] {I : Set M} (hI : ∀ x ∈ I, -x ∈ I) (x : E → M) :
    (G.reorient R).IsIFlow I (flipOn R x) ↔ G.IsIFlow I x := by
  simp only [IsIFlow, isFlow_iff_boundary, boundary_flipOn]
  refine and_congr Iff.rfl ⟨fun h e => ?_, fun h e => ?_⟩
  · have := h e; unfold flipOn at this; split_ifs at this
    · simpa using hI _ this
    · exact this
  · unfold flipOn; split_ifs
    · exact hI _ (h e)
    · exact h e

omit [Fintype E] [DecidableEq E] in
theorem flipOn_add_smul {A : Type} [AddCommGroup A] (f : E → A) (h : E → ℤ) (t : A) :
    flipOn R (f + fun e => h e • t) = flipOn R f + fun e => flipOn R h e • t := by
  funext e
  simp only [flipOn, Pi.add_apply]
  by_cases hR : R e
  · simp only [hR, ite_true, neg_smul]; abel
  · simp [hR]

/-- Reversing reference directions keeps every pair of `I`-flows `T`-joined. -/
theorem preconnected_reorient {A : Type} [AddCommGroup A] {I T : Set A} (hI : ∀ x ∈ I, -x ∈ I)
    (h : (G.stepGraph I T).Preconnected) : ((G.reorient R).stepGraph I T).Preconnected := by
  intro g₁ g₂
  let φ : {f : E → A // G.IsIFlow I f} → {f : E → A // (G.reorient R).IsIFlow I f} :=
    fun f => ⟨flipOn R f.1, (isIFlow_flipOn_iff hI f.1).2 f.2⟩
  have k : ∀ g : {f : E → A // (G.reorient R).IsIFlow I f}, ∃ f, φ f = g := by
    intro g
    refine ⟨⟨flipOn R g.1, (isIFlow_flipOn_iff (G := G) (R := R) hI _).1 ?_⟩, Subtype.ext (flipOn_flipOn g.1)⟩
    rw [flipOn_flipOn]; exact g.2
  obtain ⟨f₁, rfl⟩ := k g₁
  obtain ⟨f₂, rfl⟩ := k g₂
  refine reachable_transport φ (fun f Q t hft => ⟨flipOn R Q.chi, fun e => ?_, ?_, flipOn_add_smul _ _ _⟩) (h f₁ f₂)
  · unfold flipOn; split_ifs <;> rcases Q.chi_mem e with h | h | h <;> simp [h]
  · rw [isFlow_iff_boundary]; intro z; rw [boundary_flipOn, (isFlow_iff_boundary _ _).1 Q.isFlow_chi]

end MGraph

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] in
/-- Section 2 (tex l.129): the step graphs do not depend on the choice of the reference directions; exactly the
Statements type. -/
theorem sec2_ref_dir_indep_proved {A : Type} [AddCommGroup A] (G : MGraph V E) (R : E → Bool) (I T : Set A)
    (hI : ∀ x ∈ I, -x ∈ I) :
    ((G.reorient R).stepGraph I T).Preconnected ↔ (G.stepGraph I T).Preconnected := by
  refine ⟨fun h => ?_, preconnected_reorient hI⟩
  have := preconnected_reorient (R := R) hI h
  rwa [reorient_reorient] at this

end EulerFlow
