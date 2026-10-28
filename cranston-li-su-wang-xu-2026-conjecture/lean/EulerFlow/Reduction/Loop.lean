/-
EulerFlow/Reduction/Loop.lean — Lemma 3.1 of paper 002 (loops, tex l.222-232), for `I`-flows: if any two
`I`-flows of `G - l` are `T`-joined, then so are any two `I`-flows of `G`.
-/
import EulerFlow.Reduction.Basic

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} {G : MGraph V E} [DecidableEq V] [Fintype E] [DecidableEq E] {l : E}

/-- A map on `E(G - l)` together with the value `a` on `l`. -/
def extLoop {M : Type} (l : E) (g : {x : E // x ≠ l} → M) (a : M) : E → M :=
  fun x => if h : x = l then a else g ⟨x, h⟩

section Ext

variable {M : Type} [AddCommGroup M]

omit [Fintype E] [AddCommGroup M] in
theorem extLoop_restrict (f : E → M) : extLoop l (fun x => f x.1) (f l) = f := by
  funext x; unfold extLoop; split_ifs with h <;> simp [h]

omit [Fintype E] [DecidableEq E] in
/-- A loop adds the same term to both sides of the flow condition at its vertex (tex l.227). -/
theorem bdryTerm_loop (hl : G.IsLoop l) (x : E → M) (z : V) : G.bdryTerm x z l = 0 := by
  unfold IsLoop at hl; simp [bdryTerm, hl]

theorem boundary_extLoop (hl : G.IsLoop l) (g : {x : E // x ≠ l} → M) (a : M) (z : V) :
    G.boundary (extLoop l g a) z = (G.deleteEdge l).boundary g z := by
  rw [boundary_eq_sum_bdryTerm, boundary_eq_sum_bdryTerm, Fintype.sum_eq_add_sum_subtype_ne _ l,
    bdryTerm_loop hl, zero_add]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [bdryTerm, extLoop, dite_eq_right x.2, deleteEdge]
  rfl

theorem isFlow_extLoop_iff (hl : G.IsLoop l) (g : {x : E // x ≠ l} → M) (a : M) :
    G.IsFlow (extLoop l g a) ↔ (G.deleteEdge l).IsFlow g := by
  simp only [isFlow_iff_boundary, boundary_extLoop hl]

/-- A flow of `G` is a flow of `G - l` together with a value on `l` (tex l.227-228). -/
theorem isIFlow_extLoop_iff (hl : G.IsLoop l) {I : Set M} (g : {x : E // x ≠ l} → M) {a : M} (ha : a ∈ I) :
    G.IsIFlow I (extLoop l g a) ↔ (G.deleteEdge l).IsIFlow I g := by
  rw [IsIFlow, IsIFlow, isFlow_extLoop_iff hl]
  refine and_congr Iff.rfl ⟨fun h x => ?_, fun h x => ?_⟩
  · have := h x.1; rwa [extLoop, dite_eq_right x.2] at this
  · unfold extLoop; split_ifs with hx
    · exact ha
    · exact h _

theorem isIFlow_restrict (hl : G.IsLoop l) {I : Set M} {f : E → M} (hf : G.IsIFlow I f) :
    (G.deleteEdge l).IsIFlow I (fun x => f x.1) := by
  rw [← isIFlow_extLoop_iff hl _ (hf.2 l), extLoop_restrict]; exact hf

omit [Fintype E] in
theorem extLoop_add_smul (g : {x : E // x ≠ l} → M) (h : {x : E // x ≠ l} → ℤ) (t a : M) :
    extLoop l (g + fun x => h x • t) a = extLoop l g a + fun x => extLoop l h 0 x • t := by
  funext x; by_cases hx : x = l <;> simp [extLoop, hx]

omit [Fintype E] in
theorem extLoop_value (g : {x : E // x ≠ l} → M) (a b : M) :
    extLoop l g b = extLoop l g a + fun x => extLoop l (0 : {x : E // x ≠ l} → ℤ) 1 x • (b - a) := by
  funext x; by_cases hx : x = l <;> simp [extLoop, hx]

omit [Fintype E] in
theorem extLoop_mem_int {h : {x : E // x ≠ l} → ℤ} (hv : ∀ x, h x = -1 ∨ h x = 0 ∨ h x = 1) {c : ℤ}
    (hc : c = -1 ∨ c = 0 ∨ c = 1) (x : E) : extLoop l h c x = -1 ∨ extLoop l h c x = 0 ∨ extLoop l h c x = 1 := by
  unfold extLoop; split_ifs
  · exact hc
  · exact hv _

end Ext

/-- Deleting a loop at `w` lowers the degree of `w` by `2` and keeps the other degrees (tex l.408). -/
theorem degree_deleteEdge (hl : G.IsLoop l) (z : V) :
    (G.deleteEdge l).degree z + (if G.src l = z then 2 else 0) = G.degree z := by
  rw [degree_eq_sum_endCount, degree_eq_sum_endCount, Fintype.sum_eq_add_sum_subtype_ne _ l]
  have h1 : G.endCount z l = if G.src l = z then 2 else 0 := by
    unfold IsLoop at hl; simp only [endCount, ← hl]; split_ifs <;> rfl
  have h2 : ∑ x : {x : E // x ≠ l}, (G.deleteEdge l).endCount z x = ∑ x : {x : E // x ≠ l}, G.endCount z x.1 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [endCount, deleteEdge]; rfl
  rw [h1, h2, add_comm]

/-- Deleting a loop keeps a graph even. -/
theorem isEven_deleteEdge [Fintype V] (hl : G.IsLoop l) (hev : G.IsEven) : (G.deleteEdge l).IsEven := by
  intro z
  have h := degree_deleteEdge hl z
  have hz := hev z
  rw [← h] at hz
  split_ifs at hz
  · exact (Nat.even_add.1 hz).2 (by decide)
  · simpa using hz

/-- Lemma 3.1 for `I`-flows (tex l.222-232). `(T1)` for `I`: any two elements of `I` are the ends of a chain in `I`
whose neighbours differ by an element of `T`. -/
theorem loop_preconnected {A : Type} [AddCommGroup A] {I T : Set A} (hT0 : (0 : A) ∉ T)
    (hT1 : ∀ a b, a ∈ I → b ∈ I → Relation.ReflTransGen (fun x y : A => y ∈ I ∧ y - x ∈ T) a b)
    (hl : G.IsLoop l) (h : ((G.deleteEdge l).stepGraph I T).Preconnected) : (G.stepGraph I T).Preconnected := by
  intro f₁ f₂
  -- the flows `ext g a` of `G`, for an `I`-flow `g` of `G - l` and `a ∈ I`
  let ext : (g : {g // (G.deleteEdge l).IsIFlow I g}) → (a : A) → a ∈ I → {f // G.IsIFlow I f} :=
    fun g a ha => ⟨extLoop l g.1 a, (isIFlow_extLoop_iff hl g.1 ha).2 g.2⟩
  let r₁ : {g // (G.deleteEdge l).IsIFlow I g} := ⟨_, isIFlow_restrict hl f₁.2⟩
  let r₂ : {g // (G.deleteEdge l).IsIFlow I g} := ⟨_, isIFlow_restrict hl f₂.2⟩
  have ha₁ : f₁.1 l ∈ I := f₁.2.2 l
  have ha₂ : f₂.1 l ∈ I := f₂.2.2 l
  -- join the restrictions by T-steps of G - l (the value on l stays f₁(l))
  have hstep1 : (G.stepGraph I T).Reachable (ext r₁ _ ha₁) (ext r₂ _ ha₁) := by
    refine reachable_transport (fun g => ext g _ ha₁) (fun g Q t hft => ?_) (h r₁ r₂)
    refine ⟨extLoop l Q.chi 0, extLoop_mem_int Q.chi_mem (by simp), ?_, ?_⟩
    · exact (isFlow_extLoop_iff hl _ _).2 Q.isFlow_chi
    · exact extLoop_add_smul _ _ _ _
  -- then change the value on l along a chain of (T1)
  have hstep2 : ∀ c, Relation.ReflTransGen (fun x y : A => y ∈ I ∧ y - x ∈ T) (f₁.1 l) c →
      ∃ hc : c ∈ I, (G.stepGraph I T).Reachable (ext r₂ _ ha₁) (ext r₂ c hc) := by
    intro c hc
    induction hc with
    | refl => exact ⟨ha₁, SimpleGraph.Reachable.refl _⟩
    | tail _ hcd ih =>
      obtain ⟨hcI, hreach⟩ := ih
      refine ⟨hcd.1, hreach.trans ?_⟩
      refine reachable_of_circ _ _ (extLoop l 0 1) (extLoop_mem_int (fun _ => by simp) (by simp)) ?_ _ hcd.2
        (fun h0 => hT0 (h0 ▸ hcd.2)) (extLoop_value _ _ _)
      exact (isFlow_extLoop_iff hl _ _).2 isFlow_zero
  obtain ⟨_, hreach2⟩ := hstep2 _ (hT1 _ _ ha₁ ha₂)
  have e₁ : ext r₁ _ ha₁ = f₁ := Subtype.ext (extLoop_restrict f₁.1)
  have e₂ : ext r₂ _ ha₂ = f₂ := Subtype.ext (extLoop_restrict f₂.1)
  rw [← e₁, ← e₂]
  exact hstep1.trans hreach2

end MGraph

end EulerFlow
