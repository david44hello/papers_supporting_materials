/-
EulerFlow/Reduction/Expand.lean — the blow-up step of the proof of Theorem 2.3 of paper 002 (tex l.450-456): a
vertex `v` of degree `d ≥ 6` is replaced by a triangle `x₁ x₂ x₃` with two ends of `v` at `x₁`, two at `x₂`, the
other `d - 4` at `x₃`. The new graph is even, loopless, has `Φ(G⁺) = Φ(G) - 2`, the triangle is isolated, and
`G⁺/Δ` is isomorphic to `G`. Here `x₁ = inr 0`, `x₂ = inr 1`, `x₃ = inl v`, and the triangle edges are
`d₁₂ = inr 0`, `d₂₃ = inr 1`, `d₃₁ = inr 2`.
-/
import EulerFlow.Reduction.Iso

namespace EulerFlow

open Finset

namespace MGraph

variable {V E : Type} [DecidableEq V] [Fintype E] [DecidableEq E] (G : MGraph V E)

/-- `Φ(G) = Σ_v max(deg v - 4, 0)` (tex l.450); natural subtraction is the `max`. -/
def phi [Fintype V] : ℕ := ∑ v, (G.degree v - 4)

/-- The vertex of the end `i` after the blow-up. -/
def newEnd (S₁ S₂ : Finset (E × Bool)) (i : E × Bool) : V ⊕ Fin 2 :=
  if i ∈ S₁ then .inr 0 else if i ∈ S₂ then .inr 1 else .inl (G.endVertex i)

/-- `G⁺` (tex l.451-453). -/
def expandAt (v : V) (S₁ S₂ : Finset (E × Bool)) : MGraph (V ⊕ Fin 2) (E ⊕ Fin 3) where
  src := fun e => match e with
    | .inl e => G.newEnd S₁ S₂ (e, false)
    | .inr k => ![.inr 0, .inr 1, .inl v] k
  tgt := fun e => match e with
    | .inl e => G.newEnd S₁ S₂ (e, true)
    | .inr k => ![.inr 1, .inl v, .inr 0] k

/-- The vertices `x₁, x₂, x₃` of the triangle. -/
abbrev triX (v : V) : Finset (V ⊕ Fin 2) := {.inr 0, .inr 1, .inl v}

/-- The three edges of the triangle. -/
abbrev triD : Finset (E ⊕ Fin 3) := {.inr 0, .inr 1, .inr 2}

/-- The hypotheses on the two pairs of ends moved to `x₁` and `x₂`. -/
structure ExpandData (v : V) (S₁ S₂ : Finset (E × Bool)) : Prop where
  sub₁ : ∀ i ∈ S₁, G.endVertex i = v
  sub₂ : ∀ i ∈ S₂, G.endVertex i = v
  disj : Disjoint S₁ S₂
  card₁ : S₁.card = 2
  card₂ : S₂.card = 2

variable {G}

section Ends

variable {v : V} {S₁ S₂ : Finset (E × Bool)} (hd : G.ExpandData v S₁ S₂)
include hd

omit [Fintype E] in
theorem newEnd_mem_triX_iff (i : E × Bool) : G.newEnd S₁ S₂ i ∈ triX v ↔ G.endVertex i = v := by
  unfold newEnd
  split_ifs with h1 h2
  · simp [hd.sub₁ i h1]
  · simp [hd.sub₂ i h2]
  · simp

omit [Fintype E] hd in
theorem newEnd_of_not_mem (i : E × Bool) (h : G.newEnd S₁ S₂ i ∉ triX v) :
    G.newEnd S₁ S₂ i = .inl (G.endVertex i) := by
  unfold newEnd at *
  split_ifs at h ⊢ with h1 h2 <;> simp_all

end Ends

omit [DecidableEq V] [Fintype E] in
theorem endVertex_expandAt_inl {v : V} {S₁ S₂ : Finset (E × Bool)} (e : E) (b : Bool) :
    (G.expandAt v S₁ S₂).endVertex (.inl e, b) = G.newEnd S₁ S₂ (e, b) := by
  cases b <;> rfl

/-! ### Degrees of `G⁺` (tex l.453-454) -/

section Degree

variable [Fintype V] {v : V} {S₁ S₂ : Finset (E × Bool)}

omit [Fintype V] in
theorem sum_endCount_inl (w : V ⊕ Fin 2) :
    ∑ e : E, (G.expandAt v S₁ S₂).endCount w (.inl e) = (univ.filter fun i => G.newEnd S₁ S₂ i = w).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [endCount, expandAt, Fintype.sum_bool, add_comm]
  rfl

omit [Fintype V] in
theorem degree_expandAt (w : V ⊕ Fin 2) :
    (G.expandAt v S₁ S₂).degree w = (univ.filter fun i => G.newEnd S₁ S₂ i = w).card +
      ∑ k : Fin 3, (G.expandAt v S₁ S₂).endCount w (.inr k) := by
  rw [degree_eq_sum_endCount, Fintype.sum_sum_type, sum_endCount_inl]

variable (hd : G.ExpandData v S₁ S₂)
include hd

omit [Fintype V] hd in
theorem filter_newEnd_inr0 : (univ.filter fun i => G.newEnd S₁ S₂ i = .inr 0) = S₁ := by
  ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : i ∈ S₁ <;> by_cases h2 : i ∈ S₂ <;> simp [newEnd, h1, h2]

omit [Fintype V] in
theorem filter_newEnd_inr1 : (univ.filter fun i => G.newEnd S₁ S₂ i = .inr 1) = S₂ := by
  ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : i ∈ S₁
  · have h2 : i ∉ S₂ := Finset.disjoint_left.1 hd.disj h1
    simp [newEnd, h1, h2]
  · by_cases h2 : i ∈ S₂ <;> simp [newEnd, h1, h2]

omit [Fintype V] hd in
theorem filter_newEnd_inl (y : V) :
    (univ.filter fun i => G.newEnd S₁ S₂ i = .inl y) =
      univ.filter fun i => i ∉ S₁ ∧ i ∉ S₂ ∧ G.endVertex i = y := by
  ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : i ∈ S₁ <;> by_cases h2 : i ∈ S₂ <;> simp [newEnd, h1, h2]

omit [Fintype V] in
theorem degree_expandAt_inr0 : (G.expandAt v S₁ S₂).degree (.inr 0) = 4 := by
  rw [degree_expandAt, filter_newEnd_inr0, hd.card₁]
  simp [Fin.sum_univ_three, endCount, expandAt]

omit [Fintype V] in
theorem degree_expandAt_inr1 : (G.expandAt v S₁ S₂).degree (.inr 1) = 4 := by
  rw [degree_expandAt, filter_newEnd_inr1 hd, hd.card₂]
  simp [Fin.sum_univ_three, endCount, expandAt]

omit [Fintype V] in
theorem degree_expandAt_ne {y : V} (hy : y ≠ v) : (G.expandAt v S₁ S₂).degree (.inl y) = G.degree y := by
  rw [degree_expandAt, filter_newEnd_inl]
  have h1 : (univ.filter fun i => i ∉ S₁ ∧ i ∉ S₂ ∧ G.endVertex i = y) =
      univ.filter fun i : E × Bool => G.endVertex i = y := by
    ext i; simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2.2
    · intro h
      exact ⟨fun h' => hy (h ▸ hd.sub₁ i h'), fun h' => hy (h ▸ hd.sub₂ i h'), h⟩
  rw [h1, degree]
  simp [Fin.sum_univ_three, endCount, expandAt, Ne.symm hy]

omit [Fintype V] in
theorem degree_expandAt_v :
    (G.expandAt v S₁ S₂).degree (.inl v) = G.degree v - 4 + 2 := by
  rw [degree_expandAt, filter_newEnd_inl]
  have h1 : (univ.filter fun i => i ∉ S₁ ∧ i ∉ S₂ ∧ G.endVertex i = v) =
      (univ.filter fun i : E × Bool => G.endVertex i = v) \ (S₁ ∪ S₂) := by
    ext i; simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_union, not_or]; tauto
  have hsub : S₁ ∪ S₂ ⊆ univ.filter fun i : E × Bool => G.endVertex i = v := by
    intro i hi; rcases mem_union.1 hi with h | h
    · simpa using hd.sub₁ i h
    · simpa using hd.sub₂ i h
  rw [h1, card_sdiff_of_subset hsub, card_union_of_disjoint hd.disj, hd.card₁, hd.card₂]
  have : (∑ k : Fin 3, (G.expandAt v S₁ S₂).endCount (.inl v) (.inr k)) = 2 := by
    simp [Fin.sum_univ_three, endCount, expandAt]
  rw [this]; rfl

omit [Fintype V] in
theorem isEven_expandAt (hev : G.IsEven) (hv : 4 ≤ G.degree v) : (G.expandAt v S₁ S₂).IsEven := by
  intro w
  rcases w with y | k
  · by_cases hy : y = v
    · subst hy
      rw [degree_expandAt_v hd]
      obtain ⟨m, hm⟩ := hev y
      exact ⟨m - 1, by omega⟩
    · rw [degree_expandAt_ne hd hy]; exact hev y
  · have hk : k = 0 ∨ k = 1 := by fin_cases k <;> simp
    rcases hk with rfl | rfl
    · rw [degree_expandAt_inr0 hd]; exact ⟨2, rfl⟩
    · rw [degree_expandAt_inr1 hd]; exact ⟨2, rfl⟩

/-- `Φ(G⁺) = Φ(G) - 2` (tex l.454). -/
theorem phi_expandAt (hv : 6 ≤ G.degree v) : (G.expandAt v S₁ S₂).phi + 2 = G.phi := by
  unfold phi
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, degree_expandAt_inr0 hd, degree_expandAt_inr1 hd,
    ← Finset.add_sum_erase _ _ (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v),
    degree_expandAt_v hd]
  have : ∑ y ∈ univ.erase v, ((G.expandAt v S₁ S₂).degree (.inl y) - 4) = ∑ y ∈ univ.erase v, (G.degree y - 4) :=
    Finset.sum_congr rfl fun y hy => by rw [degree_expandAt_ne hd (Finset.ne_of_mem_erase hy)]
  rw [this]
  omega

end Degree

/-! ### `G⁺` is loopless, `Δ` is isolated, `G⁺/Δ ≅ G` (tex l.454-455) -/

section Shape

variable {v : V} {S₁ S₂ : Finset (E × Bool)} (hd : G.ExpandData v S₁ S₂) (hG : G.Loopless)
include hd hG

omit [Fintype E] in
theorem loopless_expandAt : (G.expandAt v S₁ S₂).Loopless := by
  intro e he
  unfold IsLoop at he
  rcases e with e | k
  · have hl := hG e; unfold IsLoop at hl
    simp only [expandAt] at he
    have hmem : G.newEnd S₁ S₂ (e, false) ∈ triX v ↔ G.newEnd S₁ S₂ (e, true) ∈ triX v := by rw [he]
    rw [newEnd_mem_triX_iff hd, newEnd_mem_triX_iff hd] at hmem
    by_cases h0 : G.endVertex (e, false) = v
    · exact hl (h0.trans (hmem.1 h0).symm)
    · have h0' : G.endVertex (e, true) ≠ v := fun h => h0 (hmem.2 h)
      rw [newEnd_of_not_mem _ (fun h => h0 ((newEnd_mem_triX_iff hd _).1 h)),
        newEnd_of_not_mem _ (fun h => h0' ((newEnd_mem_triX_iff hd _).1 h))] at he
      exact hl (Sum.inl_injective he)
  · fin_cases k <;> simp [expandAt] at he

omit [Fintype E] in
theorem isIsolatedTriangle_expandAt :
    (G.expandAt v S₁ S₂).IsIsolatedTriangle (.inr 0) (.inr 1) (.inl v) (.inr 0) (.inr 1) (.inr 2) where
  x_ne₁₂ := by simp
  x_ne₂₃ := by simp
  x_ne₃₁ := by simp
  joins₁₂ := Or.inl ⟨rfl, rfl⟩
  joins₂₃ := Or.inl ⟨rfl, rfl⟩
  joins₃₁ := Or.inl ⟨rfl, rfl⟩
  only := by
    intro e hs ht
    rcases e with e | k
    · exfalso
      have hl := hG e; unfold IsLoop at hl
      have h1 := (newEnd_mem_triX_iff hd (e, false)).1 hs
      have h2 := (newEnd_mem_triX_iff hd (e, true)).1 ht
      exact hl (h1.trans h2.symm)
    · fin_cases k <;> simp

end Shape

omit [Fintype E] in
theorem inr_mem_triD' (k : Fin 3) : (.inr k : E ⊕ Fin 3) ∈ (triD : Finset (E ⊕ Fin 3)) := by
  fin_cases k <;> simp

theorem inr_mem_triX (v : V) (k : Fin 2) : (.inr k : V ⊕ Fin 2) ∈ triX v := by
  fin_cases k <;> simp

/-- The edge of `G` behind an edge of `G⁺/Δ`. -/
def leftEdge (e : {e : E ⊕ Fin 3 // e ∉ (triD : Finset (E ⊕ Fin 3))}) : E :=
  match e with
  | ⟨.inl e, _⟩ => e
  | ⟨.inr k, h⟩ => absurd (inr_mem_triD' k) h

/-- The vertex of `G` behind a vertex of `G⁺/Δ` (the new vertex is `v`). -/
def leftVertex (v : V) (y : Option {y : V ⊕ Fin 2 // y ∉ triX v}) : V :=
  match y with
  | none => v
  | some ⟨.inl y, _⟩ => y
  | some ⟨.inr k, h⟩ => absurd (inr_mem_triX v k) h

theorem leftVertex_some_eq {v : V} {y : V ⊕ Fin 2} {z : V} (hy : y ∉ triX v) (h : y = .inl z) :
    leftVertex v (some ⟨y, hy⟩) = z := by
  subst h; rfl

/-- `G⁺/Δ ≅ G` (tex l.455: "Also `G = G⁺/Δ`"). -/
def expandIso {v : V} {S₁ S₂ : Finset (E × Bool)} (hd : G.ExpandData v S₁ S₂) :
    EdgeIso ((G.expandAt v S₁ S₂).contract (triX v) triD) G where
  eE := {
    toFun := leftEdge
    invFun := fun e => ⟨.inl e, by simp⟩
    left_inv := by
      rintro ⟨e | k, h⟩
      · rfl
      · exact absurd (inr_mem_triD' k) h
    right_inv := fun e => rfl }
  fV := leftVertex v
  inj := by
    rintro (_ | ⟨y | k, hy⟩) (_ | ⟨y' | k', hy'⟩) h <;> simp only [leftVertex] at h
    · rfl
    · exact absurd (h ▸ (by simp : (.inl v : V ⊕ Fin 2) ∈ triX v)) hy'
    · exact absurd (inr_mem_triX v k') hy'
    · exact absurd (h ▸ (by simp : (.inl v : V ⊕ Fin 2) ∈ triX v)) hy
    · subst h; rfl
    · exact absurd (inr_mem_triX v k') hy'
    · exact absurd (inr_mem_triX v k) hy
    · exact absurd (inr_mem_triX v k) hy
    · exact absurd (inr_mem_triX v k) hy
  src := by
    rintro ⟨e | k, h⟩
    · show G.src e = leftVertex v (((G.expandAt v S₁ S₂).contract (triX v) triD).src ⟨.inl e, h⟩)
      simp only [contract]
      split_ifs with hm
      · show G.src e = v
        exact (newEnd_mem_triX_iff hd (e, false)).1 hm
      · rw [leftVertex_some_eq (y := (G.expandAt v S₁ S₂).src (.inl e)) hm
          (newEnd_of_not_mem (e, false) hm)]
        rfl
    · exact absurd (inr_mem_triD' k) h
  tgt := by
    rintro ⟨e | k, h⟩
    · show G.tgt e = leftVertex v (((G.expandAt v S₁ S₂).contract (triX v) triD).tgt ⟨.inl e, h⟩)
      simp only [contract]
      split_ifs with hm
      · show G.tgt e = v
        exact (newEnd_mem_triX_iff hd (e, true)).1 hm
      · rw [leftVertex_some_eq (y := (G.expandAt v S₁ S₂).tgt (.inl e)) hm
          (newEnd_of_not_mem (e, true) hm)]
        rfl
    · exact absurd (inr_mem_triD' k) h

/-- Two disjoint pairs of ends at a vertex of degree at least `4`. -/
theorem exists_expandData [Fintype V] {v : V} (hv : 4 ≤ G.degree v) :
    ∃ S₁ S₂ : Finset (E × Bool), G.ExpandData v S₁ S₂ := by
  set T := univ.filter fun i : E × Bool => G.endVertex i = v
  have hT : T.card = G.degree v := rfl
  obtain ⟨S₁, hS₁, hc₁⟩ := le_card_iff_exists_subset_card.mp (show 2 ≤ T.card by omega)
  obtain ⟨S₂, hS₂, hc₂⟩ := le_card_iff_exists_subset_card.mp
    (show 2 ≤ (T \ S₁).card by rw [card_sdiff_of_subset hS₁]; omega)
  refine ⟨S₁, S₂, fun i hi => ?_, fun i hi => ?_, ?_, hc₁, hc₂⟩
  · simpa [T] using hS₁ hi
  · simpa [T] using (mem_sdiff.1 (hS₂ hi)).1
  · exact Finset.disjoint_left.2 fun i h1 h2 => (mem_sdiff.1 (hS₂ h2)).2 h1

/-- The blow-up step of Theorem 2.3 (tex l.450-456), in one statement (the interface for Theorem 2.5 (b)). -/
theorem exists_expand [Fintype V] (hG : G.Loopless) (hev : G.IsEven) {v : V} (hv : 6 ≤ G.degree v) :
    ∃ S₁ S₂ : Finset (E × Bool),
      (G.expandAt v S₁ S₂).IsIsolatedTriangle (.inr 0) (.inr 1) (.inl v) (.inr 0) (.inr 1) (.inr 2) ∧
      (G.expandAt v S₁ S₂).Loopless ∧ (G.expandAt v S₁ S₂).IsEven ∧
      (G.expandAt v S₁ S₂).phi + 2 = G.phi ∧
      Nonempty (EdgeIso ((G.expandAt v S₁ S₂).contract (triX v) triD) G) := by
  obtain ⟨S₁, S₂, hd⟩ := exists_expandData (G := G) (show 4 ≤ G.degree v by omega)
  exact ⟨S₁, S₂, isIsolatedTriangle_expandAt hd hG, loopless_expandAt hd hG,
    isEven_expandAt hd hev (by omega), phi_expandAt hd hv, ⟨expandIso hd⟩⟩

end MGraph

end EulerFlow
