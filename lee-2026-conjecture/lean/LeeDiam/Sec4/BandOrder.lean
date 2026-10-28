/-
LeeDiam/Sec4/BandOrder.lean — Section 4 helpers: the order of the band `B_k` made explicit (from `bandRel`),
comparability (P1)-(P2), and tools for antichains, connected sets and walks (paper 004, short v0.60, sec_chain.tex).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band

namespace LeeDiam.S4

open Band

section Generic

variable {P : Type} [PartialOrder P]

theorem comp_symm {x y : P} (h : Comp x y) : Comp y x := Or.symm h

theorem comp_ne {x y : P} (h : Comp x y) : x ≠ y := by
  rintro rfl
  rcases h with h | h <;> exact lt_irrefl _ h

theorem isAntichainSet_iff_comp {X : Set P} : IsAntichainSet X ↔ ∀ x ∈ X, ∀ y ∈ X, ¬ Comp x y := by
  constructor
  · intro hX x hx y hy h
    rcases h with h | h
    · exact hX hx hy h.ne h.le
    · exact hX hy hx h.ne h.le
  · intro h x hx y hy hne hle
    exact h x hx y hy (Or.inl (lt_of_le_of_ne hle hne))

theorem isAntichainSet_union {X Y : Set P} (hX : IsAntichainSet X) (hY : IsAntichainSet Y)
    (h : ∀ x ∈ X, ∀ y ∈ Y, ¬ Comp x y) : IsAntichainSet (X ∪ Y) := by
  rw [isAntichainSet_iff_comp] at hX hY ⊢
  rintro x (hx | hx) y (hy | hy) hc
  · exact hX x hx y hy hc
  · exact h x hx y hy hc
  · exact h y hy x hx (comp_symm hc)
  · exact hY x hx y hy hc

theorem isAntichainSet_image_iff {Q : Type} [PartialOrder Q] (f : P → Q)
    (hc : ∀ x y, Comp (f x) (f y) ↔ Comp x y) (X : Set P) : IsAntichainSet (f '' X) ↔ IsAntichainSet X := by
  rw [isAntichainSet_iff_comp, isAntichainSet_iff_comp]
  constructor
  · intro h x hx y hy hxy
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ ((hc x y).2 hxy)
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    exact h x hx y hy ((hc x y).1 hxy)

theorem isConnSet_singleton (x : P) : IsConnSet ({x} : Set P) := by
  unfold IsConnSet
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x, Set.mem_singleton x⟩, fun ⟨y, hy⟩ => ?_⟩
  obtain rfl : y = x := hy
  exact SimpleGraph.Reachable.refl _

theorem isConnSet_pair {x y : P} (h : Comp x y) : IsConnSet ({x, y} : Set P) :=
  SimpleGraph.induce_pair_connected_of_adj (G := compGraph P) h

theorem isConnSet_union {S T : Set P} (hS : IsConnSet S) (hT : IsConnSet T) {x y : P} (hx : x ∈ S) (hy : y ∈ T)
    (h : Comp x y) : IsConnSet (S ∪ T) :=
  SimpleGraph.connected_induce_union (G := compGraph P) (SimpleGraph.Connected.preconnected hS)
    (SimpleGraph.Connected.preconnected hT) hx hy h

theorem isConnSet_union_of_inter {S T : Set P} (hS : IsConnSet S) (hT : IsConnSet T) (h : (S ∩ T).Nonempty) :
    IsConnSet (S ∪ T) :=
  SimpleGraph.induce_union_connected (G := compGraph P) (SimpleGraph.Connected.preconnected hS)
    (SimpleGraph.Connected.preconnected hT) h

theorem isConnSet_insert {S : Set P} (hS : IsConnSet S) {x y : P} (hy : y ∈ S) (h : Comp x y) :
    IsConnSet (insert x S) := by
  rw [Set.insert_eq]
  exact isConnSet_union (isConnSet_singleton x) hS (Set.mem_singleton x) hy h

theorem isConnSet_nonempty {S : Set P} (hS : IsConnSet S) : S.Nonempty := by
  obtain ⟨⟨x, hx⟩⟩ := SimpleGraph.Connected.nonempty hS
  exact ⟨x, hx⟩

/-- A connected set cannot be cut: if `Q` holds at one element and fails at another, some comparable pair of
elements of the set crosses the cut. -/
theorem isConnSet_cross {D : Set P} (hD : IsConnSet D) (Q : P → Prop) {x y : P} (hx : x ∈ D) (hy : y ∈ D)
    (hQx : Q x) (hQy : ¬ Q y) : ∃ u ∈ D, ∃ v ∈ D, Q u ∧ ¬ Q v ∧ Comp u v := by
  obtain ⟨p⟩ := SimpleGraph.Connected.preconnected hD ⟨x, hx⟩ ⟨y, hy⟩
  suffices key : ∀ (s t : D) (_ : ((compGraph P).induce D).Walk s t), Q s.1 → ¬ Q t.1 →
      ∃ u ∈ D, ∃ v ∈ D, Q u ∧ ¬ Q v ∧ Comp u v from key _ _ p hQx hQy
  intro s t p
  induction p with
  | nil => intro h1 h2; exact absurd h1 h2
  | @cons s m t hadj p ih =>
    intro h1 h2
    by_cases hm : Q m.1
    · exact ih hm h2
    · exact ⟨s.1, s.2, m.1, m.2, h1, hm, hadj⟩

/-- A set is connected if one of its elements reaches all others through comparable pairs inside the set. -/
theorem isConnSet_of_rtg {D : Set P} {x0 : P} (hx0 : x0 ∈ D)
    (h : ∀ y ∈ D, Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ Comp u v) x0 y) : IsConnSet D := by
  unfold IsConnSet
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x0, hx0⟩, fun ⟨y, hy⟩ => ?_⟩
  have key : ∀ y, Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ Comp u v) x0 y → ∀ hy : y ∈ D,
      ((compGraph P).induce D).Reachable ⟨x0, hx0⟩ ⟨y, hy⟩ := by
    intro y hr
    induction hr with
    | refl => intro _; exact SimpleGraph.Reachable.refl _
    | @tail u v _ huv ih =>
      intro hv
      have hadj : ((compGraph P).induce D).Adj ⟨u, huv.1⟩ ⟨v, hv⟩ := huv.2.2
      exact (ih huv.1).trans hadj.reachable
  exact key y (h y hy) hy

/-- The image of a connected set under an injective map that preserves and reflects comparability is connected. -/
theorem isConnSet_image_iff {Q : Type} [PartialOrder Q] (f : P → Q) (hf : Function.Injective f)
    (hc : ∀ x y, Comp (f x) (f y) ↔ Comp x y) (D : Set P) : IsConnSet (f '' D) ↔ IsConnSet D := by
  unfold IsConnSet
  let e : D ≃ (f '' D) := Equiv.Set.image f D hf
  let iso : (compGraph P).induce D ≃g (compGraph Q).induce (f '' D) :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        exact hc u.1 v.1 }
  exact iso.connected_iff.symm

theorem isWalk_map {Q : Type} [PartialOrder Q] (f : P → Q) (hf : Function.Injective f)
    (hc : ∀ x y, Comp (f x) (f y) ↔ Comp x y) (W : List (Set P)) (hW : IsWalk W) :
    IsWalk (W.map (f '' ·)) := by
  obtain ⟨hne, hanti, hchain⟩ := hW
  refine ⟨by simpa using hne, ?_, ?_⟩
  · intro X hX
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact (isAntichainSet_image_iff f hc Y).2 (hanti Y hY)
  · rw [List.isChain_map]
    refine hchain.imp ?_
    intro X Y h
    show IsConnSet (symmDiff (f '' X) (f '' Y))
    rw [← Set.image_symmDiff hf]
    exact (isConnSet_image_iff f hf hc _).2 h

theorem isWalk_reverse {W : List (Set P)} (hW : IsWalk W) : IsWalk W.reverse := by
  obtain ⟨hne, hanti, hchain⟩ := hW
  refine ⟨by simpa using hne, fun X hX => hanti X (List.mem_reverse.1 hX), ?_⟩
  rw [List.isChain_reverse]
  refine hchain.imp ?_
  intro X Y h
  rwa [symmDiff_comm]

theorem isWalkFromTo_reverse {W : List (Set P)} {A B : Set P} (hW : IsWalkFromTo W A B) :
    IsWalkFromTo W.reverse B A := by
  obtain ⟨hw, hh, hl⟩ := hW
  exact ⟨isWalk_reverse hw, by rw [List.head?_reverse]; exact hl, by rw [List.getLast?_reverse]; exact hh⟩

end Generic

section Band

variable {k : ℕ}

@[simp] theorem a_fst (i : Fin k) : (a i).1 = i := rfl
@[simp] theorem b_fst (i : Fin k) : (b i).1 = i := rfl
@[simp] theorem c_fst (i : Fin k) : (c i).1 = i := rfl
@[simp] theorem a_snd (i : Fin k) : (a i).2 = 0 := rfl
@[simp] theorem b_snd (i : Fin k) : (b i).2 = 1 := rfl
@[simp] theorem c_snd (i : Fin k) : (c i).2 = 2 := rfl

theorem band_ext_iff (x y : Band k) : x = y ↔ x.1.val = y.1.val ∧ x.2.val = y.2.val := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem band_ne_of_row {x y : Band k} (h : x.2 ≠ y.2) : x ≠ y := fun hxy => h (hxy ▸ rfl)

theorem bandRel_iff (x y : Band k) : bandRel k x y ↔
    (x.1.val = y.1.val ∧ x.2.val = 0 ∧ y.2.val = 1) ∨ (x.1.val = y.1.val ∧ x.2.val = 1 ∧ y.2.val = 2) ∨
    (y.1.val = x.1.val + 1 ∧ x.2.val = 0 ∧ y.2.val = 1) ∨ (x.1.val = y.1.val + 1 ∧ x.2.val = 1 ∧ y.2.val = 2) := by
  unfold bandRel
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_one, Fin.val_two]

/-- The order of `B_k`, explicitly (the paper's Lemma 3.1, here proved from the cover relations `bandRel`). -/
def bandLe (x y : Band k) : Prop :=
  x = y ∨
  (x.2.val = 0 ∧ y.2.val = 1 ∧ (y.1.val = x.1.val ∨ y.1.val = x.1.val + 1)) ∨
  (x.2.val = 1 ∧ y.2.val = 2 ∧ (y.1.val = x.1.val ∨ y.1.val + 1 = x.1.val)) ∨
  (x.2.val = 0 ∧ y.2.val = 2 ∧ (y.1.val + 1 = x.1.val ∨ y.1.val = x.1.val ∨ y.1.val = x.1.val + 1))

theorem le_iff_bandLe (x y : Band k) : x ≤ y ↔ bandLe x y := by
  constructor
  · intro h
    change Relation.ReflTransGen (bandRel k) x y at h
    induction h with
    | refl => exact Or.inl rfl
    | @tail u w _ huw ih =>
      rw [bandRel_iff] at huw
      unfold bandLe at ih ⊢
      right
      rcases ih with rfl | ih | ih | ih <;> omega
  · intro h
    change Relation.ReflTransGen (bandRel k) x y
    rcases h with rfl | h | h | h
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ((bandRel_iff x y).2 (by omega))
    · exact Relation.ReflTransGen.single ((bandRel_iff x y).2 (by omega))
    · obtain ⟨h0, h2, hc⟩ := h
      rcases hc with hc | hc | hc
      · -- `c` one column to the left: through `b` of the column of `x`
        let z : Band k := (x.1, 1)
        have hz1 : z.1.val = x.1.val := rfl
        have hz2 : z.2.val = 1 := rfl
        exact Relation.ReflTransGen.head ((bandRel_iff x z).2 (by omega))
          (Relation.ReflTransGen.single ((bandRel_iff z y).2 (by omega)))
      · let z : Band k := (x.1, 1)
        have hz1 : z.1.val = x.1.val := rfl
        have hz2 : z.2.val = 1 := rfl
        exact Relation.ReflTransGen.head ((bandRel_iff x z).2 (by omega))
          (Relation.ReflTransGen.single ((bandRel_iff z y).2 (by omega)))
      · -- `c` one column to the right: through `b` of the column of `y`
        let z : Band k := (y.1, 1)
        have hz1 : z.1.val = y.1.val := rfl
        have hz2 : z.2.val = 1 := rfl
        exact Relation.ReflTransGen.head ((bandRel_iff x z).2 (by omega))
          (Relation.ReflTransGen.single ((bandRel_iff z y).2 (by omega)))

theorem lt_iff_val (x y : Band k) : x < y ↔
    (x.2.val = 0 ∧ y.2.val = 1 ∧ (y.1.val = x.1.val ∨ y.1.val = x.1.val + 1)) ∨
    (x.2.val = 1 ∧ y.2.val = 2 ∧ (y.1.val = x.1.val ∨ y.1.val + 1 = x.1.val)) ∨
    (x.2.val = 0 ∧ y.2.val = 2 ∧ (y.1.val + 1 = x.1.val ∨ y.1.val = x.1.val ∨ y.1.val = x.1.val + 1)) := by
  rw [lt_iff_le_and_ne, le_iff_bandLe]
  unfold bandLe
  constructor
  · rintro ⟨h | h, hne⟩
    · exact absurd h hne
    · exact h
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro rfl
    omega

/-- Comparability in `B_k` ((P1) and (P2) of the paper), with rows and columns as numbers. -/
theorem comp_iff_val (x y : Band k) : Comp x y ↔
    (x.2.val = 1 ∧ y.2.val ≠ 1 ∧ (y.1.val = x.1.val ∨ y.1.val + 1 = x.1.val)) ∨
    (y.2.val = 1 ∧ x.2.val ≠ 1 ∧ (x.1.val = y.1.val ∨ x.1.val + 1 = y.1.val)) ∨
    (((x.2.val = 0 ∧ y.2.val = 2) ∨ (x.2.val = 2 ∧ y.2.val = 0)) ∧ x.1.val ≤ y.1.val + 1 ∧
      y.1.val ≤ x.1.val + 1) := by
  unfold Comp
  rw [lt_iff_val, lt_iff_val]
  have := x.2.isLt
  have := y.2.isLt
  omega

theorem comp_cols {x y : Band k} (h : Comp x y) : x.1.val ≤ y.1.val + 1 ∧ y.1.val ≤ x.1.val + 1 := by
  rw [comp_iff_val] at h
  omega

theorem not_comp_of_far {x y : Band k} (h : x.1.val + 2 ≤ y.1.val ∨ y.1.val + 2 ≤ x.1.val) : ¬ Comp x y := by
  intro hc
  have := comp_cols hc
  omega

theorem not_comp_of_row {x y : Band k} (h : x.2 = y.2) : ¬ Comp x y := by
  rw [comp_iff_val]
  rw [Fin.ext_iff] at h
  omega

theorem comp_of_col {x y : Band k} (h : x.1 = y.1) (hne : x ≠ y) : Comp x y := by
  rw [comp_iff_val]
  rw [Ne, band_ext_iff] at hne
  rw [Fin.ext_iff] at h
  have := x.2.isLt
  have := y.2.isLt
  omega

/-- In an antichain, the element right after an outer element lies in the same row (no `ab`, `ac`, `ca`, `cb`). -/
theorem antichain_next_row {X : Set (Band k)} (hX : IsAntichainSet X) {x y : Band k} (hx : x ∈ X) (hy : y ∈ X)
    (hcol : y.1.val + 1 = x.1.val) (hrow : y.2.val ≠ 1) : x.2 = y.2 := by
  by_contra hne
  rw [Fin.ext_iff] at hne
  apply (isAntichainSet_iff_comp.1 hX) x hx y hy
  rw [comp_iff_val]
  have := x.2.isLt
  have := y.2.isLt
  omega

theorem antichain_col {X : Set (Band k)} (hX : IsAntichainSet X) {x y : Band k} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x.1 = y.1) : x = y := by
  by_contra hne
  exact (isAntichainSet_iff_comp.1 hX) x hx y hy (comp_of_col hxy hne)

theorem isAntichainSet_row (r : Fin 3) (X : Set (Band k)) (h : ∀ x ∈ X, x.2 = r) : IsAntichainSet X := by
  rw [isAntichainSet_iff_comp]
  intro x hx y hy
  exact not_comp_of_row ((h x hx).trans (h y hy).symm)

end Band

end LeeDiam.S4
