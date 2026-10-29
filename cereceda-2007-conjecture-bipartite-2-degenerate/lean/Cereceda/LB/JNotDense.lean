/-
Cereceda/LB/JNotDense.lean — J_ℓ is connected, has girth 6 and minimum degree ≥ 2, and is not 3-colour-dense
(short v3.90 l. 726-733).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.ColourDense
import Cereceda.LB.GirthJ

namespace Cereceda

namespace JNotDense

open SimpleGraph

/-! ### Short cycles force small girth -/

/-- A triangle `a b c` gives `egirth ≤ 3`. -/
theorem egirth_le_three {V : Type} {G : SimpleGraph V} {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hca : G.Adj c a) : G.egirth ≤ 3 := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hw : w.IsCycle := by
    have hac : a ≠ c := hca.ne.symm
    rw [Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [Walk.isPath_def, hbc.ne, hca.ne, hab.ne.symm]
    · simp [hac, hab.ne, hbc.ne]
  have := hw.egirth_le_length
  simpa [w] using this

/-- A closed walk `a b c d a` with `a ≠ c` and `b ≠ d` (a 4-cycle) gives `egirth ≤ 4`. -/
theorem egirth_le_four {V : Type} {G : SimpleGraph V} {a b c d : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) (hac : a ≠ c) (hbd : b ≠ d) : G.egirth ≤ 4 := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
  have hw : w.IsCycle := by
    rw [Walk.cons_isCycle_iff]
    refine ⟨?_, ?_⟩
    · simp [Walk.isPath_def, hbc.ne, hcd.ne, hda.ne, hbd, hab.ne.symm, hac.symm]
    · simp [hac, hbd, hab.ne, hda.ne.symm]
  have := hw.egirth_le_length
  simpa [w] using this

theorem not_six_le_of_le_four {V : Type} {G : SimpleGraph V} (h6 : 6 ≤ G.egirth) (h4 : G.egirth ≤ 4) : False := by
  have := h6.trans h4
  norm_num at this

/-! ### Degrees -/

/-- A vertex of degree at least two has two different neighbours. -/
theorem two_nbrs {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {x : V}
    (hx : 2 ≤ G.degree x) : ∃ a b, G.Adj x a ∧ G.Adj x b ∧ a ≠ b := by
  rw [← card_neighborFinset_eq_degree] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hx
  exact ⟨a, b, (mem_neighborFinset _ _ _).1 ha, (mem_neighborFinset _ _ _).1 hb, hab⟩

/-- A vertex of degree at least two with every neighbour in `{a, b}` is adjacent to `a` and to `b`. -/
theorem adj_both {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x a b : V}
    (hx : 2 ≤ G.degree x) (hN : ∀ y, G.Adj x y → y = a ∨ y = b) : G.Adj x a ∧ G.Adj x b := by
  have hsub : G.neighborFinset x ⊆ {a, b} := by
    intro y hy
    rcases hN y ((mem_neighborFinset _ _ _).1 hy) with rfl | rfl <;> simp
  have hcard : ({a, b} : Finset V).card ≤ (G.neighborFinset x).card := by
    rw [card_neighborFinset_eq_degree]
    exact (Finset.card_le_two).trans hx
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨(mem_neighborFinset _ _ _).1 ?_, (mem_neighborFinset _ _ _).1 ?_⟩ <;> rw [heq] <;> simp

/-- Two different vertices adjacent to a common vertex `x` give `2 ≤ degree x`. -/
theorem two_le_degree {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x a b : V}
    (ha : G.Adj x a) (hb : G.Adj x b) (hab : a ≠ b) : 2 ≤ G.degree x := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset x := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> simpa
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hab] at this

/-! ### The component `D` (copied from Cereceda/Intro/ColourDense.lean, namespace `ColourDense`) -/

/-- Copied from `Cereceda.ColourDense.self_mem_compMinus` (Cereceda/Intro/ColourDense.lean). -/
theorem self_mem_compMinus {V : Type} {H : SimpleGraph V} {S : Set V} {u : V} (hu : u ∉ S) :
    u ∈ compMinus H S u :=
  ⟨hu, hu, SimpleGraph.Reachable.refl _⟩

/-- Copied from `Cereceda.ColourDense.not_mem_of_mem_compMinus` (Cereceda/Intro/ColourDense.lean). -/
theorem not_mem_of_mem_compMinus {V : Type} {H : SimpleGraph V} {S : Set V} {u w : V}
    (hw : w ∈ compMinus H S u) : w ∉ S := by
  obtain ⟨_, hw', _⟩ := hw
  exact hw'

/-- Copied from `Cereceda.ColourDense.mem_compMinus_of_adj` (Cereceda/Intro/ColourDense.lean): a neighbour outside
`S` of a vertex of the component `D` lies in `D`. -/
theorem mem_compMinus_of_adj {V : Type} {H : SimpleGraph V} {S : Set V} {u w y : V}
    (hw : w ∈ compMinus H S u) (hwy : H.Adj w y) (hy : y ∉ S) : y ∈ compMinus H S u := by
  obtain ⟨hu, hw', hr⟩ := hw
  exact ⟨hu, hy, hr.trans (SimpleGraph.Adj.reachable
    (show (H.induce {x | x ∉ S}).Adj ⟨w, hw'⟩ ⟨y, hy⟩ from hwy))⟩

/-- Copied from `Cereceda.ColourDense.three_lt_ncard` (Cereceda/Intro/ColourDense.lean): four distinct elements of
a set give it more than three elements. -/
theorem three_lt_ncard {α : Type} [Finite α] {s : Set α} {a b c d : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hd : d ∈ s) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    3 < s.ncard := by
  have h4 : ({a, b, c, d} : Set α).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]), Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
      Set.ncard_pair hcd]
  have hsub : ({a, b, c, d} : Set α) ⊆ s := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have := Set.ncard_le_ncard hsub
  omega

/-- Every neighbour of a vertex of `D` lies in `D ∪ S`. -/
theorem nbr_mem_union {V : Type} {H : SimpleGraph V} {S : Set V} {u w y : V}
    (hw : w ∈ compMinus H S u) (hwy : H.Adj w y) : y ∈ compMinus H S u ∪ S := by
  by_cases hy : y ∈ S
  · exact Set.mem_union_right _ hy
  · exact Set.mem_union_left _ (mem_compMinus_of_adj hw hwy hy)

/-! ### The case `|D| = 1`: a 4-cycle -/

/-- If `D = {u}`, then `N(u) ⊆ S ⊆ N(v)`, and two neighbours of `u` with `u ≠ v` give a 4-cycle. -/
theorem case_single {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ x, 2 ≤ G.degree x) {S : Set V} {u v : V} (hu : u ∉ S) (hvD : v ∉ compMinus G S u)
    (hS : S ⊆ G.neighborSet v) (hsingle : ∀ w ∈ compMinus G S u, w = u) : G.egirth ≤ 4 := by
  have hNS : ∀ y, G.Adj u y → G.Adj v y := by
    intro y hy
    have hyS : y ∈ S := by
      by_contra hyS
      exact hy.ne (hsingle y (mem_compMinus_of_adj (self_mem_compMinus hu) hy hyS)).symm
    exact (mem_neighborSet _ _ _).1 (hS hyS)
  have huv : u ≠ v := fun h => hvD (h ▸ self_mem_compMinus hu)
  obtain ⟨a, b, ha, hb, hab⟩ := two_nbrs (hdeg u)
  exact egirth_le_four ha (hNS a ha).symm (hNS b hb) hb.symm huv hab

/-! ### The case `|D| ≥ 2`, `|D ∪ S| ≤ 3`: then `|S| ≤ 1` -/

/-- `S` has at most one element. -/
theorem S_subsingleton {V : Type} [Finite V] {G : SimpleGraph V} {S : Set V} {u w : V} (hu : u ∉ S)
    (hw : w ∈ compMinus G S u) (hwu : w ≠ u) (h3 : (compMinus G S u ∪ S).ncard ≤ 3) :
    ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ = s₂ := by
  intro s₁ h₁ s₂ h₂
  by_contra h₁₂
  have hwS : w ∉ S := not_mem_of_mem_compMinus hw
  have hne : ∀ {x y : V}, x ∉ S → y ∈ S → x ≠ y := fun hx hy h => hx (h ▸ hy)
  have := three_lt_ncard (s := compMinus G S u ∪ S) (Set.mem_union_left _ (self_mem_compMinus hu))
    (Set.mem_union_left _ hw) (Set.mem_union_right _ h₁) (Set.mem_union_right _ h₂) hwu.symm (hne hu h₁)
    (hne hu h₂) (hne hwS h₁) (hne hwS h₂) h₁₂
  omega

/-- `G − ∅` has exactly as many components as `G`, so the empty set is not a separator. -/
theorem not_isSeparator_empty {V : Type} (G : SimpleGraph V) : ¬ IsSeparator G ∅ := by
  intro h
  unfold IsSeparator at h
  have hset : {x : V | x ∉ (∅ : Set V)} = Set.univ := by
    ext x
    simp
  rw [hset, Nat.card_congr (induceUnivIso G).connectedComponentEquiv] at h
  exact lt_irrefl _ h

/-- `S = {s}`: then `D ∪ S = {u, w, s}`, both `u` and `w` have all their neighbours in it, so `u ~ w`, `u ~ s` and
`w ~ s`: a triangle. -/
theorem case_pair {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hdeg : ∀ x, 2 ≤ G.degree x) {u w s : V} (hu : u ∉ ({s} : Set V)) (hw : w ∈ compMinus G {s} u)
    (hwu : w ≠ u) (h3 : (compMinus G {s} u ∪ {s}).ncard ≤ 3) : G.egirth ≤ 3 := by
  have hwS : w ∉ ({s} : Set V) := not_mem_of_mem_compMinus hw
  have hus : u ≠ s := fun h => hu (h ▸ rfl)
  have hws : w ≠ s := fun h => hwS (h ▸ rfl)
  have hD : u ∈ compMinus G {s} u := self_mem_compMinus hu
  -- every element of `D ∪ S` is `u`, `w` or `s`
  have hthree : ∀ x ∈ compMinus G {s} u ∪ {s}, x = u ∨ x = w ∨ x = s := by
    intro x hx
    by_contra hne
    simp only [not_or] at hne
    have := three_lt_ncard (s := compMinus G {s} u ∪ {s}) (Set.mem_union_left _ hD)
      (Set.mem_union_left _ hw) (Set.mem_union_right _ (Set.mem_singleton s)) hx hwu.symm hus
      (Ne.symm hne.1) hws (Ne.symm hne.2.1) (Ne.symm hne.2.2)
    omega
  have hNu : ∀ y, G.Adj u y → y = w ∨ y = s := by
    intro y hy
    rcases hthree y (nbr_mem_union hD hy) with h | h
    · exact absurd h.symm hy.ne
    · exact h
  have hNw : ∀ y, G.Adj w y → y = u ∨ y = s := by
    intro y hy
    rcases hthree y (nbr_mem_union hw hy) with h | h | h
    · exact Or.inl h
    · exact absurd h.symm hy.ne
    · exact Or.inr h
  obtain ⟨huw, hus'⟩ := adj_both (hdeg u) hNu
  obtain ⟨-, hws'⟩ := adj_both (hdeg w) hNw
  exact egirth_le_three huw hws' hus'.symm

end JNotDense

open JNotDense in
/-- Remark 4.8 (iii), v3.90 l. 728-733, the general step (any graph with minimum degree ≥ 2 and girth ≥ 6): "no
identification as in the definition of 3-colour-dense graphs applies to it [...] Indeed, let S, u, v and D be as in
that definition. If |D| = 1, then D = {u}, so N(u) ⊆ S ⊆ N(v), so u and v have at least two common neighbours, and
J_ℓ has a cycle of length 4. If |D| ≥ 2, then |D ∪ S| ≤ 3, so |S| ≤ 1. The empty set is not a separator of a connected
graph. If S = {z}, then D consists of two adjacent vertices, each of degree at least 2 with all its neighbours in D ∪ S; so
both are adjacent to z, and J_ℓ has a triangle. Both cases contradict girth 6." -/
theorem no_identification_of_girth {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, 2 ≤ G.degree x) (hgirth : 6 ≤ G.egirth) (S : Set V) (u v : V) :
    IsSeparator G S → u ∉ S → v ∉ S → v ∉ compMinus G S u → S ⊆ G.neighborSet v →
      ¬ ((compMinus G S u).ncard = 1 ∨ (compMinus G S u ∪ S).ncard ≤ 3) := by
  intro hsep hu _ hvD hS hD
  by_cases hsingle : ∀ w ∈ compMinus G S u, w = u
  · exact not_six_le_of_le_four hgirth (case_single hdeg hu hvD hS hsingle)
  · simp only [not_forall] at hsingle
    obtain ⟨w, hw, hwu⟩ := hsingle
    have h3 : (compMinus G S u ∪ S).ncard ≤ 3 := by
      rcases hD with h1 | h3
      · exfalso
        obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 h1
        have h1' : u ∈ compMinus G S u := self_mem_compMinus hu
        have h2' := hw
        rw [hx] at h1' h2'
        exact hwu ((Set.mem_singleton_iff.1 h2').trans (Set.mem_singleton_iff.1 h1').symm)
      · exact h3
    have hS1 := S_subsingleton hu hw hwu h3
    rcases Set.eq_empty_or_nonempty S with hS0 | ⟨s, hs⟩
    · subst hS0
      exact not_isSeparator_empty G hsep
    · have hSs : S = {s} := by
        ext x
        exact ⟨fun hx => hS1 x hx s hs, fun hx => (Set.mem_singleton_iff.1 hx) ▸ hs⟩
      subst hSs
      exact not_six_le_of_le_four hgirth ((case_pair hdeg hu hw hwu h3).trans (by norm_num))

open JNotDense in
/-- Remark 4.8 (iii), v3.90 l. 727-729, for any nonempty graph with minimum degree ≥ 2 and girth ≥ 6: "It is not a
disjoint union of cliques, and no identification as in the definition of 3-colour-dense graphs applies to it; so it
is not 3-colour-dense." -/
theorem not_colourDense_of_girth {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, 2 ≤ G.degree x) (hgirth : 6 ≤ G.egirth) : ¬ IsColourDense 3 G := by
  intro h
  cases h with
  | base _ _ hq =>
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨a, b, ha, hb, hab⟩ := two_nbrs (hdeg x)
    have hab' : G.Adj a b := hq.1 a x b ha.symm hb hab
    exact not_six_le_of_le_four hgirth ((egirth_le_three ha hab' hb.symm).trans (by norm_num))
  | step _ S u v _ hsep hu hv hvD hS hD _ =>
    exact no_identification_of_girth G hdeg hgirth S u v hsep hu hv hvD hS hD

namespace JNotDense

/-! ### The graph `J_n` -/

open SimpleGraph

theorem J_adj_inl_inl {n : ℕ} (i j : Fin n) :
    (Jgraph n).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := Iff.rfl

theorem J_adj_inl_inr {n : ℕ} (i : Fin n) (j : Fin 4) :
    (Jgraph n).Adj (.inl i) (.inr j) ↔ (i.val + 1) % 4 = j.val := Fin.ext_iff

theorem J_adj_inr_inl {n : ℕ} (j : Fin 4) (i : Fin n) :
    (Jgraph n).Adj (.inr j) (.inl i) ↔ (i.val + 1) % 4 = j.val := Fin.ext_iff

/-- Each `v_i` has a neighbour on the path and a neighbour `a_j`. -/
theorem J_path_nbrs (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    (∃ i' : Fin n, (Jgraph n).Adj (.inl i) (.inl i')) ∧ ∃ j : Fin 4, (Jgraph n).Adj (.inl i) (.inr j) := by
  refine ⟨?_, ⟨⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩, (J_adj_inl_inr _ _).2 rfl⟩⟩
  by_cases hi : i.val + 1 < n
  · exact ⟨⟨i.val + 1, hi⟩, (J_adj_inl_inl _ _).2 (Or.inl rfl)⟩
  · exact ⟨⟨i.val - 1, by omega⟩, (J_adj_inl_inl _ _).2 (Or.inr (by simp only; omega))⟩

/-- Each `a_j` has two neighbours on the path: `v_i` with `i - 1 = (j + 3) mod 4` and `i - 1 = (j + 3) mod 4 + 4`. -/
theorem J_apex_nbrs (n : ℕ) (hn : 8 ≤ n) (j : Fin 4) :
    ∃ i i' : Fin n, i ≠ i' ∧ (Jgraph n).Adj (.inr j) (.inl i) ∧ (Jgraph n).Adj (.inr j) (.inl i') := by
  have hj := j.isLt
  refine ⟨⟨(j.val + 3) % 4, by omega⟩, ⟨(j.val + 3) % 4 + 4, by omega⟩, ?_, ?_, ?_⟩
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  · rw [J_adj_inr_inl]
    simp only
    omega
  · rw [J_adj_inr_inl]
    simp only
    omega

theorem J_min_degree (n : ℕ) (hn : 8 ≤ n) : ∀ x, 2 ≤ (Jgraph n).degree x := by
  intro x
  rcases x with i | j
  · obtain ⟨⟨i', hi'⟩, ⟨j, hj⟩⟩ := J_path_nbrs n (by omega) i
    exact two_le_degree hi' hj Sum.inl_ne_inr
  · obtain ⟨i, i', hii, hi, hi'⟩ := J_apex_nbrs n hn j
    exact two_le_degree hi hi' (fun h => hii (Sum.inl_injective h))

/-- Every path vertex is reachable from `v_1` along the path. -/
theorem J_reach_inl (n : ℕ) (h0 : 0 < n) : ∀ k (hk : k < n),
    (Jgraph n).Reachable (.inl ⟨0, h0⟩) (.inl ⟨k, hk⟩) := by
  intro k
  induction k with
  | zero => intro _; exact Reachable.refl _
  | succ k ih =>
    intro hk
    exact (ih (by omega)).trans (Adj.reachable ((J_adj_inl_inl _ _).2 (Or.inl rfl)))

theorem J_connected (n : ℕ) (hn : 8 ≤ n) : (Jgraph n).Connected := by
  have h0 : 0 < n := by omega
  rw [connected_iff_exists_forall_reachable]
  refine ⟨.inl ⟨0, h0⟩, ?_⟩
  rintro (i | j)
  · exact J_reach_inl n h0 i.val i.isLt
  · obtain ⟨⟨i, hi⟩, -, -, hadj, -⟩ := J_apex_nbrs n hn j
    exact (J_reach_inl n h0 i hi).trans (Adj.reachable hadj.symm)

/-- `v_1 ~ v_2 ~ v_3` but `v_1 ≁ v_3`: adjacency is not transitive. -/
theorem J_not_transitive (n : ℕ) (hn : 3 ≤ n) :
    ¬ (∀ x y z, (Jgraph n).Adj x y → (Jgraph n).Adj y z → x ≠ z → (Jgraph n).Adj x z) := by
  intro h
  have h01 : (Jgraph n).Adj (.inl ⟨0, by omega⟩) (.inl ⟨1, by omega⟩) := (J_adj_inl_inl _ _).2 (Or.inl rfl)
  have h12 : (Jgraph n).Adj (.inl ⟨1, by omega⟩) (.inl ⟨2, by omega⟩) := (J_adj_inl_inl _ _).2 (Or.inl rfl)
  have hne : (Sum.inl ⟨0, by omega⟩ : Fin n ⊕ Fin 4) ≠ .inl ⟨2, by omega⟩ := by simp
  have h02 := h _ _ _ h01 h12 hne
  rw [J_adj_inl_inl] at h02
  simp at h02

end JNotDense

open JNotDense in
/-- Remark 4.8 (iii), v3.90 l. 726-733: "J_ℓ is connected, has more than three vertices and girth 6, and has minimum
degree at least 2: each v_i has a neighbour on the path and a neighbour a_j, and each a_j has at least two neighbours
on the path. It is not a disjoint union of cliques, and no identification as in the definition of 3-colour-dense
graphs applies to it; so it is not 3-colour-dense." -/
theorem rem_4_8_iii_proved (n : ℕ) (hn : 15 ≤ n) :
    (Jgraph n).Connected ∧ 3 < Fintype.card (Fin n ⊕ Fin 4) ∧ (Jgraph n).egirth = 6 ∧
      (∀ i : Fin n, (∃ i' : Fin n, (Jgraph n).Adj (.inl i) (.inl i')) ∧ ∃ j : Fin 4, (Jgraph n).Adj (.inl i) (.inr j)) ∧
      (∀ j : Fin 4, ∃ i i' : Fin n, i ≠ i' ∧ (Jgraph n).Adj (.inr j) (.inl i) ∧ (Jgraph n).Adj (.inr j) (.inl i')) ∧
      (∀ x, 2 ≤ (Jgraph n).degree x) ∧
      ¬ (∀ x y z, (Jgraph n).Adj x y → (Jgraph n).Adj y z → x ≠ z → (Jgraph n).Adj x z) ∧
      (∀ (S : Set (Fin n ⊕ Fin 4)) (u v : Fin n ⊕ Fin 4), IsSeparator (Jgraph n) S → u ∉ S → v ∉ S →
        v ∉ compMinus (Jgraph n) S u → S ⊆ (Jgraph n).neighborSet v →
        ¬ ((compMinus (Jgraph n) S u).ncard = 1 ∨ (compMinus (Jgraph n) S u ∪ S).ncard ≤ 3)) ∧
      ¬ IsColourDense 3 (Jgraph n) := by
  have hgirth : (Jgraph n).egirth = 6 := GirthAux.Jgraph_egirth_proved n (by omega)
  have hdeg := J_min_degree n (by omega)
  have h6 : 6 ≤ (Jgraph n).egirth := hgirth.ge
  have : Nonempty (Fin n ⊕ Fin 4) := ⟨.inr 0⟩
  refine ⟨J_connected n (by omega), ?_, hgirth, J_path_nbrs n (by omega), J_apex_nbrs n (by omega), hdeg,
    J_not_transitive n (by omega), no_identification_of_girth (Jgraph n) hdeg h6,
    not_colourDense_of_girth (Jgraph n) hdeg h6⟩
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end Cereceda
