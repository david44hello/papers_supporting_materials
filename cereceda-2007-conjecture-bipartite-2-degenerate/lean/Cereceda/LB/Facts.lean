/-
Facts.lean — basic facts about the graphs H_n and J_n (paper Section 4): vertex and edge counts, the two sides,
orders with at most two later neighbours, not 1-degenerate; and three general graph facts.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

PROOF ROUTE: everything about `H_n` and `J_n` is proved once for the general `pathApex n k f`. Edges: an explicit
injective list `edgeOf` of the `n - 1` path edges and the `n` apex edges, whose image is the edge set. Orders: a
path vertex has its later neighbours among `{next path vertex, its apex}`; an apex has none. Not 1-degenerate: a
cycle (4-cycle in `H_n`, 6-cycle in `J_n`) in which every vertex has two neighbours.
-/
import Cereceda.Defs.LowerBound

namespace Cereceda.FactsAux

open Cereceda Finset SimpleGraph

/-! ### Adjacency in `pathApex`, unfolded -/

lemma adj_inl_inl {n k : ℕ} (f : Fin n → Fin k) (i j : Fin n) :
    (pathApex n k f).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := Iff.rfl

lemma adj_inl_inr {n k : ℕ} (f : Fin n → Fin k) (i : Fin n) (j : Fin k) :
    (pathApex n k f).Adj (.inl i) (.inr j) ↔ f i = j := Iff.rfl

lemma adj_inr_inl {n k : ℕ} (f : Fin n → Fin k) (j : Fin k) (i : Fin n) :
    (pathApex n k f).Adj (.inr j) (.inl i) ↔ f i = j := Iff.rfl

lemma adj_inr_inr {n k : ℕ} (f : Fin n → Fin k) (j j' : Fin k) :
    (pathApex n k f).Adj (.inr j) (.inr j') ↔ False := Iff.rfl

/-! ### Vertex counts -/

theorem Hgraph_card (n : ℕ) : Fintype.card (Fin n ⊕ Fin 2) = n + 2 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

theorem Jgraph_card (n : ℕ) : Fintype.card (Fin n ⊕ Fin 4) = n + 4 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-! ### Edge count: `n - 1` path edges and `n` apex edges -/

/-- The edges of `pathApex n k f`, listed: the path edges `v_{i+1} v_{i+2}` (`i < n - 1`) and the apex edges
`v_{i+1} f(i)` (`i < n`). -/
def edgeOf (n k : ℕ) (f : Fin n → Fin k) : Fin (n - 1) ⊕ Fin n → Sym2 (Fin n ⊕ Fin k)
  | .inl i => s(.inl ⟨i.val, by have := i.isLt; omega⟩, .inl ⟨i.val + 1, by have := i.isLt; omega⟩)
  | .inr i => s(.inl i, .inr (f i))

lemma edgeOf_injective (n k : ℕ) (f : Fin n → Fin k) : Function.Injective (edgeOf n k f) := by
  rintro (i | i) (j | j) h <;>
    simp only [edgeOf, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff, reduceCtorEq, and_false,
      false_and, or_false] at h ⊢ <;>
    omega

lemma edgeOf_mem_edgeFinset (n k : ℕ) (f : Fin n → Fin k) (x : Fin (n - 1) ⊕ Fin n) :
    edgeOf n k f x ∈ (pathApex n k f).edgeFinset := by
  rcases x with i | i
  · rw [edgeOf, mem_edgeFinset, mem_edgeSet, adj_inl_inl]
    exact Or.inl rfl
  · rw [edgeOf, mem_edgeFinset, mem_edgeSet, adj_inl_inr]

lemma exists_edgeOf_of_adj {n k : ℕ} (f : Fin n → Fin k) {u v : Fin n ⊕ Fin k}
    (h : (pathApex n k f).Adj u v) : ∃ x, edgeOf n k f x = s(u, v) := by
  rcases u with i | j <;> rcases v with i' | j'
  · rw [adj_inl_inl] at h
    have := i.isLt
    have := i'.isLt
    rcases h with h | h
    · exact ⟨.inl ⟨i.val, by omega⟩, by simp only [edgeOf, Sym2.eq_iff, Sum.inl.injEq, Fin.ext_iff, true_and]; omega⟩
    · exact ⟨.inl ⟨i'.val, by omega⟩, by simp only [edgeOf, Sym2.eq_iff, Sum.inl.injEq, Fin.ext_iff, true_and]; omega⟩
  · rw [adj_inl_inr] at h
    subst h
    exact ⟨.inr i, rfl⟩
  · rw [adj_inr_inl] at h
    subst h
    exact ⟨.inr i', Sym2.eq_swap⟩
  · exact h.elim

lemma edgeFinset_eq (n k : ℕ) (f : Fin n → Fin k) :
    (pathApex n k f).edgeFinset = univ.image (edgeOf n k f) := by
  ext e
  rw [mem_image]
  constructor
  · intro he
    induction e using Sym2.ind with
    | h u v =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      obtain ⟨x, hx⟩ := exists_edgeOf_of_adj f he
      exact ⟨x, mem_univ x, hx⟩
  · rintro ⟨x, -, rfl⟩
    exact edgeOf_mem_edgeFinset n k f x

lemma pathApex_edges (n k : ℕ) (f : Fin n → Fin k) : (pathApex n k f).edgeFinset.card = (n - 1) + n := by
  rw [edgeFinset_eq, card_image_of_injective _ (edgeOf_injective n k f), card_univ, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin]

theorem Hgraph_edges (n : ℕ) (hn : 2 ≤ n) : (Hgraph n).edgeFinset.card = 2 * n - 1 := by
  rw [pathApex_edges]
  omega

/-! ### The two sides are proper 2-colourings -/

theorem Hgraph_sides (n : ℕ) : IsProperFn (Hgraph n) (sideH n) := by
  rintro (i | j) (i' | j') h
  · rw [adj_inl_inl] at h
    simp only [sideH, ne_eq, Fin.ext_iff]
    omega
  · rw [adj_inl_inr] at h
    simp only [Fin.ext_iff] at h
    simp only [sideH, ne_eq, Fin.ext_iff]
    have := j'.isLt
    omega
  · rw [adj_inr_inl] at h
    simp only [Fin.ext_iff] at h
    simp only [sideH, ne_eq, Fin.ext_iff]
    have := j.isLt
    omega
  · exact h.elim

theorem Jgraph_sides (n : ℕ) : IsProperFn (Jgraph n) (sideJ n) := by
  rintro (i | j) (i' | j') h
  · rw [adj_inl_inl] at h
    simp only [sideJ, ne_eq, Fin.ext_iff]
    omega
  · rw [adj_inl_inr] at h
    simp only [Fin.ext_iff] at h
    simp only [sideJ, ne_eq, Fin.ext_iff]
    omega
  · rw [adj_inr_inl] at h
    simp only [Fin.ext_iff] at h
    simp only [sideJ, ne_eq, Fin.ext_iff]
    omega
  · exact h.elim

/-! ### Orders: path first, then the apices; at most two later neighbours -/

lemma rho_inl {n k : ℕ} (i : Fin n) :
    ((finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n + k)) (.inl i)).val = i.val := by
  rw [finSumFinEquiv_apply_left, Fin.val_castAdd]

lemma rho_inr {n k : ℕ} (j : Fin k) :
    ((finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n + k)) (.inr j)).val = n + j.val := by
  rw [finSumFinEquiv_apply_right, Fin.val_natAdd]

/-- An apex has no later neighbour: all its neighbours are path vertices, which come first. -/
lemma laterNbrs_inr {n k : ℕ} (f : Fin n → Fin k) (j : Fin k) :
    laterNbrs (pathApex n k f) finSumFinEquiv (.inr j) = ∅ := by
  rw [laterNbrs, filter_eq_empty_iff]
  rintro (i | i) - ⟨hadj, hlt⟩
  · rw [Fin.lt_def, rho_inl, rho_inr] at hlt
    have := i.isLt
    omega
  · exact hadj

/-- A path vertex `v_{i+1}` has its later neighbours among the next path vertex (if any) and its apex. -/
lemma laterNbrs_inl_subset {n k : ℕ} (f : Fin n → Fin k) (i : Fin n) :
    laterNbrs (pathApex n k f) finSumFinEquiv (.inl i) ⊆
      {.inl ⟨min (i.val + 1) (n - 1), by have := i.isLt; omega⟩, .inr (f i)} := by
  intro u hu
  rw [laterNbrs, mem_filter] at hu
  obtain ⟨-, hadj, hlt⟩ := hu
  rw [mem_insert, mem_singleton]
  rcases u with i' | j
  · left
    rw [adj_inl_inl] at hadj
    rw [Fin.lt_def, rho_inl, rho_inl] at hlt
    rw [Sum.inl.injEq, Fin.ext_iff]
    show i'.val = min (i.val + 1) (n - 1)
    have := i'.isLt
    omega
  · right
    rw [adj_inl_inr] at hadj
    rw [hadj]

lemma pathApex_order (n k : ℕ) (f : Fin n → Fin k) :
    IsDegOrder (pathApex n k f) 2 (finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n + k)) := by
  rintro (i | j)
  · exact (card_le_card (laterNbrs_inl_subset f i)).trans card_le_two
  · rw [laterNbrs_inr, card_empty]
    omega

theorem Hgraph_order (n : ℕ) : IsDegOrder (Hgraph n) 2 (finSumFinEquiv : Fin n ⊕ Fin 2 ≃ Fin (n + 2)) :=
  pathApex_order n 2 _

theorem Jgraph_order (n : ℕ) : IsDegOrder (Jgraph n) 2 (finSumFinEquiv : Fin n ⊕ Fin 4 ≃ Fin (n + 4)) :=
  pathApex_order n 4 _

/-! ### Not 1-degenerate: a cycle in which every vertex has two neighbours -/

lemma not_one_degenerate_of {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (hs : s.Nonempty) (h : ∀ v ∈ s, 2 ≤ (s.filter (G.Adj v)).card) : ¬ IsDegenerate G 1 := by
  intro hdeg
  obtain ⟨v, hv, hcard⟩ := hdeg s hs
  have := h v hv
  omega

lemma two_le_card_filter_adj {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {s : Finset V} {v x y : V} (hxy : x ≠ y) (hx : x ∈ s) (hy : y ∈ s) (hvx : G.Adj v x) (hvy : G.Adj v y) :
    2 ≤ (s.filter (G.Adj v)).card := by
  rw [← card_pair hxy]
  apply card_le_card
  intro u hu
  rw [mem_insert, mem_singleton] at hu
  rw [mem_filter]
  rcases hu with rfl | rfl
  · exact ⟨hx, hvx⟩
  · exact ⟨hy, hvy⟩

/-- `H_n`, `n ≥ 3`: the 4-cycle `a v_1 v_2 v_3` (`inr 0, inl 0, inl 1, inl 2`). -/
theorem Hgraph_not_one_degenerate (n : ℕ) (hn : 3 ≤ n) : ¬ IsDegenerate (Hgraph n) 1 := by
  let p : ℕ → Fin n ⊕ Fin 2 := fun i => .inl ⟨i % 3, by omega⟩
  have hp : ∀ i j, i < 3 → j < 3 → (p i = p j ↔ i = j) := by
    intro i j hi hj
    simp only [p, Sum.inl.injEq, Fin.ext_iff]
    omega
  have hpa : ∀ i, p i ≠ .inr 0 := fun i => Sum.inl_ne_inr
  have hpp : ∀ i j, i < 3 → j < 3 → ((Hgraph n).Adj (p i) (p j) ↔ i + 1 = j ∨ j + 1 = i) := by
    intro i j hi hj
    simp only [p, adj_inl_inl]
    omega
  have hpA : ∀ i, i < 3 → ((Hgraph n).Adj (p i) (.inr 0) ↔ i % 2 = 0) := by
    intro i hi
    simp only [p, adj_inl_inr, Fin.ext_iff, Fin.val_zero]
    omega
  apply not_one_degenerate_of _ {p 0, p 1, p 2, .inr 0} (insert_nonempty _ _)
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact two_le_card_filter_adj _ (x := p 1) (y := .inr 0) (hpa 1) (by simp) (by simp)
      ((hpp 0 1 (by omega) (by omega)).mpr (by omega)) ((hpA 0 (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 0) (y := p 2) (by rw [Ne, hp 0 2 (by omega) (by omega)]; omega)
      (by simp) (by simp) ((hpp 1 0 (by omega) (by omega)).mpr (by omega))
      ((hpp 1 2 (by omega) (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 1) (y := .inr 0) (hpa 1) (by simp) (by simp)
      ((hpp 2 1 (by omega) (by omega)).mpr (by omega)) ((hpA 2 (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 0) (y := p 2) (by rw [Ne, hp 0 2 (by omega) (by omega)]; omega)
      (by simp) (by simp) ((adj_symm _ ((hpA 0 (by omega)).mpr (by omega))))
      ((adj_symm _ ((hpA 2 (by omega)).mpr (by omega))))

/-- `J_n`, `n ≥ 5`: the 6-cycle `a_1 v_1 v_2 v_3 v_4 v_5` (`inr 1, inl 0, …, inl 4`). -/
theorem Jgraph_not_one_degenerate (n : ℕ) (hn : 5 ≤ n) : ¬ IsDegenerate (Jgraph n) 1 := by
  let p : ℕ → Fin n ⊕ Fin 4 := fun i => .inl ⟨i % 5, by omega⟩
  have hp : ∀ i j, i < 5 → j < 5 → (p i = p j ↔ i = j) := by
    intro i j hi hj
    simp only [p, Sum.inl.injEq, Fin.ext_iff]
    omega
  have hpa : ∀ i, p i ≠ .inr 1 := fun i => Sum.inl_ne_inr
  have hpp : ∀ i j, i < 5 → j < 5 → ((Jgraph n).Adj (p i) (p j) ↔ i + 1 = j ∨ j + 1 = i) := by
    intro i j hi hj
    simp only [p, adj_inl_inl]
    omega
  have hpA : ∀ i, i < 5 → ((Jgraph n).Adj (p i) (.inr 1) ↔ (i + 1) % 4 = 1) := by
    intro i hi
    simp only [p, adj_inl_inr, Fin.ext_iff, Fin.val_one]
    rw [Nat.mod_eq_of_lt hi]
  have hne : ∀ i j, i < 5 → j < 5 → i ≠ j → p i ≠ p j := fun i j hi hj hij h => hij ((hp i j hi hj).mp h)
  apply not_one_degenerate_of _ {.inr 1, p 0, p 1, p 2, p 3, p 4} (insert_nonempty _ _)
  intro v hv
  simp only [mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · exact two_le_card_filter_adj _ (x := p 0) (y := p 4) (hne 0 4 (by omega) (by omega) (by omega))
      (by simp) (by simp) (adj_symm _ ((hpA 0 (by omega)).mpr (by omega)))
      (adj_symm _ ((hpA 4 (by omega)).mpr (by omega)))
  · exact two_le_card_filter_adj _ (x := p 1) (y := .inr 1) (hpa 1) (by simp) (by simp)
      ((hpp 0 1 (by omega) (by omega)).mpr (by omega)) ((hpA 0 (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 0) (y := p 2) (hne 0 2 (by omega) (by omega) (by omega))
      (by simp) (by simp) ((hpp 1 0 (by omega) (by omega)).mpr (by omega))
      ((hpp 1 2 (by omega) (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 1) (y := p 3) (hne 1 3 (by omega) (by omega) (by omega))
      (by simp) (by simp) ((hpp 2 1 (by omega) (by omega)).mpr (by omega))
      ((hpp 2 3 (by omega) (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 2) (y := p 4) (hne 2 4 (by omega) (by omega) (by omega))
      (by simp) (by simp) ((hpp 3 2 (by omega) (by omega)).mpr (by omega))
      ((hpp 3 4 (by omega) (by omega)).mpr (by omega))
  · exact two_le_card_filter_adj _ (x := p 3) (y := .inr 1) (hpa 3) (by simp) (by simp)
      ((hpp 4 3 (by omega) (by omega)).mpr (by omega)) ((hpA 4 (by omega)).mpr (by omega))

/-! ### General graph facts -/

/-- An order with at most `d` later neighbours gives `d`-degeneracy: in a nonempty set take the first vertex in
the order; all its neighbours in the set come later. -/
theorem degenerate_of_order {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) {m : ℕ} (ρ : V ≃ Fin m) (h : IsDegOrder G d ρ) : IsDegenerate G d := by
  intro s hs
  obtain ⟨v, hv, hmin⟩ := s.exists_min_image ρ hs
  refine ⟨v, hv, le_trans (card_le_card ?_) (h v)⟩
  intro u hu
  rw [mem_filter] at hu
  rw [laterNbrs, mem_filter]
  refine ⟨mem_univ u, hu.2, lt_of_le_of_ne (hmin u hu.1) ?_⟩
  intro heq
  exact G.ne_of_adj hu.2 (ρ.injective heq)

/-- A proper function to `Fin 2` is a 2-colouring. -/
theorem bipartite_of_sides {V : Type} (G : SimpleGraph V) (s : V → Fin 2) (h : IsProperFn G s) :
    G.IsBipartite :=
  ⟨Coloring.mk s fun hvw => h _ _ hvw⟩

/-- A triangle would need three different colours among two. -/
theorem cliqueFree_three_of_bipartite {V : Type} (G : SimpleGraph V) (h : G.IsBipartite) : G.CliqueFree 3 :=
  Colorable.cliqueFree h (by norm_num)

end Cereceda.FactsAux
