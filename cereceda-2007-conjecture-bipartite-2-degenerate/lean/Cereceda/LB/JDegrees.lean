/-
Cereceda/LB/JDegrees.lean — J_ℓ: a_1 has degree at least 4, Grundy number at least 4, mad > 3 (short v3.90 l. 721-725).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.LB.Facts
import Cereceda.Defs.Intro
import Cereceda.Setting.Misc

namespace Cereceda

open Finset

namespace JDegrees

/-- The path indices used below exist when `15 ≤ n` (a context-free proof, so that no hypothesis leaks into it). -/
theorem lt_n {n : ℕ} (hn : 15 ≤ n) (i : ℕ) (hi : i < 15 := by norm_num) : i < n := lt_of_lt_of_le hi hn

/-! ### First-fit: the colour of a vertex from the colours of its earlier neighbours -/

/-- In a first-fit colouring, a vertex gets the least colour `k` missing from the set `T` of colours of its earlier
neighbours (given as: every earlier neighbour has a colour in `T`, and every colour in `T` is on one). -/
theorem greedy_eq {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℕ}
    {ρ : V ≃ Fin m} {c : V → ℕ} (hc : IsGreedyRel G ρ c) (v : V) (T : Finset ℕ)
    (hT : ∀ u, G.Adj v u → ρ u < ρ v → c u ∈ T) (hT' : ∀ y ∈ T, ∃ u, G.Adj v u ∧ ρ u < ρ v ∧ c u = y)
    (k : ℕ) (hk : k ∉ T) (hlt : ∀ y < k, y ∈ T) : c v = k := by
  obtain ⟨h1, h2⟩ := hc v
  rcases lt_trichotomy (c v) k with h | h | h
  · obtain ⟨u, hadj, hρ, hu⟩ := hT' _ (hlt _ h)
    exact absurd (mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ u, hadj, hρ⟩, hu⟩) h1
  · exact h
  · obtain ⟨u, hu, hcu⟩ := mem_image.mp (h2 k h)
    obtain ⟨-, hadj, hρ⟩ := mem_filter.mp hu
    exact absurd (hcu ▸ hT u hadj hρ) hk

/-! ### The eight vertices `v_1, v_4, v_5, v_10, v_7, v_8, v_9, a_1` at the start of an order -/

/-- If `v_1, v_4, v_5, v_10, v_7, v_8, v_9, a_1` are at the places `0, …, 7` of the order, every vertex at a place
below `8` is one of them. -/
theorem early {n m : ℕ} (hn : 15 ≤ n) (ρ : Fin n ⊕ Fin 4 ≃ Fin m)
    (h0 : (ρ (.inl ⟨0, lt_n hn 0⟩)).val = 0) (h1 : (ρ (.inl ⟨3, lt_n hn 3⟩)).val = 1)
    (h2 : (ρ (.inl ⟨4, lt_n hn 4⟩)).val = 2) (h3 : (ρ (.inl ⟨9, lt_n hn 9⟩)).val = 3)
    (h4 : (ρ (.inl ⟨6, lt_n hn 6⟩)).val = 4) (h5 : (ρ (.inl ⟨7, lt_n hn 7⟩)).val = 5)
    (h6 : (ρ (.inl ⟨8, lt_n hn 8⟩)).val = 6) (h7 : (ρ (.inr 1)).val = 7)
    (u : Fin n ⊕ Fin 4) (hu : (ρ u).val < 8) :
    u = .inl ⟨0, lt_n hn 0⟩ ∨ u = .inl ⟨3, lt_n hn 3⟩ ∨ u = .inl ⟨4, lt_n hn 4⟩ ∨ u = .inl ⟨9, lt_n hn 9⟩ ∨
      u = .inl ⟨6, lt_n hn 6⟩ ∨ u = .inl ⟨7, lt_n hn 7⟩ ∨ u = .inl ⟨8, lt_n hn 8⟩ ∨ u = .inr 1 := by
  have key : ∀ w, (ρ w).val = (ρ u).val → u = w := fun w hw => ρ.injective (Fin.ext hw.symm)
  rcases (show (ρ u).val = 0 ∨ (ρ u).val = 1 ∨ (ρ u).val = 2 ∨ (ρ u).val = 3 ∨ (ρ u).val = 4 ∨
      (ρ u).val = 5 ∨ (ρ u).val = 6 ∨ (ρ u).val = 7 by omega) with h | h | h | h | h | h | h | h
  · exact Or.inl (key _ (h0.trans h.symm))
  · exact Or.inr (Or.inl (key _ (h1.trans h.symm)))
  · exact Or.inr (Or.inr (Or.inl (key _ (h2.trans h.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (key _ (h3.trans h.symm)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ (h4.trans h.symm))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ (h5.trans h.symm)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key _ (h6.trans h.symm))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key _ (h7.trans h.symm))))))))

/-- First-fit in an order that begins with `v_1, v_4, v_5, v_10, v_7, v_8, v_9, a_1` gives these vertices the
colours `0, 0, 1, 0, 0, 1, 2, 3` (Lean's colours start at `0`). -/
theorem colours {n m : ℕ} (hn : 15 ≤ n) (ρ : Fin n ⊕ Fin 4 ≃ Fin m) (c : Fin n ⊕ Fin 4 → ℕ)
    (hc : IsGreedyRel (Jgraph n) ρ c)
    (h0 : (ρ (.inl ⟨0, lt_n hn 0⟩)).val = 0) (h1 : (ρ (.inl ⟨3, lt_n hn 3⟩)).val = 1)
    (h2 : (ρ (.inl ⟨4, lt_n hn 4⟩)).val = 2) (h3 : (ρ (.inl ⟨9, lt_n hn 9⟩)).val = 3)
    (h4 : (ρ (.inl ⟨6, lt_n hn 6⟩)).val = 4) (h5 : (ρ (.inl ⟨7, lt_n hn 7⟩)).val = 5)
    (h6 : (ρ (.inl ⟨8, lt_n hn 8⟩)).val = 6) (h7 : (ρ (.inr 1)).val = 7) :
    c (.inl ⟨0, lt_n hn 0⟩) = 0 ∧ c (.inl ⟨3, lt_n hn 3⟩) = 0 ∧ c (.inl ⟨4, lt_n hn 4⟩) = 1 ∧
      c (.inl ⟨9, lt_n hn 9⟩) = 0 ∧ c (.inl ⟨6, lt_n hn 6⟩) = 0 ∧ c (.inl ⟨7, lt_n hn 7⟩) = 1 ∧
      c (.inl ⟨8, lt_n hn 8⟩) = 2 ∧ c (.inr 1) = 3 := by
  have E := early hn ρ h0 h1 h2 h3 h4 h5 h6 h7
  -- every earlier neighbour of the vertex at place `k ≤ 7` is one of the eight; sort the cases
  have c0 : c (.inl ⟨0, lt_n hn 0⟩) = 0 := by
    refine greedy_eq hc _ ∅ (fun u _ hlt => ?_) (by simp) 0 (by simp) (by simp)
    rw [Fin.lt_def, h0] at hlt
    omega
  have c1 : c (.inl ⟨3, lt_n hn 3⟩) = 0 := by
    refine greedy_eq hc _ ∅ (fun u hadj hlt => ?_) (by simp) 0 (by simp) (by simp)
    rw [Fin.lt_def, h1] at hlt
    rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [FactsAux.adj_inl_inl, FactsAux.adj_inl_inr]
  have c2 : c (.inl ⟨4, lt_n hn 4⟩) = 1 := by
    refine greedy_eq hc _ {0} (fun u hadj hlt => ?_) ?_ 1 (by simp) (by simp)
    · rw [Fin.lt_def, h2] at hlt
      rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [FactsAux.adj_inl_inl, FactsAux.adj_inl_inr]
    · intro y hy
      rw [mem_singleton] at hy
      exact ⟨.inl ⟨3, lt_n hn 3⟩, by simp [FactsAux.adj_inl_inl], by rw [Fin.lt_def, h1, h2]; omega, c1.trans hy.symm⟩
  have c3 : c (.inl ⟨9, lt_n hn 9⟩) = 0 := by
    refine greedy_eq hc _ ∅ (fun u hadj hlt => ?_) (by simp) 0 (by simp) (by simp)
    rw [Fin.lt_def, h3] at hlt
    rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [FactsAux.adj_inl_inl, FactsAux.adj_inl_inr]
  have c4 : c (.inl ⟨6, lt_n hn 6⟩) = 0 := by
    refine greedy_eq hc _ ∅ (fun u hadj hlt => ?_) (by simp) 0 (by simp) (by simp)
    rw [Fin.lt_def, h4] at hlt
    rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [FactsAux.adj_inl_inl, FactsAux.adj_inl_inr]
  have c5 : c (.inl ⟨7, lt_n hn 7⟩) = 1 := by
    refine greedy_eq hc _ {0} (fun u hadj hlt => ?_) ?_ 1 (by simp) (by simp)
    · rw [Fin.lt_def, h5] at hlt
      rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [FactsAux.adj_inl_inl, FactsAux.adj_inl_inr]
    · intro y hy
      rw [mem_singleton] at hy
      exact ⟨.inl ⟨6, lt_n hn 6⟩, by simp [FactsAux.adj_inl_inl], by rw [Fin.lt_def, h4, h5]; omega,
        c4.trans hy.symm⟩
  have c6 : c (.inl ⟨8, lt_n hn 8⟩) = 2 := by
    refine greedy_eq hc _ {0, 1} (fun u hadj hlt => ?_) ?_ 2 (by simp) (fun y hy => by simp; omega)
    · rw [Fin.lt_def, h6] at hlt
      rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [FactsAux.adj_inl_inl, FactsAux.adj_inl_inr]
    · intro y hy
      rw [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨.inl ⟨9, lt_n hn 9⟩, by simp [FactsAux.adj_inl_inl], by rw [Fin.lt_def, h3, h6]; omega, c3⟩
      · exact ⟨.inl ⟨7, lt_n hn 7⟩, by simp [FactsAux.adj_inl_inl], by rw [Fin.lt_def, h5, h6]; omega, c5⟩
  have c7 : c (.inr 1) = 3 := by
    refine greedy_eq hc _ {0, 1, 2} (fun u hadj hlt => ?_) ?_ 3 (by simp) (fun y hy => by simp; omega)
    · rw [Fin.lt_def, h7] at hlt
      rcases E u (by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [FactsAux.adj_inr_inl, Fin.ext_iff]
    · intro y hy
      rw [mem_insert, mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨.inl ⟨0, lt_n hn 0⟩, by simp [FactsAux.adj_inr_inl], by rw [Fin.lt_def, h0, h7]; omega,
          c0⟩
      · exact ⟨.inl ⟨4, lt_n hn 4⟩, by simp [FactsAux.adj_inr_inl], by rw [Fin.lt_def, h2, h7]; omega,
          c2⟩
      · exact ⟨.inl ⟨8, lt_n hn 8⟩, by simp [FactsAux.adj_inr_inl], by rw [Fin.lt_def, h6, h7]; omega,
          c6⟩
  exact ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩

/-! ### An order that begins with `v_1, v_4, v_5, v_10, v_7, v_8, v_9, a_1` -/

/-- The place of the path vertex with 0-based index `i`: the indices `0, 3, 4, 9, 6, 7, 8` go to `0, …, 6`, the
indices `1, 2, 5` to `8, 9, 10`, and every index `i ≥ 10` to `i + 1`. -/
def pos (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 3 then 1 else if i = 4 then 2 else if i = 9 then 3 else if i = 6 then 4 else
  if i = 7 then 5 else if i = 8 then 6 else if i = 1 then 8 else if i = 2 then 9 else if i = 5 then 10 else i + 1

/-- The place of the apex `a_j`: `a_1` goes to `7`, `a_0` to `n + 1`, `a_2` and `a_3` to `n + 2` and `n + 3`. -/
def apos (n j : ℕ) : ℕ := if j = 1 then 7 else if j = 0 then n + 1 else n + j

theorem pos_lt {n : ℕ} (hn : 15 ≤ n) {i : ℕ} (hi : i < n) : pos i < n + 4 := by
  unfold pos
  split_ifs <;> omega

theorem apos_lt {n : ℕ} (hn : 15 ≤ n) {j : ℕ} (hj : j < 4) : apos n j < n + 4 := by
  unfold apos
  split_ifs <;> omega

/-- A left inverse of `pos`. -/
def unpos (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 3 else if k = 2 then 4 else if k = 3 then 9 else if k = 4 then 6 else
  if k = 5 then 7 else if k = 6 then 8 else if k = 8 then 1 else if k = 9 then 2 else if k = 10 then 5 else k - 1

theorem unpos_of_ge (k : ℕ) (hk : 11 ≤ k) : unpos k = k - 1 := by
  unfold unpos
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    ite_eq_right (by omega), ite_eq_right (by omega)]

theorem unpos_pos (i : ℕ) : unpos (pos i) = i := by
  unfold pos
  split_ifs with h0 h3 h4 h9 h6 h7 h8 h1 h2 h5
  · subst h0; rfl
  · subst h3; rfl
  · subst h4; rfl
  · subst h9; rfl
  · subst h6; rfl
  · subst h7; rfl
  · subst h8; rfl
  · subst h1; rfl
  · subst h2; rfl
  · subst h5; rfl
  · rw [unpos_of_ge _ (by omega)]
    omega

theorem pos_inj {a b : ℕ} (h : pos a = pos b) : a = b := by
  rw [← unpos_pos a, h, unpos_pos]

theorem apos_inj {n a b : ℕ} (hn : 15 ≤ n) (ha : a < 4) (hb : b < 4) (h : apos n a = apos n b) : a = b := by
  unfold apos at h
  split_ifs at h <;> omega

theorem pos_ne_apos {n a b : ℕ} (hn : 15 ≤ n) (ha : a < n) : pos a ≠ apos n b := by
  unfold pos apos
  split_ifs <;> omega

/-- The order as a function. -/
def ordFun (n : ℕ) (hn : 15 ≤ n) : Fin n ⊕ Fin 4 → Fin (n + 4)
  | .inl i => ⟨pos i.val, pos_lt hn i.isLt⟩
  | .inr j => ⟨apos n j.val, apos_lt hn j.isLt⟩

theorem ordFun_injective (n : ℕ) (hn : 15 ≤ n) : Function.Injective (ordFun n hn) := by
  rintro (i | j) (i' | j') h <;> simp only [ordFun, Fin.mk.injEq] at h
  · exact congrArg Sum.inl (Fin.ext (pos_inj h))
  · exact absurd h (pos_ne_apos hn i.isLt)
  · exact absurd h.symm (pos_ne_apos hn i'.isLt)
  · exact congrArg Sum.inr (Fin.ext (apos_inj hn j.isLt j'.isLt h))

/-- The order: a bijection from the vertices of `J_n` to the places `0, …, n + 3`. -/
noncomputable def ord (n : ℕ) (hn : 15 ≤ n) : Fin n ⊕ Fin 4 ≃ Fin (n + 4) :=
  Equiv.ofBijective (ordFun n hn)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨ordFun_injective n hn, by simp⟩)

/-! ### `mad` is at least the average degree -/

/-- The whole vertex set is a witness in `mad`: `mad G ≥ 2 |E(G)| / |V(G)|`. -/
theorem avg_le_mad {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * (G.edgeFinset.card : ℝ) / Fintype.card V ≤ mad G := by
  have hf : G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ (univ : Finset V)) = G.edgeFinset :=
    filter_true_of_mem (fun _ _ v _ => mem_univ v)
  unfold mad
  apply le_csSup
  · refine (Set.finite_range (fun s : Finset V =>
      2 * ((G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ s)).card : ℝ) / s.card)).bddAbove.mono ?_
    rintro r ⟨s, -, rfl⟩
    exact ⟨s, rfl⟩
  · exact ⟨univ, univ_nonempty, by rw [hf, card_univ]⟩

end JDegrees

open JDegrees

/-- Remark 4.8 (ii), v3.90 l. 721: "The vertex `a_1` is adjacent to `v_1`, `v_5`, `v_9` and `v_13`, so it has degree
at least `4`." (`v_i` is `Sum.inl ⟨i - 1, _⟩`, `a_1` is `Sum.inr 1`; so the maximum degree is above `3`.) -/
theorem rem_4_8_ii_proved (n : ℕ) (hn : 15 ≤ n) :
    (Jgraph n).Adj (.inr 1) (.inl ⟨0, by omega⟩) ∧ (Jgraph n).Adj (.inr 1) (.inl ⟨4, by omega⟩) ∧
      (Jgraph n).Adj (.inr 1) (.inl ⟨8, by omega⟩) ∧ (Jgraph n).Adj (.inr 1) (.inl ⟨12, by omega⟩) ∧
      4 ≤ (Jgraph n).degree (.inr 1) ∧ 3 < (Jgraph n).maxDegree := by
  have a0 : (Jgraph n).Adj (.inr 1) (.inl ⟨0, lt_n hn 0⟩) := by simp [FactsAux.adj_inr_inl]
  have a4 : (Jgraph n).Adj (.inr 1) (.inl ⟨4, lt_n hn 4⟩) := by simp [FactsAux.adj_inr_inl]
  have a8 : (Jgraph n).Adj (.inr 1) (.inl ⟨8, lt_n hn 8⟩) := by simp [FactsAux.adj_inr_inl]
  have a12 : (Jgraph n).Adj (.inr 1) (.inl ⟨12, lt_n hn 12⟩) := by simp [FactsAux.adj_inr_inl]
  have hsub : ({.inl ⟨0, lt_n hn 0⟩, .inl ⟨4, lt_n hn 4⟩, .inl ⟨8, lt_n hn 8⟩, .inl ⟨12, lt_n hn 12⟩} :
      Finset (Fin n ⊕ Fin 4)) ⊆ (Jgraph n).neighborFinset (.inr 1) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [SimpleGraph.mem_neighborFinset]
    rcases hx with rfl | rfl | rfl | rfl
    exacts [a0, a4, a8, a12]
  have hcard : ({.inl ⟨0, lt_n hn 0⟩, .inl ⟨4, lt_n hn 4⟩, .inl ⟨8, lt_n hn 8⟩, .inl ⟨12, lt_n hn 12⟩} :
      Finset (Fin n ⊕ Fin 4)).card = 4 := by
    rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp), card_insert_of_notMem (by simp),
      card_singleton]
  have hdeg : 4 ≤ (Jgraph n).degree (.inr 1) := by
    have h := card_le_card hsub
    rw [hcard] at h
    rwa [← SimpleGraph.card_neighborFinset_eq_degree]
  exact ⟨a0, a4, a8, a12, hdeg, lt_of_lt_of_le (by omega) (hdeg.trans ((Jgraph n).degree_le_maxDegree _))⟩

/-- Remark 4.8 (iv), v3.90 l. 722-723: "A first-fit colouring in an order that begins with `v_1, v_4, v_5, v_10, v_7,
v_8, v_9, a_1` gives these vertices the colours `1, 1, 2, 1, 1, 2, 3, 4`, so the Grundy number of `J_ℓ` is at least
`4`." (Lean's colours start at `0`; the first conjunct shows that such an order exists.) -/
theorem rem_4_8_iv_proved (n : ℕ) (hn : 15 ≤ n) :
    let L : List (Fin n ⊕ Fin 4) := [.inl ⟨0, by omega⟩, .inl ⟨3, by omega⟩, .inl ⟨4, by omega⟩, .inl ⟨9, by omega⟩,
      .inl ⟨6, by omega⟩, .inl ⟨7, by omega⟩, .inl ⟨8, by omega⟩, .inr 1]
    (∃ ρ : Fin n ⊕ Fin 4 ≃ Fin (n + 4), L.map (fun x => (ρ x).val) = [0, 1, 2, 3, 4, 5, 6, 7]) ∧
      (∀ (ρ : Fin n ⊕ Fin 4 ≃ Fin (n + 4)) (c : Fin n ⊕ Fin 4 → ℕ), IsGreedyRel (Jgraph n) ρ c →
        L.map (fun x => (ρ x).val) = [0, 1, 2, 3, 4, 5, 6, 7] → L.map c = [0, 0, 1, 0, 0, 1, 2, 3]) ∧
      4 ≤ grundyNumber (Jgraph n) := by
  dsimp only
  have hord : [Sum.inl ⟨0, lt_n hn 0⟩, .inl ⟨3, lt_n hn 3⟩, .inl ⟨4, lt_n hn 4⟩, .inl ⟨9, lt_n hn 9⟩,
      .inl ⟨6, lt_n hn 6⟩, .inl ⟨7, lt_n hn 7⟩, .inl ⟨8, lt_n hn 8⟩, .inr 1].map (fun x => (ord n hn x).val) =
      [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  have hcol : ∀ {m : ℕ} (ρ : Fin n ⊕ Fin 4 ≃ Fin m) (c : Fin n ⊕ Fin 4 → ℕ), IsGreedyRel (Jgraph n) ρ c →
      [Sum.inl ⟨0, lt_n hn 0⟩, .inl ⟨3, lt_n hn 3⟩, .inl ⟨4, lt_n hn 4⟩, .inl ⟨9, lt_n hn 9⟩,
        .inl ⟨6, lt_n hn 6⟩, .inl ⟨7, lt_n hn 7⟩, .inl ⟨8, lt_n hn 8⟩, .inr 1].map (fun x => (ρ x).val) =
        [0, 1, 2, 3, 4, 5, 6, 7] →
      [Sum.inl ⟨0, lt_n hn 0⟩, .inl ⟨3, lt_n hn 3⟩, .inl ⟨4, lt_n hn 4⟩, .inl ⟨9, lt_n hn 9⟩,
        .inl ⟨6, lt_n hn 6⟩, .inl ⟨7, lt_n hn 7⟩, .inl ⟨8, lt_n hn 8⟩, .inr 1].map c = [0, 0, 1, 0, 0, 1, 2, 3] := by
    intro m ρ c hc hL
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hL
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hL
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := colours hn ρ c hc h0 h1 h2 h3 h4 h5 h6 h7
    simp only [List.map_cons, List.map_nil, c0, c1, c2, c3, c4, c5, c6, c7]
  refine ⟨⟨ord n hn, hord⟩, fun ρ c hc hL => hcol ρ c hc hL, ?_⟩
  -- the order at the type used by `grundyNumber`
  set ρ' : Fin n ⊕ Fin 4 ≃ Fin (Fintype.card (Fin n ⊕ Fin 4)) :=
    (ord n hn).trans (finCongr (FactsAux.Jgraph_card n).symm) with hρ'
  obtain ⟨c, hc⟩ := Misc.exists_greedyRel (Jgraph n) ρ'
  have hcs := hcol ρ' c hc hord
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
  obtain ⟨c0, -, c2, -, -, -, c6, c7⟩ := hcs
  have hsub : ({0, 1, 2, 3} : Finset ℕ) ⊆ univ.image c := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [mem_image.mpr ⟨_, mem_univ _, c0⟩, mem_image.mpr ⟨_, mem_univ _, c2⟩,
      mem_image.mpr ⟨_, mem_univ _, c6⟩, mem_image.mpr ⟨_, mem_univ _, c7⟩]
  exact le_trans (card_le_card hsub) ((grundyNumber_spec_proved (Jgraph n)).2 ρ' c hc)

/-- Remark 4.8 (v), v3.90 l. 724-725: "`J_ℓ` has `ℓ + 4` vertices and `2ℓ − 1` edges, so its maximum average degree is
at least `2(2ℓ − 1)/(ℓ + 4) > 3`." (Lean's `n` is the paper's `ℓ`.) -/
theorem rem_4_8_v_proved (n : ℕ) (hn : 15 ≤ n) :
    Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧ (Jgraph n).edgeFinset.card = 2 * n - 1 ∧
      2 * (2 * (n : ℝ) - 1) / (n + 4) ≤ mad (Jgraph n) ∧ (3 : ℝ) < 2 * (2 * (n : ℝ) - 1) / (n + 4) := by
  have hE : (Jgraph n).edgeFinset.card = 2 * n - 1 := by
    rw [FactsAux.pathApex_edges]
    omega
  have hnR : (15 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨FactsAux.Jgraph_card n, hE, ?_, ?_⟩
  · have h := avg_le_mad (Jgraph n)
    rw [hE, FactsAux.Jgraph_card, Nat.cast_sub (by omega)] at h
    push_cast at h
    exact h
  · rw [lt_div_iff₀ (by positivity)]
    linarith

end Cereceda
