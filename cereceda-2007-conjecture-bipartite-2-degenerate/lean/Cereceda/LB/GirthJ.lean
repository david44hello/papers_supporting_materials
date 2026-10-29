/-
Cereceda/LB/GirthJ.lean — the graph `J_n` (n ≥ 5) has girth exactly six (paper Section 4.2, short v3.90 l. 674-679).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

PROOF ROUTE: `≤ 6` from the 6-cycle a_1 v_1 v_2 v_3 v_4 v_5 a_1. `≥ 6`: `sideJ` is a proper 2-colouring, so every
closed walk has even length; a cycle has length ≥ 3, hence ≥ 4; a 4-cycle u0 u1 u2 u3 would give the two different
vertices u0, u2 two different common neighbours u1, u3, but in `J_n` two different vertices share at most one.
-/
import Cereceda.Defs.LowerBound

namespace Cereceda.GirthAux

open SimpleGraph

/-! ### Adjacency in `J_n`, unfolded -/

lemma Jgraph_adj_inl_inl {n : ℕ} (i j : Fin n) :
    (Jgraph n).Adj (.inl i) (.inl j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := Iff.rfl

lemma Jgraph_adj_inl_inr {n : ℕ} (i : Fin n) (j : Fin 4) :
    (Jgraph n).Adj (.inl i) (.inr j) ↔ (i.val + 1) % 4 = j.val := Fin.ext_iff

lemma Jgraph_adj_inr_inl {n : ℕ} (j : Fin 4) (i : Fin n) :
    (Jgraph n).Adj (.inr j) (.inl i) ↔ (i.val + 1) % 4 = j.val := Fin.ext_iff

lemma Jgraph_not_adj_inr_inr {n : ℕ} (j j' : Fin 4) : ¬ (Jgraph n).Adj (.inr j) (.inr j') := id

lemma Jgraph_adj_inr_inr {n : ℕ} (j j' : Fin 4) : (Jgraph n).Adj (.inr j) (.inr j') ↔ False := Iff.rfl

/-! ### `≥ 6`, step 1: every closed walk has even length (`sideJ` is a proper 2-colouring) -/

lemma Jgraph_sideJ_adj {n : ℕ} {a b : Fin n ⊕ Fin 4} (h : (Jgraph n).Adj a b) :
    ((sideJ n a).val + (sideJ n b).val) % 2 = 1 := by
  rcases a with i | i <;> rcases b with j | j
  · rw [Jgraph_adj_inl_inl] at h
    simp only [sideJ]
    omega
  · rw [Jgraph_adj_inl_inr] at h
    simp only [sideJ]
    omega
  · rw [Jgraph_adj_inr_inl] at h
    simp only [sideJ]
    omega
  · exact absurd h (Jgraph_not_adj_inr_inr i j)

lemma Jgraph_walk_parity {n : ℕ} {a b : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk a b) :
    (w.length + (sideJ n a).val + (sideJ n b).val) % 2 = 0 := by
  induction w with
  | nil =>
    rw [Walk.length_nil]
    omega
  | cons h p ih =>
    have hab := Jgraph_sideJ_adj h
    rw [Walk.length_cons]
    omega

lemma Jgraph_closed_walk_even {n : ℕ} {a : Fin n ⊕ Fin 4} (w : (Jgraph n).Walk a a) :
    w.length % 2 = 0 := by
  have := Jgraph_walk_parity w
  omega

/-! ### `≥ 6`, step 2: two different vertices have at most one common neighbour -/

lemma Jgraph_common_nbr_unique {n : ℕ} {x y z z' : Fin n ⊕ Fin 4} (hxy : x ≠ y)
    (hxz : (Jgraph n).Adj x z) (hyz : (Jgraph n).Adj y z)
    (hxz' : (Jgraph n).Adj x z') (hyz' : (Jgraph n).Adj y z') : z = z' := by
  rcases x with i | i <;> rcases y with j | j <;> rcases z with k | k <;> rcases z' with l | l <;>
    simp only [Jgraph_adj_inl_inl, Jgraph_adj_inl_inr, Jgraph_adj_inr_inl, Jgraph_adj_inr_inr, ne_eq,
      Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff, reduceCtorEq] at hxy hxz hyz hxz' hyz' ⊢ <;>
    omega

/-! ### `≥ 6`, step 3: no cycle of length four -/

lemma Jgraph_no_four_cycle {n : ℕ} {a : Fin n ⊕ Fin 4} {w : (Jgraph n).Walk a a} (hw : w.IsCycle) :
    w.length ≠ 4 := by
  intro h4
  have h01 : (Jgraph n).Adj (w.getVert 0) (w.getVert 1) := w.adj_getVert_succ (by omega)
  have h12 : (Jgraph n).Adj (w.getVert 1) (w.getVert 2) := w.adj_getVert_succ (by omega)
  have h23 : (Jgraph n).Adj (w.getVert 2) (w.getVert 3) := w.adj_getVert_succ (by omega)
  have h34 : (Jgraph n).Adj (w.getVert 3) (w.getVert 4) := w.adj_getVert_succ (by omega)
  have h4a : w.getVert 4 = a := by
    have := w.getVert_length
    rwa [h4] at this
  rw [Walk.getVert_zero] at h01
  rw [h4a] at h34
  have h02 : a ≠ w.getVert 2 := fun h =>
    absurd ((hw.getVert_endpoint_iff (by omega)).mp h.symm) (by omega)
  have h13 : w.getVert 1 ≠ w.getVert 3 := fun h =>
    absurd (hw.getVert_injOn (by simp; omega) (by simp; omega) h) (by omega)
  exact h13 (Jgraph_common_nbr_unique h02 h01 h12.symm h34.symm h23)

lemma Jgraph_six_le_cycle_length {n : ℕ} {a : Fin n ⊕ Fin 4} {w : (Jgraph n).Walk a a}
    (hw : w.IsCycle) : 6 ≤ w.length := by
  have h3 := hw.three_le_length
  have h2 := Jgraph_closed_walk_even w
  have h4 := Jgraph_no_four_cycle hw
  omega

/-! ### `≤ 6`: the 6-cycle a_1 v_1 v_2 v_3 v_4 v_5 a_1 -/

/-- The closed walk `inr 1, inl 0, inl 1, inl 2, inl 3, inl 4, inr 1` (paper: a_1 v_1 v_2 v_3 v_4 v_5 a_1). -/
def Jgraph_sixCycle (n : ℕ) (hn : 5 ≤ n) : (Jgraph n).Walk (.inr 1) (.inr 1) :=
  .cons (v := .inl ⟨0, by omega⟩) ((Jgraph_adj_inr_inl _ _).mpr (by simp)) <|
  .cons (v := .inl ⟨1, by omega⟩) ((Jgraph_adj_inl_inl _ _).mpr (.inl rfl)) <|
  .cons (v := .inl ⟨2, by omega⟩) ((Jgraph_adj_inl_inl _ _).mpr (.inl rfl)) <|
  .cons (v := .inl ⟨3, by omega⟩) ((Jgraph_adj_inl_inl _ _).mpr (.inl rfl)) <|
  .cons (v := .inl ⟨4, by omega⟩) ((Jgraph_adj_inl_inl _ _).mpr (.inl rfl)) <|
  .cons (v := .inr 1) ((Jgraph_adj_inl_inr _ _).mpr (by simp)) .nil

lemma Jgraph_sixCycle_length (n : ℕ) (hn : 5 ≤ n) : (Jgraph_sixCycle n hn).length = 6 := rfl

lemma Jgraph_sixCycle_isCycle (n : ℕ) (hn : 5 ≤ n) : (Jgraph_sixCycle n hn).IsCycle := by
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def]
    simp [Jgraph_sixCycle]
  · simp [Jgraph_sixCycle]
  · simp [Jgraph_sixCycle]

/-! ### The girth of `J_n` -/

theorem Jgraph_egirth_proved (n : ℕ) (hn : 5 ≤ n) : (Jgraph n).egirth = 6 := by
  apply le_antisymm
  · have := (Jgraph_sixCycle_isCycle n hn).egirth_le_length
    rwa [Jgraph_sixCycle_length] at this
  · rw [le_egirth]
    intro a w hw
    exact_mod_cast Jgraph_six_le_cycle_length hw

end Cereceda.GirthAux
