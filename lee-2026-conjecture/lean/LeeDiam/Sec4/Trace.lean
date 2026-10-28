/-
LeeDiam/Sec4/Trace.lean — Section 4 helpers: lists with repeated entries ("stretches") and `List.destutter`, used for
the outer traces (sec_chain.tex l. 31) of merged, reversed and σ-mapped walks.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import Mathlib

namespace LeeDiam.S4

section Stretch

variable {α : Type}

/-- `Stretch l l'`: the list `l'` is `l` with every entry repeated, in place, one or more times. -/
inductive Stretch : List α → List α → Prop
  | nil : Stretch [] []
  | cons (x : α) {l l' : List α} : Stretch l l' → Stretch (x :: l) (x :: l')
  | dup (x : α) {l l' : List α} : Stretch (x :: l) l' → Stretch (x :: l) (x :: l')

variable [DecidableEq α]

theorem destutter'_ne_eq_cons (a : α) (l : List α) : ∃ t, l.destutter' (· ≠ ·) a = a :: t := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    rw [List.destutter'_cons]
    split_ifs with h
    · exact ⟨_, rfl⟩
    · exact ih a

theorem stretch_destutter' {l l' : List α} (h : Stretch l l') (a : α) :
    l'.destutter' (· ≠ ·) a = l.destutter' (· ≠ ·) a := by
  induction h generalizing a with
  | nil => rfl
  | cons x _ ih =>
    rw [List.destutter'_cons, List.destutter'_cons]
    simp only [ih]
  | @dup x l l' _ ih =>
    rw [List.destutter'_cons]
    simp only [ih]
    by_cases hax : a ≠ x
    · rw [ite_eq_left hax, List.destutter'_cons, ite_eq_right (not_not.2 rfl), List.destutter'_cons, ite_eq_left hax]
    · rw [ite_eq_right hax]

/-- Repeating entries does not change `destutter`. -/
theorem stretch_destutter {l l' : List α} (h : Stretch l l') : l'.destutter (· ≠ ·) = l.destutter (· ≠ ·) := by
  cases h with
  | nil => rfl
  | cons x h' =>
    rw [List.destutter_cons', List.destutter_cons']
    exact stretch_destutter' h' x
  | dup x h' =>
    rw [List.destutter_cons', stretch_destutter' h' x, List.destutter'_cons, ite_eq_right (not_not.2 rfl),
      List.destutter_cons']

theorem stretch_destutter'_self (a : α) (l : List α) : Stretch (l.destutter' (· ≠ ·) a) (a :: l) := by
  induction l generalizing a with
  | nil => exact Stretch.cons a Stretch.nil
  | cons b l ih =>
    rw [List.destutter'_cons]
    split_ifs with hab
    · exact Stretch.cons a (ih b)
    · have hab' : a = b := not_not.1 hab
      subst hab'
      obtain ⟨t, ht⟩ := destutter'_ne_eq_cons a l
      have key := ih a
      rw [ht] at key ⊢
      exact Stretch.dup a key

/-- Every list is a stretch of its `destutter`. -/
theorem stretch_destutter_self (l : List α) : Stretch (l.destutter (· ≠ ·)) l := by
  cases l with
  | nil => exact Stretch.nil
  | cons a l => exact stretch_destutter'_self a l

omit [DecidableEq α] in
theorem stretch_cons_inv {x : α} {l L : List α} (h : Stretch (x :: l) L) :
    ∃ p, 1 ≤ p ∧ ∃ L', L = List.replicate p x ++ L' ∧ Stretch l L' := by
  generalize hl : x :: l = l₀ at h
  induction h with
  | nil => exact absurd hl (List.cons_ne_nil x l)
  | @cons y l₁ l₁' h' _ =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    exact ⟨1, le_rfl, l₁', rfl, h'⟩
  | @dup y l₁ l₁' _ ih =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    obtain ⟨p, hp, L', rfl, hL'⟩ := ih rfl
    exact ⟨p + 1, by omega, L', rfl, hL'⟩

omit [DecidableEq α] in
theorem stretch_replicate_append {x : α} {l L : List α} {p : ℕ} (hp : 1 ≤ p) (h : Stretch l L) :
    Stretch (x :: l) (List.replicate p x ++ L) := by
  induction p, hp using Nat.le_induction with
  | base => exact Stretch.cons x h
  | succ n _ ih => exact Stretch.dup x ih

/-- A list destutters to `[u, v, w]` exactly when it is `u^p v^q w^r` with `p, q, r ≥ 1`. -/
theorem destutter_eq_three_iff {u v w : α} (huv : u ≠ v) (hvw : v ≠ w) (L : List α) :
    L.destutter (· ≠ ·) = [u, v, w] ↔ ∃ p q r, 1 ≤ p ∧ 1 ≤ q ∧ 1 ≤ r ∧
      L = List.replicate p u ++ List.replicate q v ++ List.replicate r w := by
  constructor
  · intro h
    have hs := stretch_destutter_self L
    rw [h] at hs
    obtain ⟨p, hp, L₁, rfl, h₁⟩ := stretch_cons_inv hs
    obtain ⟨q, hq, L₂, rfl, h₂⟩ := stretch_cons_inv h₁
    obtain ⟨r, hr, L₃, rfl, h₃⟩ := stretch_cons_inv h₂
    cases h₃
    exact ⟨p, q, r, hp, hq, hr, by simp⟩
  · rintro ⟨p, q, r, hp, hq, hr, rfl⟩
    have hw : Stretch [w] (List.replicate r w) := by
      simpa using stretch_replicate_append (L := []) hr (Stretch.nil (α := α))
    have hs : Stretch [u, v, w] (List.replicate p u ++ List.replicate q v ++ List.replicate r w) := by
      rw [List.append_assoc]
      exact stretch_replicate_append hp (stretch_replicate_append hq hw)
    rw [stretch_destutter hs]
    exact List.destutter_of_isChain _ _ (by simp [huv, hvw])

omit [DecidableEq α] in
/-- Reading a sequence `f` along a position function `pos` that starts at `0` and moves by `0` or `1` stretches it. -/
theorem stretch_of_pos (M : ℕ) : ∀ (f : ℕ → α) (pos : ℕ → ℕ) (n : ℕ), pos 0 = 0 → pos M = n →
    (∀ t < M, pos (t + 1) = pos t ∨ pos (t + 1) = pos t + 1) →
    Stretch ((List.range (n + 1)).map f) ((List.range (M + 1)).map (fun t => f (pos t))) := by
  induction M with
  | zero =>
    intro f pos n h0 hM _
    subst hM
    simp only [h0, Nat.zero_add, List.range_one, List.map_cons, List.map_nil]
    exact Stretch.cons _ Stretch.nil
  | succ M ih =>
    intro f pos n h0 hM hinc
    have hmono : ∀ t, 1 ≤ t → t ≤ M + 1 → pos 1 ≤ pos t := by
      intro t ht1 ht2
      induction t, ht1 using Nat.le_induction with
      | base => exact le_rfl
      | succ t ht ih' =>
        have h1 := hinc t (by omega)
        have h2 := ih' (by omega)
        omega
    rw [List.range_succ_eq_map (n := M + 1), List.map_cons, List.map_map, h0]
    rcases hinc 0 (by omega) with h1 | h1
    · have key := ih f (fun t => pos (t + 1)) n (by simpa [h0] using h1) hM
        (fun t ht => hinc (t + 1) (by omega))
      rw [List.range_succ_eq_map (n := n), List.map_cons, List.map_map] at key ⊢
      exact Stretch.dup (f 0) key
    · have hp1 : pos 1 = 1 := by rw [h1, h0]
      have hn : 1 ≤ n := by
        have := hmono (M + 1) le_add_self le_rfl
        omega
      have key := ih (fun t => f (t + 1)) (fun t => pos (t + 1) - 1) (n - 1) (by simp [hp1]) (by simp [hM])
        (fun t ht => by
          have h3 := hinc (t + 1) (by omega)
          have h4 := hmono (t + 1) (by omega) (by omega)
          omega)
      have hn' : n - 1 + 1 = n := by omega
      rw [hn'] at key
      have hcongr : (List.range (M + 1)).map (fun t => (fun t => f (t + 1)) ((fun t => pos (t + 1) - 1) t)) =
          (List.range (M + 1)).map ((fun t => f (pos t)) ∘ Nat.succ) := by
        apply List.map_congr_left
        intro t ht
        have ht' := List.mem_range.1 ht
        have h4 := hmono (t + 1) (by omega) (by omega)
        show f (pos (t + 1) - 1 + 1) = f (pos (t + 1))
        congr 1
        omega
      rw [hcongr] at key
      rw [List.range_succ_eq_map (n := n), List.map_cons, List.map_map]
      exact Stretch.cons (f 0) key

theorem map_range_getD {β : Type} (L : List β) (d : β) :
    (List.range L.length).map (fun i => L.getD i d) = L := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

end Stretch

end LeeDiam.S4
