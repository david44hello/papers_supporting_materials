/-
LeeDiam/Defs/Chain.lean — the notions of Section 4 of paper 004 ("The chain polytope of the band", short v1.50,
sec_chain.tex): words, rows, σ, column translations, outer traces, merged walks, tame walks, helpers.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against sec_chain.tex v1.50 (the "l." numbers below). Indexing: columns 0-based (`Fin k`); the
paper's column `i` is Lean's `i - 1`; rows `0, 1, 2` = `a, b, c`. A walk is a list of states (Defs/Walks.lean).
-/
import LeeDiam.Defs.Basic
import LeeDiam.Defs.Walks
import LeeDiam.Defs.Band

namespace LeeDiam

open Band

variable {k : ℕ}

/-- Row `r`, columns `s, …, e` (0-based, inclusive): the paper's `{a_{s+1}, …, a_{e+1}}` for `r = 0`. -/
def rowSeg (r : Fin 3) (s e : ℕ) : Set (Band k) := {x | x.2 = r ∧ s ≤ x.1.val ∧ x.1.val ≤ e}

/-- The set described by a word `w` (l. 14): `w i = some r` puts the element of row `r` in column `i`; `none` = `-`. -/
def ofWord (w : Fin k → Option (Fin 3)) : Set (Band k) := {x | w x.1 = some x.2}

/-- The forbidden neighboring letter pairs `ab`, `ac`, `ca`, `cb` of l. 14. -/
def BadPair : Option (Fin 3) → Option (Fin 3) → Prop
  | some 0, some 1 => True
  | some 0, some 2 => True
  | some 2, some 0 => True
  | some 2, some 1 => True
  | _, _ => False

/-- `σ` (l. 30): exchanges `a_i` and `c_i` and fixes `b_i` (the row index `r ↦ 2 - r`). -/
def sigmaAC (x : Band k) : Band k := (x.1, Fin.rev x.2)

/-- The translation of the columns by `d` (l. 21), from `B_k` into `B_{k'}`. -/
def colShift {k' : ℕ} (d : ℕ) (hd : k + d ≤ k') (x : Band k) : Band k' :=
  (⟨x.1.val + d, by have := x.1.isLt; omega⟩, x.2)

open Classical in
/-- The outer element of a set in column `e` (l. 32), if any (for an antichain there is at most one). -/
noncomputable def outerAt (X : Set (Band k)) (e : Fin k) : Option (Band k) :=
  if a e ∈ X then some (a e) else if c e ∈ X then some (c e) else none

/-- The outer trace of a walk at column `e` (l. 32): the outer elements of the states in column `e` (`none` = `-`),
consecutive repetitions merged. -/
noncomputable def outerTrace (W : List (Set (Band k))) (e : Fin k) : List (Option (Band k)) :=
  (W.map (outerAt · e)).destutter (· ≠ ·)

/-- The difference of move `m` of `W`, between the states `m` and `m + 1`. -/
def moveDiff {P : Type} (W : List (Set P)) (m : ℕ) : Set P := symmDiff (W.getD m ∅) (W.getD (m + 1) ∅)

/-- The graph on the moves of one step `β` of a merge (Lemma 4.3 (ii), l. 40): move `m` of walk `t` is a pair
`⟨t, m⟩`; two moves are joined when some element of the difference of one is comparable to some element of the
difference of the other. -/
def moveGraph {r M : ℕ} (W : Fin r → List (Set (Band k))) (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M)
    (β : Fin M) : SimpleGraph {p : (t : Fin r) × Fin ((W t).length - 1) // step p.1 p.2 = β} where
  Adj p q := p ≠ q ∧ ∃ x ∈ moveDiff (W p.1.1) p.1.2, ∃ y ∈ moveDiff (W q.1.1) q.1.2, Comp x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    obtain ⟨-, x, hx, y, hy, hxy⟩ := h
    exact ⟨y, hy, x, hx, hxy.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The state `Z_α` of a merge (Lemma 4.3, l. 36): the union of the states the walks have reached after the steps
`0, …, α - 1` (0-based steps), i.e. walk `t` has made its moves of step index `< α`. -/
def mergedState {r M : ℕ} (W : Fin r → List (Set (Band k))) (step : (t : Fin r) → Fin ((W t).length - 1) → Fin M)
    (α : ℕ) : Set (Band k) :=
  ⋃ t, (W t).getD (Finset.univ.filter (fun m => (step t m).val < α)).card ∅

/-- A walk tame at column `i` with outer element `h` (Definition 4.7, l. 77): all states lie in the columns `≤ i`,
and the outer trace at column `i` is `(-, h, -)` for an outer element `h` of column `i`. -/
def IsTameAt (W : List (Set (Band k))) (i : Fin k) (h : Band k) : Prop :=
  (∀ X ∈ W, ∀ x ∈ X, x.1 ≤ i) ∧ h.1 = i ∧ h.2 ≠ 1 ∧ outerTrace W i = [none, some h, none]

/-- The helpers of Lemma 4.5 (l. 61): `c_t` for the columns `t ∈ [s, e]` with `t - s ≡ par (mod 2)`; `par = 1` gives
the even helper positions (second, fourth, … column), `par = 0` the odd ones (first, third, …). -/
def helperSet (par s e : ℕ) : Set (Band k) := {x | x.2 = 2 ∧ s ≤ x.1.val ∧ x.1.val ≤ e ∧ (x.1.val - s) % 2 = par}

end LeeDiam
