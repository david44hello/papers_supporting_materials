/-
Cereceda/Defs/LowerBound.lean — the graphs H_n and J_n of Section 4, their colourings σ±, plain colourings, height
functions on the path, and a straight-line drawing (for "planar").
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: read against short v3.90 Section 4 (l. 574-734: `H_ℓ` l. 580-584; `σ±`, plain colourings and height
functions l. 591-596; `J_ℓ` l. 672-674 and 682). Lean's `n` is the paper's ℓ (the number of path vertices).
INDEXING: the path vertex `Sum.inl i` (`i : Fin n`, 0-based) is the paper's `v_{i+1}`.
-/
import Cereceda.Defs.Basic

namespace Cereceda

open Finset

/-- A path `v_1 … v_n` with `k` extra vertices (apices) `Sum.inr j`; the path vertex `v_{i+1}` (`Sum.inl i`) is joined
to the apex `f i`; apices are pairwise non-adjacent. -/
def pathApex (n k : ℕ) (f : Fin n → Fin k) : SimpleGraph (Fin n ⊕ Fin k) where
  Adj a b := match a, b with
    | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
    | .inl i, .inr j => f i = j
    | .inr j, .inl i => f i = j
    | .inr _, .inr _ => False
  symm := ⟨fun a b h => by
    rcases a with i | i <;> rcases b with j | j <;> simp_all <;> omega⟩
  loopless := ⟨fun a h => by rcases a with i | i <;> simp_all⟩

instance (n k : ℕ) (f : Fin n → Fin k) : DecidableRel (pathApex n k f).Adj := fun a b =>
  match a, b with
  | .inl i, .inl j => inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))
  | .inl i, .inr j => inferInstanceAs (Decidable (f i = j))
  | .inr j, .inl i => inferInstanceAs (Decidable (f i = j))
  | .inr _, .inr _ => inferInstanceAs (Decidable False)

/-- `H_n` (paper Section 4): the path `v_1 ⋯ v_n`, a vertex `a = Sum.inr 0` joined to every `v_i` with `i` odd and
a vertex `b = Sum.inr 1` joined to every `v_i` with `i` even (0-based index `i - 1` even ↔ `i` odd). -/
abbrev Hgraph (n : ℕ) : SimpleGraph (Fin n ⊕ Fin 2) :=
  pathApex n 2 (fun i => ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩)

/-- `J_n` (paper Section 4.2, girth six; also defined in Section 1, v3.90 l. 194-196): the path `v_1 ⋯ v_n` and four
vertices `a_0, …, a_3` (`Sum.inr j`), where `a_j` is joined to every `v_i` with `i ≡ j (mod 4)` (0-based index `i - 1`, so `j = (index + 1) % 4`). -/
abbrev Jgraph (n : ℕ) : SimpleGraph (Fin n ⊕ Fin 4) :=
  pathApex n 4 (fun i => ⟨(i.val + 1) % 4, Nat.mod_lt _ (by norm_num)⟩)

/-- `σ⁺` (paper Section 4): every apex on `3`, `v_i` on `(i - 1) mod 3`. -/
def sigmaPlus (n k : ℕ) : Fin n ⊕ Fin k → Fin 4
  | .inl i => ⟨i.val % 3, by omega⟩
  | .inr _ => 3

/-- `σ⁻` (paper Section 4): every apex on `3`, `v_i` on `-(i - 1) mod 3`. -/
def sigmaMinus (n k : ℕ) : Fin n ⊕ Fin k → Fin 4
  | .inl i => ⟨(3 - i.val % 3) % 3, by omega⟩
  | .inr _ => 3

/-- The two sides of `H_n` (paper Section 4): side `0` = the odd path vertices and `b`; side `1` = the even path
vertices and `a` (0-based index `i`: `v_{i+1}` is odd iff `i` is even). -/
def sideH (n : ℕ) : Fin n ⊕ Fin 2 → Fin 2
  | .inl i => ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩
  | .inr j => ⟨(j.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The two sides of `J_n` (paper Section 4): side `0` = the odd path vertices with `a_0, a_2`; side `1` = the even
path vertices with `a_1, a_3`. -/
def sideJ (n : ℕ) : Fin n ⊕ Fin 4 → Fin 2
  | .inl i => ⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩
  | .inr j => ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩

/-- A colouring is plain (paper Section 4) if every apex has the colour `3`. -/
def IsPlain {n k : ℕ} (c : Fin n ⊕ Fin k → Fin 4) : Prop :=
  ∀ j, c (.inr j) = 3

/-- A height function of a plain colouring `c` (paper Section 4): `h : ℕ → ℤ` (only `h 0, …, h (n-1)` matter) with
`h (i+1) - h i = s_i` for every step, where the step `s_i ∈ {+1, -1}` is `col(v_{i+2}) - col(v_{i+1}) (mod 3)`.
The winding is `W = h (n-1) - h 0`. -/
def IsPathHeight {n k : ℕ} (c : Fin n ⊕ Fin k → Fin 4) (h : ℕ → ℤ) : Prop :=
  ∀ i (hi : i + 1 < n),
    (h (i + 1) - h i = 1 ∨ h (i + 1) - h i = -1) ∧
    (((h (i + 1) - h i : ℤ) : ZMod 3) =
      ((c (.inl ⟨i + 1, hi⟩)).val : ZMod 3) - ((c (.inl ⟨i, by omega⟩)).val : ZMod 3))

/-- `G` has a straight-line drawing in the plane: injective points, no vertex inside an edge it is not an end of,
and two different edges meet only in a common end. This implies planarity under every usual definition; it is the
form in which we prove "planar" (paper Proposition 1.3, Section 4). -/
def IsStraightLinePlanar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ p : V → ℝ × ℝ, Function.Injective p ∧
    (∀ u v w, G.Adj u v → w ≠ u → w ≠ v → p w ∉ segment ℝ (p u) (p v)) ∧
    (∀ u v u' v', G.Adj u v → G.Adj u' v' → s(u, v) ≠ s(u', v') →
      segment ℝ (p u) (p v) ∩ segment ℝ (p u') (p v') ⊆ p '' ({u, v} ∩ {u', v'}))

end Cereceda
