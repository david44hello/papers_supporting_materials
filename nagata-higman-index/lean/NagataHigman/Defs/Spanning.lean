/-
NagataHigman/Defs/Spanning.lean — the polynomial L and the spanning elements a · L(v_1, …, v_n) · b of (F1).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Defs.FreeAlgebra

noncomputable section

namespace NagataHigman

open Equiv

/-- `L(y_1, …, y_n) = ∑_{π ∈ S_n} y_{π(1)} ⋯ y_{π(n)}` (paper line 206), in any non-unital ring. -/
def symSum {R : Type*} [NonUnitalRing R] (n : ℕ) (y : Fin n → R) : R :=
  ∑ π : Perm (Fin n), tupleProd n (fun k => y (π k))

variable (F : Type*) [Field F]

/-- The word `x_{l_0} x_{l_1} ⋯` of a list of letters (meaningful for a nonempty list). -/
def wordOf (l : List ℕ) : FreeNUAlg F := tupleProd l.length (fun i => letter F (l.get i))

/-- `a · x · b`, where the words `a`, `b` may be empty (then that side is omitted). -/
def sandwich (a b : List ℕ) (x : FreeNUAlg F) : FreeNUAlg F :=
  let left := if a = [] then x else wordOf F a * x
  if b = [] then left else left * wordOf F b

/-- The element `a · L(v_1, …, v_n) · b` of (F1) (paper line 216). -/
def sandwichElem {n : ℕ} (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ) : FreeNUAlg F :=
  sandwich F a b (symSum n (fun i => wordOf F (v i)))

/-- The side condition of (F1) (paper lines 214-218): every `v_i` is a nonempty word, and every letter
`x_0, …, x_{m-1}` occurs exactly once in `a v_1 ⋯ v_n b`. -/
def IsMultilinTriple {n : ℕ} (m : ℕ) (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ) : Prop :=
  (∀ i, v i ≠ []) ∧ (a ++ (List.ofFn v).flatten ++ b).Perm (List.range m)

end NagataHigman

end
