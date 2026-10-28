/-
NagataHigman/Defs/FreeAlgebra.lean — the free non-unital algebra, the T-ideal of x^n, and d(n) (paper Section 2.1).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.04, lines 187-219.
Indexing: the paper's letters x_1, x_2, ... are `letter F 0`, `letter F 1`, ... here (shift by one).
-/
import Mathlib

noncomputable section

namespace NagataHigman

/-- The product `x 0 * x 1 * ⋯ * x (m-1)` of a tuple, in any type with a multiplication.
The empty product (`m = 0`) has no meaning in a non-unital algebra; it is set to `0` and every statement
that uses `tupleProd` asks `1 ≤ m`. -/
def tupleProd {R : Type*} [Mul R] [Zero R] : (m : ℕ) → (Fin m → R) → R
  | 0, _ => 0
  | 1, x => x 0
  | (m + 2), x => tupleProd (m + 1) (fun i => x i.castSucc) * x (Fin.last (m + 1))

/-- `x ^ n` in a non-unital algebra: the product of `n` copies of `x` (meaningful for `1 ≤ n`). -/
def nuPow {R : Type*} [Mul R] [Zero R] (x : R) (n : ℕ) : R := tupleProd n (fun _ => x)

variable (F : Type*) [Field F]

/-- The free non-unital associative algebra `F⟨X⟩` on `X = {x_0, x_1, …}` (paper: `x_1, x_2, …`):
the semigroup algebra of the free semigroup on `ℕ`. Its elements are polynomials without constant term. -/
abbrev FreeNUAlg : Type _ := MonoidAlgebra F (FreeSemigroup ℕ)

/-- The letter `x_i` (paper: `x_{i+1}`). -/
def letter (i : ℕ) : FreeNUAlg F := MonoidAlgebra.single (FreeSemigroup.of i) (1 : F)

/-- A subspace `S ⊆ F⟨X⟩` is a T-ideal: a two-sided ideal that is closed under every endomorphism of the
non-unital algebra `F⟨X⟩` (paper lines 188-189). -/
structure IsTIdeal (S : Submodule F (FreeNUAlg F)) : Prop where
  mul_left : ∀ r a : FreeNUAlg F, a ∈ S → r * a ∈ S
  mul_right : ∀ r a : FreeNUAlg F, a ∈ S → a * r ∈ S
  endo : ∀ (φ : FreeNUAlg F →ₙₐ[F] FreeNUAlg F) (a : FreeNUAlg F), a ∈ S → φ a ∈ S

/-- `T = (x^n)^T`: the smallest T-ideal of `F⟨X⟩` that contains `x^n`, `x = x_0` (paper line 190). -/
def TIdeal (n : ℕ) : Submodule F (FreeNUAlg F) :=
  sInf {S | IsTIdeal F S ∧ nuPow (letter F 0) n ∈ S}

/-- The word `x_0 x_1 ⋯ x_{m-1}` (paper: `x_1 ⋯ x_m`). -/
def firstLettersProd (m : ℕ) : FreeNUAlg F := tupleProd m (fun i => letter F i)

/-- The Nagata–Higman index `d(n) = min {m ≥ 1 : x_1 ⋯ x_m ∈ T}` (paper line 192). It is `sInf ∅ = 0` if no
such `m` exists; for that reason every upper bound in `Paper/Statements.lean` ALSO states the membership
`firstLettersProd F m ∈ TIdeal F n` itself, so no bound is true merely because the set is empty. -/
def nhIndex (n : ℕ) : ℕ := sInf {m | 1 ≤ m ∧ firstLettersProd F m ∈ TIdeal F n}

/-- The multilinear word `x_{w 0} x_{w 1} ⋯ x_{w (m-1)}` of a permutation `w` of `{0, …, m-1}`. -/
def multilinWord {m : ℕ} (w : Equiv.Perm (Fin m)) : FreeNUAlg F :=
  tupleProd m (fun i => letter F (w i))

/-- `V_m`: the multilinear polynomials in `x_0, …, x_{m-1}`, spanned by the `m!` multilinear words
(paper line 192). -/
def multilinSpace (m : ℕ) : Submodule F (FreeNUAlg F) :=
  Submodule.span F (Set.range (multilinWord F (m := m)))

/-- `W_{n,m} = V_m ∩ T` (paper line 193). -/
def multilinIdentities (n m : ℕ) : Submodule F (FreeNUAlg F) := multilinSpace F m ⊓ TIdeal F n

end NagataHigman

end
