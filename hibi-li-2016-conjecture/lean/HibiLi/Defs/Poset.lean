/-
HibiLi/Defs/Poset.lean — order, chain and chain–order polytopes; the poset X; unimodular equivalence.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Polytope

namespace HibiLi

open Finset

variable (P : Type*) [Fintype P] [PartialOrder P]

/-- A chain of `P`: a finite totally ordered subset (the empty set counts). -/
def IsChainSet (K : Finset P) : Prop := IsChain (· ≤ ·) (K : Set P)

/-- Order polytope (paper line 177): `{v ∈ [0,1]^P : v_p ≤ v_q whenever p ≤ q}`. -/
def orderPolytope : Set (P → ℝ) :=
  {v | (∀ p, 0 ≤ v p ∧ v p ≤ 1) ∧ ∀ p q, p ≤ q → v p ≤ v q}

/-- Chain polytope (paper lines 178–179): `{x ∈ ℝ_{≥0}^P : Σ_{p∈K} x_p ≤ 1 for every chain K}`. -/
def chainPolytope : Set (P → ℝ) :=
  {x | (∀ p, 0 ≤ x p) ∧ ∀ K : Finset P, IsChainSet P K → ∑ p ∈ K, x p ≤ 1}

/-- Chain–order polytope `O_I(P)` (paper lines 225–238, Fourier §2) for an order ideal `I`; chain coordinates on `I`,
order coordinates on `J = P \ I`.  The five inequality families, in the paper's order:
(1) `x_p ≥ 0 (p ∈ I)`; (2) `0 ≤ y_r ≤ 1 (r ∈ J)`; (3) `y_r ≤ y_r' (r ≤ r' in J)`;
(4) `Σ_{p∈K} x_p ≤ y_r` for `r ∈ J` and `K ⊆ I` a chain with `p < r` for all `p ∈ K`;
(5) `Σ_{p∈K} x_p ≤ 1` for `K ⊆ I` a chain. -/
def chainOrderPolytope (I : Set P) : Set (P → ℝ) :=
  {x | (∀ p ∈ I, 0 ≤ x p) ∧
       (∀ r ∉ I, 0 ≤ x r ∧ x r ≤ 1) ∧
       (∀ r r', r ∉ I → r' ∉ I → r ≤ r' → x r ≤ x r') ∧
       (∀ r ∉ I, ∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → (∀ p ∈ K, p < r) → ∑ p ∈ K, x p ≤ x r) ∧
       (∀ K : Finset P, (↑K ⊆ I) → IsChainSet P K → ∑ p ∈ K, x p ≤ 1)}

/-- `P` contains `X` (paper lines 87–92): five elements `a, b, c, g, h` with `a, b < c < g, h`, `a, b` incomparable and
`g, h` incomparable.  (Distinctness of the five follows from these relations.) -/
def ContainsX : Prop :=
  ∃ a b c g h : P, a < c ∧ b < c ∧ c < g ∧ c < h ∧ ¬ a ≤ b ∧ ¬ b ≤ a ∧ ¬ g ≤ h ∧ ¬ h ≤ g

/-- Unimodular equivalence (paper lines 184–187): `Q' = M(Q) + w` with `M` integral, `det M = ±1`, `w` integral. -/
def UnimodEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] (Q Q' : Set (ι → ℝ)) : Prop :=
  ∃ M : Matrix ι ι ℤ, (M.det = 1 ∨ M.det = -1) ∧ ∃ w : ι → ℤ,
    Q' = (fun v => (M.map (Int.cast : ℤ → ℝ)).mulVec v + (fun i => (w i : ℝ))) '' Q

/-! ### Hibi–Li's own conventions (used ONLY to state their cited theorems verbatim; HibiLi/Cited/)

Hibi–Li (Math. Scand. 118 (2016), §1–2, and HLSS 2017 §1): "O(P) ... consists of those (a_1,...,a_d) such that
0 ≤ a_i ≤ 1 ... together with a_i ≥ a_j if x_i ≤ x_j"; "C(P) ... a_i ≥ 0 ... together with a_{i1}+...+a_{ik} ≤ 1 for
every maximal chain"; "P and Q are unimodularly equivalent if there exist a unimodular matrix U and an integral vector w
such that Q = f_U(P) + w, where f_U(v) = vU".  The paper's footnote (lines 181–183) says `v ↦ 1 − v` identifies the two
order polytopes; we PROVE that, rather than assume it. -/

/-- Hibi–Li's order polytope: `0 ≤ a_i ≤ 1`, and `a_i ≥ a_j` whenever `x_i ≤ x_j`. -/
def orderPolytopeHL : Set (P → ℝ) :=
  {v | (∀ p, 0 ≤ v p ∧ v p ≤ 1) ∧ ∀ p q, p ≤ q → v q ≤ v p}

/-- Hibi–Li's chain polytope: `a_i ≥ 0`, and the sum over every MAXIMAL chain is at most 1. -/
def chainPolytopeHL : Set (P → ℝ) :=
  {x | (∀ p, 0 ≤ x p) ∧ ∀ K : Finset P, IsMaxChain (· ≤ ·) (K : Set P) → ∑ p ∈ K, x p ≤ 1}

/-- Hibi–Li's unimodular equivalence: `Q' = f_U(Q) + w` with `f_U(v) = vU` (row vector times matrix). -/
def UnimodEquivHL {ι : Type*} [Fintype ι] [DecidableEq ι] (Q Q' : Set (ι → ℝ)) : Prop :=
  ∃ U : Matrix ι ι ℤ, (U.det = 1 ∨ U.det = -1) ∧ ∃ w : ι → ℤ,
    Q' = (fun v => Matrix.vecMul v (U.map (Int.cast : ℤ → ℝ)) + (fun i => (w i : ℝ))) '' Q

end HibiLi
