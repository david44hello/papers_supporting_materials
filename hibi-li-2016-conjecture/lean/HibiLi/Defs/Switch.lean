/-
HibiLi/Defs/Switch.lean — one switch of Fourier: base polytope B, the functions L and U, the subdivisions S, T, R,
restrictions to faces, carriers, the local terms σ τ ρ δ, and transversality.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Poset

namespace HibiLi

open Finset Polynomial

/-- The data of one switch (paper lines 306–308; "so that I ∪ {q} is again an order ideal" is
`sec3_insert_isLowerSet`): an order ideal `I` and an element `q` minimal in `J = P \ I`
("minimal in J" = every element below `q` lies in `I`). -/
structure Switch (P : Type*) [Fintype P] [PartialOrder P] where
  I : Set P
  isLowerSet : IsLowerSet I
  q : P
  q_notMem : q ∉ I
  q_minimal : ∀ p, p < q → p ∈ I

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- `P' = P \ {q}` with the induced order. -/
abbrev P' := {p : P // p ≠ s.q}

noncomputable instance : Fintype s.P' := by classical exact inferInstance

/-- The ideal `I` seen inside `P'`. -/
def I' : Set s.P' := {p | p.1 ∈ s.I}

/-- The base polytope `B = O_I(P')` (paper line 309). -/
def B : Set (s.P' → ℝ) := chainOrderPolytope s.P' s.I'

/-- The chains `K ⊆ I` with `p < q` for all `p ∈ K` (the empty chain included) — the branches of `L`. -/
noncomputable def lowBranches : Finset (Finset s.P') := by
  classical exact univ.filter (fun K => (↑K ⊆ s.I') ∧ IsChainSet s.P' K ∧ ∀ p ∈ K, p.1 < s.q)

lemma lowBranches_nonempty : s.lowBranches.Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [lowBranches, IsChainSet]

/-- The chain sum `ℓ_K(u) = Σ_{p∈K} u_p`. -/
def chainSum (K : Finset s.P') (u : s.P' → ℝ) : ℝ := ∑ p ∈ K, u p

/-- `L(u) = max{Σ_{p∈K} u_p : K ⊆ I a chain with p < q for all p ∈ K}` (paper line 312). -/
noncomputable def L (u : s.P' → ℝ) : ℝ := s.lowBranches.sup' s.lowBranches_nonempty (fun K => s.chainSum K u)

/-- The branches of `U`: `none` is the constant `1`, `some r` (with `r > q`) is the coordinate `u_r`. -/
noncomputable def upBranches : Finset (Option s.P') := by
  classical exact insert none ((univ.filter (fun r : s.P' => s.q < r.1)).image some)

lemma upBranches_nonempty : s.upBranches.Nonempty := by
  classical exact ⟨none, by simp [upBranches]⟩

/-- Value of an upper branch. -/
def upVal : Option s.P' → (s.P' → ℝ) → ℝ
  | none, _ => 1
  | some r, u => u r

/-- `U(u) = min({u_r : r > q} ∪ {1})` (paper line 314). -/
noncomputable def U (u : s.P' → ℝ) : ℝ := s.upBranches.inf' s.upBranches_nonempty (fun j => s.upVal j u)

/-- Affinity domain of the branch `K` of `L`: `A_ℓ = {u ∈ B : L(u) = ℓ_K(u)}` (paper line 369). -/
def domL (K : Finset s.P') : Set (s.P' → ℝ) := {u | u ∈ s.B ∧ s.L u = s.chainSum K u}

/-- Affinity domain of the branch `j` of `U`. -/
def domU (j : Option s.P') : Set (s.P' → ℝ) := {u | u ∈ s.B ∧ s.U u = s.upVal j u}

/-- Cells of `S` (paper lines 357–380): all nonempty faces of the full-dimensional affinity domains of `L`. -/
def cellsS : Set (Set (s.P' → ℝ)) :=
  {C | ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ IsFace (s.domL K) C}

/-- Cells of `T`: all nonempty faces of the full-dimensional affinity domains of `U`. -/
def cellsT : Set (Set (s.P' → ℝ)) :=
  {C | ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ IsFace (s.domU j) C}

/-- Cells of the common refinement `R = S ∨ T` (paper lines 383–385): the nonempty intersections `S ∩ T`. -/
def cellsR : Set (Set (s.P' → ℝ)) :=
  {C | C.Nonempty ∧ ∃ A ∈ s.cellsS, ∃ D ∈ s.cellsT, C = A ∩ D}

/-- Restriction of a family of cells to a face `E` (paper lines 397–403): the nonempty intersections with `E`. -/
def restrict (K : Set (Set (s.P' → ℝ))) (E : Set (s.P' → ℝ)) : Set (Set (s.P' → ℝ)) :=
  {C | C.Nonempty ∧ ∃ A ∈ K, C = A ∩ E}

/-- Number of `k`-cells of the family `K` whose carrier is `E` (paper lines 415–417: σ_E, τ_E, ρ_E). -/
noncomputable def carrierNum (K : Set (Set (s.P' → ℝ))) (E : Set (s.P' → ℝ)) (k : ℕ) : ℕ :=
  {C | C ∈ K ∧ adim C = k ∧ IsCarrier s.B E C}.ncard

/-- `δ_{E,k} = ρ_E(k) − σ_E(k) − τ_E(k) + 1_{k=e}` (paper line 419). -/
noncomputable def deltaCoeff (E : Set (s.P' → ℝ)) (k : ℕ) : ℤ :=
  (s.carrierNum s.cellsR E k : ℤ) - s.carrierNum s.cellsS E k - s.carrierNum s.cellsT E k +
    (if k = adim E then 1 else 0)

/-- `δ_E(t) = Σ_k δ_{E,k} t^k` (paper line 420); every cell lies in `B`, so `k ≤ card P'`. -/
noncomputable def delta (E : Set (s.P' → ℝ)) : ℤ[X] :=
  ∑ k ∈ range (Fintype.card s.P' + 1), C (s.deltaCoeff E k) * X ^ k

/-- Transversality relative to the faces of `B` (paper Definition 3.3, lines 443–448 = Fourier Definition 4.2): for
every face `E` of `B` and `x ∈ relint E` (the paper's `u`), the cells `A ∈ S|_E`, `D ∈ T|_E` whose relative interiors
contain `x` — unique on each side, by `def_3_3_unique_cells` — satisfy
`dim(A ∩ D) = dim A + dim D − dim E` (written with `+` on both sides to avoid truncated subtraction). -/
def Transverse : Prop :=
  ∀ E, IsFace s.B E → ∀ x ∈ intrinsicInterior ℝ E,
    ∀ A ∈ s.restrict s.cellsS E, ∀ D ∈ s.restrict s.cellsT E,
      x ∈ intrinsicInterior ℝ A → x ∈ intrinsicInterior ℝ D →
        adim (A ∩ D) + adim E = adim A + adim D

/-- `R(Y)` (paper Lemma 3.5): the cells of `R` of dimension `dim Y` contained in `Y`. -/
def RR (Y : Set (s.P' → ℝ)) : Set (Set (s.P' → ℝ)) :=
  {R | R ∈ s.cellsR ∧ R ⊆ Y ∧ adim R = adim Y}

/-- The `e`-cells (`e = dim E`) of the restriction `K|_E`. -/
def topCells (K : Set (Set (s.P' → ℝ))) (E : Set (s.P' → ℝ)) : Set (Set (s.P' → ℝ)) :=
  {A | A ∈ s.restrict K E ∧ adim A = adim E}

/-- Adjacency of the bipartite graph `G_E` (paper Lemma 3.5(ii)): an `e`-cell `A` of `S|_E` and an `e`-cell `D` of
`T|_E` are joined when `A ∩ D` is an `e`-cell of `R|_E`; cells of the same side are never joined. -/
def graphAdj (E : Set (s.P' → ℝ)) :
    (s.topCells s.cellsS E ⊕ s.topCells s.cellsT E) → (s.topCells s.cellsS E ⊕ s.topCells s.cellsT E) → Prop
  | .inl A, .inr D => A.1 ∩ D.1 ∈ s.topCells s.cellsR E
  | .inr D, .inl A => A.1 ∩ D.1 ∈ s.topCells s.cellsR E
  | _, _ => False

/-- The bipartite graph `G_E` of paper Lemma 3.5(ii). -/
def graphG (E : Set (s.P' → ℝ)) : SimpleGraph (s.topCells s.cellsS E ⊕ s.topCells s.cellsT E) where
  Adj := s.graphAdj E
  symm := ⟨fun x y hxy => by cases x <;> cases y <;> simp_all [graphAdj]⟩
  loopless := ⟨fun x hx => by cases x <;> simp_all [graphAdj]⟩

end Switch

end HibiLi
