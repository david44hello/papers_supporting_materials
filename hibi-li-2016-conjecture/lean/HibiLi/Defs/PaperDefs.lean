/-
HibiLi/Defs/PaperDefs.lean — auxiliary definitions used to STATE the paper's claims (Section 4 data, crossing hypotheses).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Examples
import HibiLi.Defs.Switch

namespace HibiLi

open Polynomial

/-- The gap polynomial `t^2 (1+t)^{n-3}` of Theorem 4.1. -/
noncomputable def gapPoly (n : ℕ) : ℤ[X] := X ^ 2 * (1 + X) ^ (n - 3)

/-- `f` agrees with an affine function on `D`. -/
def AffineOn {ι : Type*} (f : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) : Prop :=
  ∃ g : (ι → ℝ) →ᵃ[ℝ] ℝ, ∀ u ∈ D, f u = g u

/-- The five elements of a copy of `X` (paper Section 4.2). -/
def IsXCopy {P : Type*} [PartialOrder P] (a b c g h : P) : Prop :=
  a < c ∧ b < c ∧ c < g ∧ c < h ∧ ¬ a ≤ b ∧ ¬ b ≤ a ∧ ¬ g ≤ h ∧ ¬ h ≤ g

/-- The hypotheses of Lemma 4.2 at a point `w` of a face `E` of `B`: a convex neighbourhood `N` of `w` in `E` meets
exactly two `e`-cells `S₁, S₂` of `S|_E`, which cut `N` along the hyperplane `φ = φ w`; the same for `T₁, T₂` and `ψ`;
and `φ, ψ` restricted to `dir(E)` (the direction of `aff(E)`) are linearly independent — the v0.41 wording of
Lemma 4.2.  The wording of v0.60 to v2.10 (v2.10 lines 585–588: `H_S`, `H_T` hyperplanes of `aff(E)` through `w`,
`H_S ≠ H_T`) is equivalent: `crossingAt_iff_v060`.  For `N`, "a convex neighborhood `N` of `w` in `E`" is the v1.80
wording; v2.10 (lines 582–583) takes "some convex set `N ⊆ E`, open in `aff(E)` and containing `w`", which is such a
neighbourhood (`Paper.lemma_4_2_v190`). -/
def CrossingAt {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) (E : Set (s.P' → ℝ)) (w : s.P' → ℝ) :
    Prop :=
  w ∈ intrinsicInterior ℝ E ∧
  ∃ N : Set (s.P' → ℝ), Convex ℝ N ∧ N ⊆ E ∧ N ∈ nhdsWithin w E ∧
  ∃ (S₁ S₂ T₁ T₂ : Set (s.P' → ℝ)) (φ ψ : (s.P' → ℝ) →ₗ[ℝ] ℝ),
    S₁ ∈ s.topCells s.cellsS E ∧ S₂ ∈ s.topCells s.cellsS E ∧
    T₁ ∈ s.topCells s.cellsT E ∧ T₂ ∈ s.topCells s.cellsT E ∧
    (∀ A ∈ s.topCells s.cellsS E, (A ∩ N).Nonempty → A = S₁ ∨ A = S₂) ∧
    (∀ D ∈ s.topCells s.cellsT E, (D ∩ N).Nonempty → D = T₁ ∨ D = T₂) ∧
    S₁ ∩ N = {u ∈ N | φ w ≤ φ u} ∧ S₂ ∩ N = {u ∈ N | φ u ≤ φ w} ∧
    T₁ ∩ N = {u ∈ N | ψ w ≤ ψ u} ∧ T₂ ∩ N = {u ∈ N | ψ u ≤ ψ w} ∧
    LinearIndependent ℝ ![φ.domRestrict (vectorSpan ℝ E), ψ.domRestrict (vectorSpan ℝ E)]

/-- The data of Section 4.2: a copy of `X`, the element `q`, and its two incomparable upper covers `g', h'`. -/
structure XSwitch (P : Type*) [Fintype P] [PartialOrder P] where
  a : P
  b : P
  c : P
  g : P
  h : P
  isX : IsXCopy a b c g h
  q : P
  c_le_q : c ≤ q
  q_not_chain : ¬ IsChain (· ≤ ·) (Set.Ioi q)
  q_max : ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)
  g' : P
  h' : P
  q_covby_g' : q ⋖ g'
  q_covby_h' : q ⋖ h'
  g'_ne_h' : g' ≠ h'
  g'_h'_incomp : ¬ g' ≤ h' ∧ ¬ h' ≤ g'

namespace XSwitch

variable {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P)

/-- The switch of `q` with `I = P \ ↑q` (paper lines 706–710). -/
def toSwitch : Switch P where
  I := (Set.Ici x.q)ᶜ
  isLowerSet := fun _ _ hle hb ha => hb (le_trans ha hle)
  q := x.q
  q_notMem := fun h => h le_rfl
  q_minimal := fun _ hp hge => absurd (lt_of_lt_of_le hp hge) (lt_irrefl _)

/-- The face `E₀` (paper lines 713–715): chain coordinates other than `a, b` are 0; order coordinates other than
`g', h'` are 1. -/
def E0 : Set (x.toSwitch.P' → ℝ) :=
  {u | u ∈ x.toSwitch.B ∧
    (∀ p : x.toSwitch.P', p.1 ∈ x.toSwitch.I → p.1 ≠ x.a → p.1 ≠ x.b → u p = 0) ∧
    (∀ r : x.toSwitch.P', r.1 ∉ x.toSwitch.I → r.1 ≠ x.g' → r.1 ≠ x.h' → u r = 1)}

lemma a_lt_q : x.a < x.q := lt_of_lt_of_le x.isX.1 x.c_le_q
lemma b_lt_q : x.b < x.q := lt_of_lt_of_le x.isX.2.1 x.c_le_q

/-- The coordinate `α = x_a` of `B` (paper line 710). -/
def pa : x.toSwitch.P' := ⟨x.a, x.a_lt_q.ne⟩
/-- The coordinate `β = x_b`. -/
def pb : x.toSwitch.P' := ⟨x.b, x.b_lt_q.ne⟩
/-- The coordinate `γ = y_{g'}`. -/
def pg : x.toSwitch.P' := ⟨x.g', x.q_covby_g'.lt.ne'⟩
/-- The coordinate `η = y_{h'}`. -/
def ph : x.toSwitch.P' := ⟨x.h', x.q_covby_h'.lt.ne'⟩

/-- The four retained coordinates `α, β, γ, η`; the others form `ζ`. -/
def special : Set x.toSwitch.P' := {x.pa, x.pb, x.pg, x.ph}

/-- The point `u₀` (paper lines 736–737): `(α,β,γ,η) = (1/4,1/4,3/4,3/4)` and `ζ = ζ₀` (chain coordinates 0,
order coordinates 1). -/
noncomputable def u0 : x.toSwitch.P' → ℝ := by
  classical
  exact fun p => if p = x.pa ∨ p = x.pb then 1 / 4 else if p = x.pg ∨ p = x.ph then 3 / 4
    else if p.1 ∈ x.toSwitch.I then 0 else 1

/-- The `ζ`-part of a point of `B`'s ambient space. -/
def zeta (u : x.toSwitch.P' → ℝ) : {p // p ∉ x.special} → ℝ := fun p => u p.1

/-- The `(α, β, γ, η)`-part of a point. -/
def alphaPart (u : x.toSwitch.P' → ℝ) : Fin 4 → ℝ := ![u x.pa, u x.pb, u x.pg, u x.ph]

lemma singleton_pa_mem : ({x.pa} : Finset x.toSwitch.P') ∈ x.toSwitch.lowBranches := by
  classical
  simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton,
    Set.singleton_subset_iff, Finset.mem_singleton, forall_eq]
  refine ⟨fun h => absurd (lt_of_le_of_lt h x.a_lt_q) (lt_irrefl _), ?_, x.a_lt_q⟩
  simp [IsChainSet]

lemma singleton_pb_mem : ({x.pb} : Finset x.toSwitch.P') ∈ x.toSwitch.lowBranches := by
  classical
  simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton,
    Set.singleton_subset_iff, Finset.mem_singleton, forall_eq]
  refine ⟨fun h => absurd (lt_of_le_of_lt h x.b_lt_q) (lt_irrefl _), ?_, x.b_lt_q⟩
  simp [IsChainSet]

/-- `λ_a` (paper lines 738–742): the maximum of the forms `Σ_{p∈K∖{a}} x_p` over chains `K ∋ a` in the definition
of `L` (the `a`-family). -/
noncomputable def lamA (u : x.toSwitch.P' → ℝ) : ℝ := by
  classical
  exact (x.toSwitch.lowBranches.filter (fun K => x.pa ∈ K)).sup'
    ⟨{x.pa}, Finset.mem_filter.mpr ⟨x.singleton_pa_mem, Finset.mem_singleton_self _⟩⟩
    (fun K => x.toSwitch.chainSum (K.erase x.pa) u)

/-- `λ_b`: the same for the `b`-family. -/
noncomputable def lamB (u : x.toSwitch.P' → ℝ) : ℝ := by
  classical
  exact (x.toSwitch.lowBranches.filter (fun K => x.pb ∈ K)).sup'
    ⟨{x.pb}, Finset.mem_filter.mpr ⟨x.singleton_pb_mem, Finset.mem_singleton_self _⟩⟩
    (fun K => x.toSwitch.chainSum (K.erase x.pb) u)

/-- The product neighbourhood `N₀ = V₄ × V_ζ` (paper Lemma 4.5). -/
def N0 (V4 : Set (Fin 4 → ℝ)) (Vz : Set ({p // p ∉ x.special} → ℝ)) : Set (x.toSwitch.P' → ℝ) :=
  {u | x.alphaPart u ∈ V4 ∧ x.zeta u ∈ Vz}

end XSwitch

end HibiLi
