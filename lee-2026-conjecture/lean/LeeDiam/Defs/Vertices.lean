/-
LeeDiam/Defs/Vertices.lean — the vertices of O(P) and C(P) named by ideals and antichains, and the distances d_O, d_C
(paper 004, short v1.50 l. 50 and l. 139: "We identify each vertex of O(P) with the corresponding ideal and each vertex
of C(P) with the corresponding antichain").
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

TRUST SURFACE: `oVtx I`, `cVtx A` are the indicator vectors of an ideal / antichain as vertices of the graphs (the two
lemmas below PROVE that they are vertices, so no statement about them is empty); `dO`, `dC` are graph distances
(`⊤` when there is no path).
-/
import LeeDiam.Defs.Basic
import LeeDiam.Vendor.HibiLi.Example21.VertexBijection

namespace LeeDiam

variable {P : Type} [Fintype P] [PartialOrder P]

omit [Fintype P] in
/-- Points of the paper's `O(P)` lie in the cube. -/
theorem orderPolytope_cube {x : P → ℝ} (hx : x ∈ orderPolytope P) (p : P) : 0 ≤ x p ∧ x p ≤ 1 := hx.1 p

omit [Fintype P] in
/-- Points of `C(P)` lie in the cube (each `{p}` is a chain). -/
theorem chainPolytope_cube {x : P → ℝ} (hx : x ∈ chainPolytope P) (p : P) : 0 ≤ x p ∧ x p ≤ 1 := by
  refine ⟨hx.1 p, ?_⟩
  have h := hx.2 {p} (by simp [HibiLi.IsChainSet])
  simpa using h

/-- The indicator vector of an ideal is a vertex of the paper's `O(P)` (Stanley; PROVED here). -/
theorem isFace_ideal (I : Set P) (hI : IsIdeal I) :
    HibiLi.IsFace (orderPolytope P) {HibiLi.setVector I} := by
  classical
  refine HibiLi.zeroOne_isFace_singleton (fun w hw => orderPolytope_cube hw) ?_ (HibiLi.setVector_zeroOne I)
  refine ⟨fun p => ?_, fun p q hpq => ?_⟩
  · by_cases hp : p ∈ I <;> simp [HibiLi.setVector, hp]
  · by_cases hq : q ∈ I
    · have hp : p ∈ I := hI hpq hq
      simp [HibiLi.setVector, hp, hq]
    · by_cases hp : p ∈ I <;> simp [HibiLi.setVector, hp, hq]

/-- The indicator vector of an antichain is a vertex of `C(P)` (Stanley; PROVED here). -/
theorem isFace_antichain (A : Set P) (hA : IsAntichainSet A) :
    HibiLi.IsFace (chainPolytope P) {HibiLi.setVector A} :=
  HibiLi.zeroOne_isFace_singleton (fun _ hw => chainPolytope_cube hw) (HibiLi.setVector_antichain_mem hA)
    (HibiLi.setVector_zeroOne A)

/-- The vertex of `O(P)` of an ideal `I`. -/
noncomputable def oVtx (I : Set P) (hI : IsIdeal I) : {v : P → ℝ // HibiLi.IsFace (orderPolytope P) {v}} :=
  ⟨HibiLi.setVector I, isFace_ideal I hI⟩

/-- The vertex of `C(P)` of an antichain `A`. -/
noncomputable def cVtx (A : Set P) (hA : IsAntichainSet A) : {v : P → ℝ // HibiLi.IsFace (chainPolytope P) {v}} :=
  ⟨HibiLi.setVector A, isFace_antichain A hA⟩

/-- `d_O(I, J)`: the distance between two ideals in the graph of `O(P)`. -/
noncomputable def dO (I J : Set P) (hI : IsIdeal I) (hJ : IsIdeal J) : ℕ∞ :=
  (polyGraph (orderPolytope P)).edist (oVtx I hI) (oVtx J hJ)

/-- `d_C(A, B)`: the distance between two antichains in the graph of `C(P)`. -/
noncomputable def dC (A B : Set P) (hA : IsAntichainSet A) (hB : IsAntichainSet B) : ℕ∞ :=
  (polyGraph (chainPolytope P)).edist (cVtx A hA) (cVtx B hB)

end LeeDiam
