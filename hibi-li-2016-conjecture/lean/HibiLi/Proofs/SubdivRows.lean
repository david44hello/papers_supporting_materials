/-
HibiLi/Proofs/SubdivRows.lean — proof steps of Section 3.2 (l. 371-394): review 006 coverage item B10, rows g, h, i.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

g: Lemma 3.6 (cover) with `E = B`, and the characterization of the maximal cells. h: `A_ℓ ∩ A_ℓ'` is exposed in
`A_ℓ` by `ℓ' − ℓ`, which is `≤ 0` on `A_ℓ` because `L` is the maximum of the branches (for `U`, the minimum).
i: `IsFace.inter_decomposition` for the polytopes `A ∈ S`, `D ∈ T`.
-/
import HibiLi.Polytope.RefinementSubdivision
import HibiLi.Proofs.V060Claims
import HibiLi.Proofs.RoundJClaims
import HibiLi.Proofs.LU
import HibiLi.Proofs.Lemma36

namespace HibiLi.Proofs

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

/-- B10 g, l. 371-373: a full-dimensional convex `D ⊆ B` on which `L` (resp. `U`) is affine lies in a
full-dimensional affinity domain `A_ℓ` (resp. of `U`). -/
theorem sec3_affine_in_domain :
    (∀ D ⊆ s.B, Convex ℝ D → adim D = Fintype.card s.P' → AffineOn s.L D →
      ∃ K ∈ s.lowBranches, adim (s.domL K) = Fintype.card s.P' ∧ D ⊆ s.domL K) ∧
    (∀ D ⊆ s.B, Convex ℝ D → adim D = Fintype.card s.P' → AffineOn s.U D →
      ∃ j ∈ s.upBranches, adim (s.domU j) = Fintype.card s.P' ∧ D ⊆ s.domU j) := by
  have hB : adim s.B = Fintype.card s.P' := chainOrderPolytope_adim _ _
  have hBface : IsFace s.B s.B := IsFace.refl (B_nonempty s)
  constructor
  · intro D hDB hDc hDdim hL
    obtain ⟨C, ⟨⟨-, A, hA, rfl⟩, hCdim⟩, hDC⟩ :=
      (lemma_3_6_cover_proved s s.B hBface D hDB hDc (hDdim.trans hB.symm)).1 hL
    have hAB : A ⊆ s.B := by
      obtain ⟨K, -, -, hface⟩ := hA
      exact hface.subset.trans fun u hu => hu.1
    rw [Set.inter_eq_left.2 hAB] at hCdim hDC
    have hmax := sec3_maximal_cells_full_proved s A
    obtain ⟨K, hK, hKdim, hAeq⟩ := hmax.1.1 (hmax.2.1.2 ⟨hA, hCdim.trans hB⟩)
    exact ⟨K, hK, hKdim, hAeq ▸ hDC⟩
  · intro D hDB hDc hDdim hU
    obtain ⟨C, ⟨⟨-, A, hA, rfl⟩, hCdim⟩, hDC⟩ :=
      (lemma_3_6_cover_proved s s.B hBface D hDB hDc (hDdim.trans hB.symm)).2 hU
    have hAB : A ⊆ s.B := by
      obtain ⟨j, -, -, hface⟩ := hA
      exact hface.subset.trans fun u hu => hu.1
    rw [Set.inter_eq_left.2 hAB] at hCdim hDC
    have hmax := sec3_maximal_cells_full_proved s A
    obtain ⟨j, hj, hjdim, hAeq⟩ := hmax.2.2.1.1 (hmax.2.2.2.2 ⟨hA, hCdim.trans hB⟩)
    exact ⟨j, hj, hjdim, hAeq ▸ hDC⟩

/-- The linear part of an upper branch: `0` for the constant `1`, the coordinate `u_r` for `r`. -/
noncomputable def upLin : Option s.P' → (s.P' → ℝ) →L[ℝ] ℝ
  | none => 0
  | some r => ContinuousLinearMap.proj r

theorem upVal_eq_upLin (j : Option s.P') : ∃ c : ℝ, ∀ u, s.upVal j u = upLin s j u + c := by
  cases j with
  | none => exact ⟨1, fun u => by simp [Switch.upVal, upLin]⟩
  | some r => exact ⟨0, fun u => by simp [Switch.upVal, upLin]⟩

/-- B10 h, l. 386-387: two affinity domains of `L` that meet intersect in `A_ℓ ∩ {ℓ = ℓ'}`, a face of `A_ℓ`; the same
for `U`. -/
theorem sec3_domain_inter_face :
    (∀ K ∈ s.lowBranches, ∀ K' ∈ s.lowBranches, (s.domL K ∩ s.domL K').Nonempty →
      s.domL K ∩ s.domL K' = {u ∈ s.domL K | s.chainSum K u = s.chainSum K' u} ∧
        IsFace (s.domL K) (s.domL K ∩ s.domL K')) ∧
    (∀ j ∈ s.upBranches, ∀ j' ∈ s.upBranches, (s.domU j ∩ s.domU j').Nonempty →
      s.domU j ∩ s.domU j' = {u ∈ s.domU j | s.upVal j u = s.upVal j' u} ∧
        IsFace (s.domU j) (s.domU j ∩ s.domU j')) := by
  constructor
  · intro K hK K' hK' hne
    have heq : s.domL K ∩ s.domL K' = {u ∈ s.domL K | s.chainSum K u = s.chainSum K' u} := by
      ext u
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.2.symm.trans h2.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.1, h1.2.trans h2⟩
    refine ⟨heq, hne, fun _ => ?_⟩
    let l : (s.P' → ℝ) →L[ℝ] ℝ :=
      ∑ p ∈ K', ContinuousLinearMap.proj p - ∑ p ∈ K, ContinuousLinearMap.proj p
    have hl : ∀ u, l u = s.chainSum K' u - s.chainSum K u := fun u => by simp [l, Switch.chainSum]
    refine ⟨l, ?_⟩
    ext x
    constructor
    · rintro ⟨hxK, hxK'⟩
      refine ⟨hxK, fun y hy => ?_⟩
      rw [hl, hl]
      have h1 := chainSum_le_L s hK' y
      have h2 := hy.2
      have h3 := hxK.2
      have h4 := hxK'.2
      linarith
    · rintro ⟨hxK, hmax⟩
      obtain ⟨y, hyK, hyK'⟩ := hne
      have h1 := hmax y hyK
      rw [hl, hl] at h1
      have h2 := chainSum_le_L s hK' x
      have h3 := hyK.2
      have h4 := hyK'.2
      have h5 := hxK.2
      exact ⟨hxK, hxK.1, by linarith⟩
  · intro j hj j' hj' hne
    have heq : s.domU j ∩ s.domU j' = {u ∈ s.domU j | s.upVal j u = s.upVal j' u} := by
      ext u
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.2.symm.trans h2.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.1, h1.2.trans h2⟩
    refine ⟨heq, hne, fun _ => ?_⟩
    obtain ⟨c, hc⟩ := upVal_eq_upLin s j
    obtain ⟨c', hc'⟩ := upVal_eq_upLin s j'
    let l : (s.P' → ℝ) →L[ℝ] ℝ := upLin s j - upLin s j'
    have hl : ∀ u, l u = (s.upVal j u - c) - (s.upVal j' u - c') := fun u => by
      rw [hc u, hc' u]
      simp [l]
    refine ⟨l, ?_⟩
    ext x
    constructor
    · rintro ⟨hxj, hxj'⟩
      refine ⟨hxj, fun y hy => ?_⟩
      rw [hl, hl]
      have h1 := U_le_upVal s hj' y
      have h2 := hy.2
      have h3 := hxj.2
      have h4 := hxj'.2
      linarith
    · rintro ⟨hxj, hmax⟩
      obtain ⟨y, hyj, hyj'⟩ := hne
      have h1 := hmax y hyj
      rw [hl, hl] at h1
      have h2 := U_le_upVal s hj' x
      have h3 := hyj.2
      have h4 := hyj'.2
      have h5 := hxj.2
      exact ⟨hxj, hxj.1, by linarith⟩

/-- B10 i, l. 390-392: a face of a cell `S ∩ T` of `R` is `S₀ ∩ T₀`, with `S₀`, `T₀` faces of `S`, `T`. -/
theorem sec3_R_cell_faces :
    ∀ A ∈ s.cellsS, ∀ D ∈ s.cellsT, ∀ F, IsFace (A ∩ D) F → ∃ A₀ D₀, IsFace A A₀ ∧ IsFace D D₀ ∧ F = A₀ ∩ D₀ :=
  fun _ hA _ hD _ hF => hF.inter_decomposition (s.cellsS_isPolytope hA) (s.cellsT_isPolytope hD)
    (s.cellsS_halfspaces hA) (s.cellsT_halfspaces hD)

end HibiLi.Proofs
