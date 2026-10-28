/-
HibiLi/Polytope/CJKProof.lean — [CJK, Lemma 2] PROVED: the dual graph of a polytopal subdivision of a full-dimensional polytope is
connected, with exactly the type of the cited statement `HibiLi.Cited.cjk_dual_connected`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper route (v2.10 l. 494-505, Lemma 3.5(ii), "We recall the argument"): fix `x` in the relative interior of one
top-dimensional cell; choose `y` in the relative interior of another, off the finitely many proper affine subspaces
`aff({x} ∪ C)` (`C` a cell of dimension at most `e - 2`, or an `(e-1)`-cell with `x ∈ aff(C)`), possible because that
relative interior is a nonempty open subset of `aff(E)`; then the segment `[x, y]` meets no cell of dimension at most
`e - 2`, crosses the `(e-1)`-cells at finitely many exceptional points, and consecutive top cells along it share an
`(e-1)`-face.

Lean route (same idea; two steps differ, both simplifications):
* Genericity, as in the paper: `x` is chosen in the interior of the first maximal cell off the affine spans of the
  cells of dimension at most `e - 2` (the paper takes `x` in a relative interior and uses the relative-interior
  partition for the same conclusion), and `y` in the interior of the second maximal cell off the spans
  `aff({x} ∪ C)` of those cells (`exists_mem_open_forall_not_mem`: a nonempty open set is not covered by finitely
  many affine subspaces other than the whole space).  Then `[x, y]` meets no cell of dimension at most `e - 2`.
* Instead of the exceptional points, Lean uses that the segment is connected: the maximal cells reachable from the
  first cell in the dual graph and the other maximal cells give two closed sets covering `[x, y]`; if the second cell
  were not reachable, both would be met, so some point `z` of the segment lies in a reachable maximal cell `M` and an
  unreachable one `M'`.  `M ∩ M'` is a common face (subdivision property), a cell, proper in `M` (maximality), so of
  dimension at most `e - 1`, and at least `e - 1` because it contains `z`; so `M`, `M'` are adjacent, a contradiction.
  The `(e-1)`-cells with `x ∈ aff(C)` and the finiteness of the exceptional points are therefore not needed.
* Maximal cells have dimension `e = dim base` (`subdivision_max_adim`); here `e` is the ambient dimension, as the base
  spans the space (lower-dimensional bases are handled by the transport theorem that uses this result).
-/
import HibiLi.Polytope.SubdivisionPurity
import HibiLi.Polytope.TopCells

namespace HibiLi.CJKProof

open Set

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An affine subspace other than the whole space has empty interior. -/
theorem interior_affineSubspace_eq_empty {A : AffineSubspace ℝ E} (hA : A ≠ ⊤) : interior (A : Set E) = ∅ := by
  by_contra hne
  apply hA
  have h := (Convex.interior_nonempty_iff_affineSpan_eq_top A.convex).1 (Set.nonempty_iff_ne_empty.2 hne)
  simpa using h

/-- A nonempty open set is not covered by finitely many affine subspaces other than the whole space (v2.10 l. 498:
"possible, as that relative interior is a nonempty open subset"). -/
theorem exists_mem_open_forall_not_mem {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (S : Finset (AffineSubspace ℝ E)) (hS : ∀ A ∈ S, A ≠ ⊤) : ∃ u ∈ U, ∀ A ∈ S, u ∉ A := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdense : Dense (⋂ A ∈ (S : Set (AffineSubspace ℝ E)), ((A : Set E))ᶜ) :=
    dense_biInter_of_isOpen (fun A _ => (A.closed_of_finiteDimensional).isOpen_compl) S.countable_toSet
      fun A hA => interior_eq_empty_iff_dense_compl.1 (interior_affineSubspace_eq_empty (hS A hA))
  obtain ⟨u, huU, hu⟩ := hdense.inter_open_nonempty U hU hne
  rw [Set.mem_iInter₂] at hu
  exact ⟨u, huU, fun A hA hmem => hu A hA hmem⟩

omit [FiniteDimensional ℝ E] in
/-- A set of dimension below the ambient dimension spans an affine subspace other than the whole space. -/
theorem affineSpan_ne_top_of_adim_lt {S : Set E} (h : adim S < Module.finrank ℝ E) : affineSpan ℝ S ≠ ⊤ := by
  intro htop
  have hv : vectorSpan ℝ S = ⊤ := by rw [← direction_affineSpan, htop, AffineSubspace.direction_top]
  unfold adim at h
  rw [hv, finrank_top] at h
  exact lt_irrefl _ h

end Generic

/-- [CJK, Lemma 2] (v2.10 l. 494-505), with exactly the type of `HibiLi.Cited.cjk_dual_connected`: the dual graph of
a finite polytopal subdivision of a full-dimensional polytope is connected. -/
theorem cjk_dual_connected_proved {ι : Type*} [Fintype ι]
    (base : Set (ι → ℝ)) (cells : Finset (Set (ι → ℝ)))
    (polytope : HibiLi.IsPolytope base) (nonempty : base.Nonempty)
    (spans : affineSpan ℝ base = ⊤)
    (subdivision : HibiLi.IsFinitePolytopalSubdivision base cells) :
    (HibiLi.subdivisionDualGraph cells).Connected := by
  classical
  -- maximal cells have the dimension of the base
  have hmax : ∀ M : MaxSubdivisionCell cells, adim M.1 = adim base :=
    fun M => subdivision_max_adim polytope nonempty subdivision M
  obtain ⟨cell_props, union_eq, face_closed, meets⟩ := subdivision
  -- the base spans the space, so its dimension is the ambient dimension
  have hamb : Module.finrank ℝ (ι → ℝ) = adim base := by
    have hv : vectorSpan ℝ base = ⊤ := by
      rw [← direction_affineSpan, spans, AffineSubspace.direction_top]
    unfold adim
    rw [hv, finrank_top]
  have hsub : ∀ M : MaxSubdivisionCell cells, M.1 ⊆ base := fun M =>
    union_eq ▸ Set.subset_sUnion_of_mem M.2.1
  -- every point of the base lies in a maximal cell
  have hcover : ∀ z ∈ base, ∃ M : MaxSubdivisionCell cells, z ∈ M.1 := by
    intro z hz
    rw [← union_eq, Set.mem_sUnion] at hz
    obtain ⟨C, hC, hzC⟩ := hz
    obtain ⟨M, hCM, hM⟩ := cells.exists_le_maximal (Finset.mem_coe.1 hC)
    exact ⟨⟨M, hM.1, fun other hother hle => (hM.2 hother hle).antisymm hle⟩, hCM hzC⟩
  -- maximal cells have nonempty interior
  have hint : ∀ M : MaxSubdivisionCell cells, (interior M.1).Nonempty := by
    intro M
    have hp := cell_props M.1 M.2.1
    refine (Convex.interior_nonempty_iff_affineSpan_eq_top hp.1.convex).2 ?_
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty (k := ℝ) (V := ι → ℝ)
      (P := ι → ℝ) hp.2]
    apply Submodule.eq_top_of_finrank_eq
    rw [hamb]
    exact hmax M
  -- the cells of dimension at most `e - 2`, and the proper affine subspaces they give
  let low : Finset (Set (ι → ℝ)) := cells.filter fun C => adim C + 2 ≤ adim base
  have hlow_span : ∀ C ∈ low, affineSpan ℝ C ≠ ⊤ := fun C hC =>
    affineSpan_ne_top_of_adim_lt (by have := (Finset.mem_filter.1 hC).2; omega)
  have hlow_insert : ∀ C ∈ low, ∀ x : ι → ℝ, affineSpan ℝ (insert x C) ≠ ⊤ := by
    intro C hC x
    have hC' := (Finset.mem_filter.1 hC).2
    apply affineSpan_ne_top_of_adim_lt
    rw [hamb]
    have := finrank_vectorSpan_insert_le_set (k := ℝ) C x
    unfold adim at hC' ⊢
    omega
  -- a segment between two maximal cells that meets no cell of dimension at most `e - 2`
  have hgen : ∀ C₀ C₁ : MaxSubdivisionCell cells, ∃ x ∈ C₀.1, ∃ y ∈ C₁.1,
      ∀ C ∈ low, ∀ p ∈ segment ℝ x y, p ∉ C := by
    intro C₀ C₁
    obtain ⟨x, hx, hxS⟩ := exists_mem_open_forall_not_mem isOpen_interior (hint C₀)
      (low.image fun C => affineSpan ℝ C) (by
        intro A hA
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hA
        exact hlow_span C hC)
    obtain ⟨y, hy, hyS⟩ := exists_mem_open_forall_not_mem isOpen_interior (hint C₁)
      (low.image fun C => affineSpan ℝ (insert x C)) (by
        intro A hA
        obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hA
        exact hlow_insert C hC x)
    refine ⟨x, interior_subset hx, y, interior_subset hy, fun C hC p hp hpC => ?_⟩
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hp
    rcases eq_or_lt_of_le ht0 with h0 | hpos
    · -- `t = 0`: the point is `x`, which is off the span of every low cell
      rw [← h0, AffineMap.lineMap_apply_zero] at hpC
      exact hxS _ (Finset.mem_image_of_mem _ hC) (subset_affineSpan ℝ C hpC)
    · -- `t > 0`: then `y` is on the line through `x` and the point, inside `aff({x} ∪ C)`
      apply hyS _ (Finset.mem_image_of_mem _ hC)
      have hmem : AffineMap.lineMap x (AffineMap.lineMap x y t) t⁻¹ ∈ affineSpan ℝ (insert x C) :=
        AffineMap.lineMap_mem t⁻¹ (subset_affineSpan ℝ _ (Set.mem_insert x C))
          (subset_affineSpan ℝ _ (Set.mem_insert_of_mem x hpC))
      rwa [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hpos.ne', AffineMap.lineMap_apply_one] at hmem
  have : Finite (MaxSubdivisionCell cells) :=
    Finite.of_injective (fun M : MaxSubdivisionCell cells => (⟨M.1, M.2.1⟩ : cells)) fun M N h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext h
  -- the dual graph is preconnected: the segment argument
  have hpre : (subdivisionDualGraph cells).Preconnected := by
    intro C₀ C₁
    by_contra hnot
    obtain ⟨x, hx, y, hy, hseg⟩ := hgen C₀ C₁
    -- the maximal cells reachable from `C₀`, and the others: two closed sets covering the segment
    let A : Set (ι → ℝ) :=
      ⋃ M ∈ {M : MaxSubdivisionCell cells | (subdivisionDualGraph cells).Reachable C₀ M}, M.1
    let B : Set (ι → ℝ) :=
      ⋃ M ∈ {M : MaxSubdivisionCell cells | ¬ (subdivisionDualGraph cells).Reachable C₀ M}, M.1
    have hAc : IsClosed A :=
      (Set.toFinite _).isClosed_biUnion fun M _ => (cell_props M.1 M.2.1).1.isClosed
    have hBc : IsClosed B :=
      (Set.toFinite _).isClosed_biUnion fun M _ => (cell_props M.1 M.2.1).1.isClosed
    have hcov : segment ℝ x y ⊆ A ∪ B := by
      intro z hz
      obtain ⟨M, hzM⟩ := hcover z (polytope.convex.segment_subset (hsub C₀ hx) (hsub C₁ hy) hz)
      by_cases hM : (subdivisionDualGraph cells).Reachable C₀ M
      · exact Or.inl (Set.mem_biUnion hM hzM)
      · exact Or.inr (Set.mem_biUnion hM hzM)
    obtain ⟨z, hzseg, hzA, hzB⟩ := isPreconnected_closed_iff.1 (convex_segment x y).isPreconnected A B hAc hBc
      hcov ⟨x, left_mem_segment ℝ x y, Set.mem_biUnion (SimpleGraph.Reachable.refl C₀) hx⟩
      ⟨y, right_mem_segment ℝ x y, Set.mem_biUnion hnot hy⟩
    rw [Set.mem_iUnion₂] at hzA hzB
    obtain ⟨M, hM, hzM⟩ := hzA
    obtain ⟨M', hM', hzM'⟩ := hzB
    have hR : (subdivisionDualGraph cells).Reachable C₀ M := hM
    have hR' : ¬ (subdivisionDualGraph cells).Reachable C₀ M' := hM'
    have hne : M ≠ M' := fun h => hR' (h ▸ hR)
    have hMM : M.1 ≠ M'.1 := fun h => hne (Subtype.ext h)
    have hzMM : z ∈ M.1 ∩ M'.1 := ⟨hzM, hzM'⟩
    obtain ⟨hfaceM, hfaceM'⟩ := meets M.1 M.2.1 M'.1 M'.2.1 ⟨z, hzMM⟩
    -- `M ∩ M'` is a proper face of `M`, so of dimension below `e`
    have hsmall : adim (M.1 ∩ M'.1) < adim base := by
      have hle : adim (M.1 ∩ M'.1) ≤ adim M.1 :=
        Submodule.finrank_mono (vectorSpan_mono ℝ Set.inter_subset_left)
      have hneq : adim (M.1 ∩ M'.1) ≠ adim M.1 := fun h =>
        hMM (M.2.2 M'.1 M'.2.1 (Set.inter_eq_left.1 (hfaceM.eq_of_adim_eq h))).symm
      have := hmax M
      omega
    -- `M ∩ M'` is a cell through the point `z` of the segment, so of dimension at least `e - 1`
    have hbig : ¬ (adim (M.1 ∩ M'.1) + 2 ≤ adim base) := fun h =>
      hseg (M.1 ∩ M'.1) (Finset.mem_filter.2 ⟨face_closed M.1 M.2.1 _ hfaceM, h⟩) z hzseg hzMM
    have hadj : (subdivisionDualGraph cells).Adj M M' := by
      change M ≠ M' ∧ (M.1 ∩ M'.1).Nonempty ∧ IsFace M.1 (M.1 ∩ M'.1) ∧ IsFace M'.1 (M.1 ∩ M'.1) ∧
        adim (M.1 ∩ M'.1) + 1 = adim M.1 ∧ adim (M.1 ∩ M'.1) + 1 = adim M'.1
      exact ⟨hne, ⟨z, hzMM⟩, hfaceM, hfaceM', by rw [hmax M]; omega, by rw [hmax M']; omega⟩
    exact hR' (hR.trans hadj.reachable)
  obtain ⟨z, hz⟩ := nonempty
  obtain ⟨M, -⟩ := hcover z hz
  have : Nonempty (MaxSubdivisionCell cells) := ⟨M⟩
  exact ⟨hpre⟩

end HibiLi.CJKProof
