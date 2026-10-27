/-
HibiLi/Example21/DimensionCertificate.lean — finite affine-dimension certificates.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.FiniteHull

namespace HibiLi.Example21

theorem matrix_rank_certificate {R : Type*} [Field R] {rows cols : Type*}
    [Fintype rows] [Fintype cols] {rr : ℕ} (mat : Matrix rows cols R)
    (pivot : Fin rr → cols) (dual : Matrix (Fin rr) rows R)
    (coeff : Matrix (Fin rr) cols R)
    (hleft : dual * mat.submatrix id pivot = 1)
    (hfactor : mat = mat.submatrix id pivot * coeff) : mat.rank = rr := by
  apply Nat.le_antisymm
  · calc
      mat.rank = (mat.submatrix id pivot * coeff).rank := congrArg Matrix.rank hfactor
      _ ≤ (mat.submatrix id pivot).rank := Matrix.rank_mul_le_left _ _
      _ ≤ rr := by simpa using Matrix.rank_le_card_width (mat.submatrix id pivot)
  · calc
      rr = (1 : Matrix (Fin rr) (Fin rr) R).rank := by simp
      _ = (dual * mat.submatrix id pivot).rank := congrArg Matrix.rank hleft.symm
      _ ≤ (mat.submatrix id pivot).rank := Matrix.rank_mul_le_right _ _
      _ ≤ mat.rank := Matrix.rank_submatrix_le mat id pivot

def differenceMatrix {rows cols : Type*} [DecidableEq cols]
    (points : cols → rows → ℝ) (subset : Finset cols) (base : cols) : Matrix rows cols ℝ :=
  fun row col => if col ∈ subset then points col row - points base row else 0

theorem adim_image_eq_rank {rows cols : Type*} [Fintype rows] [Fintype cols]
    [DecidableEq cols] (points : cols → rows → ℝ) (subset : Finset cols) (base : cols)
    (hbase : base ∈ subset) :
    HibiLi.adim (points '' (subset : Set cols)) = (differenceMatrix points subset base).rank := by
  unfold HibiLi.adim
  rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_image_of_mem points hbase),
    Matrix.rank_eq_finrank_span_cols]
  suffices hh : Submodule.span ℝ ((fun point => point -ᵥ points base) ''
      points '' (subset : Set cols)) =
      Submodule.span ℝ (Set.range (differenceMatrix points subset base).col) by rw [hh]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨point, ⟨idx, hidx, rfl⟩, rfl⟩
    change idx ∈ subset at hidx
    apply Submodule.subset_span
    refine ⟨idx, ?_⟩
    ext row
    simp [differenceMatrix, Matrix.col, hidx]
  · apply Submodule.span_le.mpr
    rintro _ ⟨idx, rfl⟩
    by_cases hidx : idx ∈ subset
    · apply Submodule.subset_span
      refine ⟨points idx, Set.mem_image_of_mem points hidx, ?_⟩
      ext row
      simp [differenceMatrix, Matrix.col, hidx]
    · have hz : (differenceMatrix points subset base).col idx = 0 := by
        ext row
        simp [differenceMatrix, Matrix.col, hidx]
      rw [hz]
      exact Submodule.zero_mem _

theorem rational_matrix_rank_certificate {rows cols : Type*}
    [Fintype rows] [Fintype cols] {rr : ℕ} (mat : Matrix rows cols ℚ)
    (pivot : Fin rr → cols) (dual : Matrix (Fin rr) rows ℚ)
    (coeff : Matrix (Fin rr) cols ℚ)
    (hleft : dual * mat.submatrix id pivot = 1)
    (hfactor : mat = mat.submatrix id pivot * coeff) :
    (mat.map (Rat.castHom ℝ)).rank = rr := by
  apply matrix_rank_certificate (mat.map (Rat.castHom ℝ)) pivot
    (dual.map (Rat.castHom ℝ)) (coeff.map (Rat.castHom ℝ))
  · have hh := congrArg (fun mm => mm.map (Rat.castHom ℝ)) hleft
    rw [Matrix.map_mul (f := Rat.castHom ℝ)] at hh
    have hone : (1 : Matrix (Fin rr) (Fin rr) ℚ).map (Rat.castHom ℝ) = 1 := by
      ext ii jj
      by_cases hij : ii = jj <;> simp [Matrix.one_apply, hij]
    rw [hone] at hh
    exact hh
  · have hh := congrArg (fun mm => mm.map (Rat.castHom ℝ)) hfactor
    rw [Matrix.map_mul (f := Rat.castHom ℝ)] at hh
    exact hh

end HibiLi.Example21
