/-
HibiLiLean — symmetry and composition of integral unimodular affine images.
-/
import HibiLi.Polytope.Affine

namespace HibiLi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private abbrev realMatrix (matrix : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  matrix.map (Int.cast : ℤ → ℝ)

private abbrev realVector (vector : ι → ℤ) : ι → ℝ := fun coord => (vector coord : ℝ)

private theorem realMatrix_mul (left right : Matrix ι ι ℤ) :
    realMatrix (left * right) = realMatrix left * realMatrix right :=
  (Int.castRingHom ℝ).mapMatrix.map_mul left right

omit [DecidableEq ι] in
private theorem realVector_mulVec (matrix : Matrix ι ι ℤ) (vector : ι → ℤ) :
    realVector (matrix.mulVec vector) = (realMatrix matrix).mulVec (realVector vector) := by
  funext coord
  exact (Int.castRingHom ℝ).map_mulVec matrix vector coord

omit [Fintype ι] [DecidableEq ι] in
private theorem realVector_add (left right : ι → ℤ) :
    realVector (left + right) = realVector left + realVector right := by
  ext coord
  simp [realVector]

omit [Fintype ι] [DecidableEq ι] in
private theorem realVector_neg (vector : ι → ℤ) : realVector (-vector) = -realVector vector := by
  ext coord
  simp [realVector]

theorem UnimodEquiv.trans {first middle last : Set (ι → ℝ)}
    (left : UnimodEquiv first middle) (right : UnimodEquiv middle last) : UnimodEquiv first last := by
  rcases left with ⟨leftMatrix, leftDet, leftShift, leftImage⟩
  rcases right with ⟨rightMatrix, rightDet, rightShift, rightImage⟩
  refine ⟨rightMatrix * leftMatrix, ?_, rightMatrix.mulVec leftShift + rightShift, ?_⟩
  · rw [Matrix.det_mul]
    rcases leftDet with leftDet | leftDet <;> rcases rightDet with rightDet | rightDet <;>
      simp [leftDet, rightDet]
  · rw [rightImage, leftImage, Set.image_image]
    congr 1
    funext point
    change (realMatrix rightMatrix).mulVec ((realMatrix leftMatrix).mulVec point + realVector leftShift) +
      realVector rightShift = (realMatrix (rightMatrix * leftMatrix)).mulVec point +
        realVector (rightMatrix.mulVec leftShift + rightShift)
    rw [realMatrix_mul, realVector_add, realVector_mulVec, Matrix.mulVec_add,
      ← Matrix.mulVec_mulVec]
    exact add_assoc _ _ _

theorem UnimodEquiv.symm {body target : Set (ι → ℝ)}
    (equivalent : UnimodEquiv body target) : UnimodEquiv target body := by
  rcases equivalent with ⟨matrix, determinant, shift, image_eq⟩
  have unit_det : IsUnit matrix.det := by
    rcases determinant with positive | negative
    · simp [positive]
    · simp [negative]
  have inverse_det := Matrix.det_nonsing_inv_mul_det matrix unit_det
  refine ⟨matrix⁻¹, ?_, -(matrix⁻¹.mulVec shift), ?_⟩
  · rcases determinant with positive | negative
    · left
      simp [positive]
    · right
      rw [negative] at inverse_det
      linarith
  · have inverse_product : realMatrix matrix⁻¹ * realMatrix matrix = 1 := by
      rw [← realMatrix_mul, Matrix.nonsing_inv_mul _ unit_det]
      exact (Int.castRingHom ℝ).mapMatrix.map_one
    have inverse_point (point : ι → ℝ) :
        (realMatrix matrix⁻¹).mulVec ((realMatrix matrix).mulVec point + realVector shift) +
          realVector (-(matrix⁻¹.mulVec shift)) = point := by
      rw [realVector_neg, realVector_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_mulVec, inverse_product, Matrix.one_mulVec]
      abel
    rw [image_eq, Set.image_image]
    symm
    calc
      _ = (id : (ι → ℝ) → (ι → ℝ)) '' body := by
        congr 1
        funext point
        exact inverse_point point
      _ = body := Set.image_id body

end HibiLi
