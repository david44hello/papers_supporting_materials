/-
NagataHigman/Proofs/MatInvNonVacuity.lean — the trust-surface definition `IsConjInvariant` is not vacuous.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Both sides are pinned: a single matrix entry, the variable `X_{(0,0,1)}` of a 2×2 matrix, is NOT invariant (conjugate
by diag(2, 1)); and every trace `tr(x_{i_1} ⋯ x_{i_r})` IS invariant (Proofs/MatrixInvariants.lean,
`tracePoly_isConjInvariant`), so `matInvariants` is neither everything nor only the constants.
-/
import NagataHigman.Proofs.MatrixInvariants

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman

/-- The `(0,1)` entry of a `2 × 2` matrix is not invariant under conjugation. -/
theorem entry_not_conjInvariant :
    (MvPolynomial.X ((0 : Fin 1), (0 : Fin 2), (1 : Fin 2)) : MatPoly ℚ 2 1) ∉ matInvariants ℚ 2 1 := by
  intro h
  have hd : IsUnit (Matrix.diagonal ![(2 : ℚ), 1]) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    simp
  obtain ⟨u, hu⟩ := hd
  let E : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of ![![0, 1], ![0, 0]]
  have h1 := h u (fun _ => E * (u : Matrix (Fin 2) (Fin 2) ℚ))
  simp only [MvPolynomial.eval_X, tupleCoords, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1
  rw [hu] at h1
  simp [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal] at h1

/-- A trace is a non-constant invariant: for `2 × 2` matrices, `tr(x_0) ∈ matInvariants`. -/
theorem trace_mem_matInvariants : tracePoly ℚ 2 1 [0] ∈ matInvariants ℚ 2 1 :=
  tracePoly_isConjInvariant [0]

end NagataHigman.Proofs

end
