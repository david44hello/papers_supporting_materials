/-
Osserman/Defs/Blocks.lean — the four 16×16 blocks of a 32×32 matrix in the splitting ℝ^32 = ℝ^16 ⊕ ℝ^16, z = (x, y)
(paper 013, §5, l. 543-548 and 569-571).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE. `z = Fin.append x y` puts `x` in the coordinates 0-15 and `y` in 16-31 (as in `sec2_F_eval`). For
`P = [[H, Bᵀ], [B, D]]` (l. 569): `blkXX P = H` (rows and columns of `x`), `blkYX P = B` (rows of `y`, columns of
`x`; the paper's `C_i` in Proposition 5.1), `blkXY P` the upper-right block (`= Bᵀ` when `P` is symmetric), and
`blkYY P = D`.
-/
import Osserman.Defs.Basic

namespace Osserman

open Matrix

/-- The upper-left block `H` (rows and columns of `x`). -/
def blkXX (M : Matrix (Fin 32) (Fin 32) ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  M.submatrix (Fin.castAdd 16) (Fin.castAdd 16)

/-- The upper-right block (rows of `x`, columns of `y`). -/
def blkXY (M : Matrix (Fin 32) (Fin 32) ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  M.submatrix (Fin.castAdd 16) (Fin.natAdd 16)

/-- The lower-left block `B` (rows of `y`, columns of `x`). -/
def blkYX (M : Matrix (Fin 32) (Fin 32) ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  M.submatrix (Fin.natAdd 16) (Fin.castAdd 16)

/-- The lower-right block `D` (rows and columns of `y`). -/
def blkYY (M : Matrix (Fin 32) (Fin 32) ℝ) : Matrix (Fin 16) (Fin 16) ℝ :=
  M.submatrix (Fin.natAdd 16) (Fin.natAdd 16)

/-- The block convention, pinned: for `z = (x, y)`, `⟨Mz,z⟩ = ⟨Hx,x⟩ + ⟨(upper right)y,x⟩ + ⟨Bx,y⟩ + ⟨Dy,y⟩`. -/
theorem quad_blocks (M : Matrix (Fin 32) (Fin 32) ℝ) (x y : Vec 16) :
    (Fin.append x y : Vec 32) ⬝ᵥ (M *ᵥ (Fin.append x y : Vec 32)) =
      x ⬝ᵥ (blkXX M *ᵥ x) + x ⬝ᵥ (blkXY M *ᵥ y) + y ⬝ᵥ (blkYX M *ᵥ x) + y ⬝ᵥ (blkYY M *ᵥ y) := by
  simp only [dotProduct, mulVec, blkXX, blkXY, blkYX, blkYY, submatrix_apply]
  rw [Fin.sum_univ_add (a := 16) (b := 16)]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_univ_add (a := 16) (b := 16), mul_add,
    Finset.sum_add_distrib]
  ring

end Osserman
