/-
NagataHigman/Defs/WordCycle.lean — the map `Φ` of Proposition 2.1, step (1), and the projection `P` onto `C_N`
(paper Section 2.2-2.3).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.04, line 258 (`P`), 249-250
(step (1): `Φ`). Indexing as in Defs/FreeAlgebra.lean and Defs/GroupAlgebra.lean: the paper's letter `x_j` is `letter F (j-1)`,
its point `j` is `j - 1 : Fin N`, and its point `N` is `Fin.last m` (`N = m + 1`).
-/
import NagataHigman.Defs.FreeAlgebra
import NagataHigman.Defs.GroupAlgebra

noncomputable section

namespace NagataHigman

open Equiv

/-- The cycle list `[N, w(0), w(1), …, w(m-1)]` of the multilinear word `x_{w(0)} ⋯ x_{w(m-1)}`, as points of
`Fin (m+1)` (the letter `x_j` gives the point `j`; the paper's point `N` is `Fin.last m`). -/
def cycList {m : ℕ} (w : Perm (Fin m)) : List (Fin (m + 1)) :=
  Fin.last m :: List.ofFn (fun i => (w i).castSucc)

/-- **Step (1), `Φ` on words** (paper line 286): `Φ(x_{j_1} ⋯ x_{j_m})` is the `N`-cycle
`N → j_1 → ⋯ → j_m → N`. (`List.formPerm l` sends each entry of `l` to the next one and the last entry to the first.) -/
def wordCycle {m : ℕ} (w : Perm (Fin m)) : Perm (Fin (m + 1)) := List.formPerm (cycList w)

variable (F : Type*) [Field F]

/-- Coordinates to `V_m`: `c ↦ Σ_w c_w · x_{w(0)} ⋯ x_{w(m-1)}` (the multilinear words, paper line 192). -/
def wordLin (m : ℕ) : (Perm (Fin m) → F) →ₗ[F] FreeNUAlg F :=
  Fintype.linearCombination F (multilinWord F (m := m))

/-- Coordinates to `C_N`: `c ↦ Σ_w c_w · Φ(w)` (the `N`-cycles). The paper's linear map `Φ : V_m → C_N` (line 287) is
`cycleLin ∘ wordLin⁻¹`; for `S ⊆ V_m`, the image `Φ(S)` is `(S.comap (wordLin F m)).map (cycleLin F m)`. -/
def cycleLin (m : ℕ) : (Perm (Fin m) → F) →ₗ[F] GrpAlg F (m + 1) :=
  Fintype.linearCombination F (fun w : Perm (Fin m) => perm F (wordCycle w))

open Classical in
/-- `P`: the coordinate projection of `F[S_N]` onto `C_N` (paper line 258): keep the coefficients of the `N`-cycles. -/
def cycleProj (N : ℕ) : GrpAlg F N →ₗ[F] GrpAlg F N where
  toFun a := ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin N) => IsFullCycle σ), a.coeff σ • perm F σ
  map_add' x y := by
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

end NagataHigman

end
