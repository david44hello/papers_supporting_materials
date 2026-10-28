/-
Osserman/Defs/Cayley.lean — the octonions (Cayley–Dickson over Mathlib's quaternions), the standard symmetric Clifford
system S_0, …, S_8 on ℝ^16 = 𝕆 ⊕ 𝕆, and the Cayley curvature tensor R_Cay (paper 013, §6, l. 648-668; l. 190-192).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE.
* `𝕆 = ℍ × ℍ` with the Cayley–Dickson product `(a,b)(c,d) = (ac - d̄b, da + bc̄)` and conjugation `(a,b)‾ = (ā,-b)`:
  a standard model of the octonions; the coordinates `x_0, …, x_7` of `ℝ^8` are the components of `(a, b)`, so the
  standard basis of `ℝ^8` is an orthonormal basis `e_1, …, e_8` of `𝕆` (l. 653).
* `stdSys` is the system of l. 649-652; `RCayFun = -R_𝕆` with the Brown–Gray formula in the form of l. 657-659
  (cited [BG, Eq. (6.12)] in the form [Nik2012, eq. (7)]); it is the DEFINITION of `R_Cay` here (Mathlib has no Cayley
  projective plane). The paper's normalization "sectional curvatures between 1 and 4" (l. 191-192) is a PROVED row.
* Matrices of maps are built column by column (`matOfFun`); a Lean row proves that the maps are linear.
-/
import Osserman.Defs.Curvature

namespace Osserman

open Matrix Quaternion

/-- Octonions as pairs of quaternions. WARNING: `Oct` is `ℍ × ℍ`, so `p * q` on it is Mathlib's COMPONENTWISE product of
pairs, NOT the octonion product; the octonion product is `octMul` (and `omul` on `ℝ^8`), the only one used in this
project. Likewise `‖·‖` on `Vec n` is the sup norm; lengths here are always written with `⬝ᵥ`. -/
abbrev Oct := ℍ[ℝ] × ℍ[ℝ]

/-- Cayley–Dickson product `(a,b)(c,d) = (ac - d̄b, da + bc̄)`. -/
def octMul (p q : Oct) : Oct := (p.1 * q.1 - star q.2 * p.2, q.2 * p.1 + p.2 * star q.1)

/-- Octonion conjugation `(a,b)‾ = (ā, -b)`. -/
def octConj (p : Oct) : Oct := (star p.1, -p.2)

/-- `ℝ^8 → 𝕆`, coordinates in the order `re, i, j, k` of the two quaternions. -/
def octOfVec (x : Vec 8) : Oct := (⟨x 0, x 1, x 2, x 3⟩, ⟨x 4, x 5, x 6, x 7⟩)

/-- `𝕆 → ℝ^8`. -/
def vecOfOct (p : Oct) : Vec 8 := ![p.1.re, p.1.imI, p.1.imJ, p.1.imK, p.2.re, p.2.imI, p.2.imJ, p.2.imK]

/-- The octonion product on `ℝ^8`. -/
def omul (x y : Vec 8) : Vec 8 := vecOfOct (octMul (octOfVec x) (octOfVec y))

/-- Octonion conjugation on `ℝ^8`. -/
def oconj (x : Vec 8) : Vec 8 := vecOfOct (octConj (octOfVec x))

/-- The two octonionic coordinates of `x ∈ ℝ^16` (l. 648). -/
def oct1 (x : Vec 16) : Vec 8 := fun i => x (Fin.castAdd 8 i)

/-- The second octonionic coordinate. -/
def oct2 (x : Vec 16) : Vec 8 := fun i => x (Fin.natAdd 8 i)

/-- `(x_1, x_2) ∈ ℝ^8 × ℝ^8 ↦ ℝ^16`. -/
def octPair (a b : Vec 8) : Vec 16 := Fin.append a b

/-- The orthonormal basis `e_1, …, e_8` of `𝕆` (`octBasis k` = `e_{k+1}`). -/
def octBasis (k : Fin 8) : Vec 8 := Pi.single k 1

/-- The standard system as maps (l. 649-652): `S_0(x_1,x_2) = (x_1, -x_2)` and
`S_{k+1}(x_1,x_2) = (e_{k+1} x̄_2, x̄_1 e_{k+1})`. -/
def stdSysFun (i : Fin 9) (x : Vec 16) : Vec 16 :=
  if h : i.val = 0 then octPair (oct1 x) (-oct2 x)
  else
    let e := octBasis ⟨i.val - 1, by omega⟩
    octPair (omul e (oconj (oct2 x))) (omul (oconj (oct1 x)) e)

/-- The matrix whose `c`-th column is `f(e_c)`. -/
def matOfFun {n : ℕ} (f : Vec n → Vec n) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun r c => f (Pi.single c 1) r

/-- The standard system `S_0, …, S_8` on `ℝ^16` (l. 649-652), as matrices. -/
def stdSys (i : Fin 9) : Matrix (Fin 16) (Fin 16) ℝ := matOfFun (stdSysFun i)

/-- `(u ∧ v) z = ⟨u,z⟩v - ⟨v,z⟩u` (l. 654). -/
def wedge {n : ℕ} (u v z : Vec n) : Vec n := (u ⬝ᵥ z) • v - (v ⬝ᵥ z) • u

/-- Brown–Gray (l. 657-659): `R_𝕆(u,v) = 3 u∧v + ∑_{i=0}^8 S_iu ∧ S_iv`. -/
def ROctFun (u v z : Vec 16) : Vec 16 := (3 : ℝ) • wedge u v z + ∑ i, wedge (stdSys i *ᵥ u) (stdSys i *ᵥ v) z

/-- `R_Cay = -R_𝕆` (l. 666): the curvature tensor of the Cayley projective plane (DEFINITION, see the header). -/
def RCayFun (u v z : Vec 16) : Vec 16 := -ROctFun u v z

/-- `R` is of Cayley type (l. 202-207): `R = aR_1 + b T^*R_Cay` for constants `a, b` and some `T ∈ O(16)`. -/
def IsCayleyType (R : CurvTensor 16) : Prop :=
  ∃ a b : ℝ, ∃ T ∈ Matrix.orthogonalGroup (Fin 16) ℝ,
    ∀ u v w, R.op u v w = a • R1fun u v w + b • pullbackFun T RCayFun u v w

end Osserman
