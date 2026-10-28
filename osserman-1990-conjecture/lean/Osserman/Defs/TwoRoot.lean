/-
Osserman/Defs/TwoRoot.lean — the objects of Theorem C's proof: the two-eigenvalue hypothesis with the paper's names
μ, κ (l. 337-338), A(x), Q(x), L(x), the polarization B(u,v), the three normal forms (eq:Cl7), (eq:Cl8), (eq:Cayley)
(l. 254-263) (paper 013, §1 and §2).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Cayley

namespace Osserman

open Matrix

/-- The hypothesis of Theorem C with the paper's names (l. 337-338): `κ ≠ 0`, and at every unit `x` the reduced
Jacobi operator has the eigenvalue `μ` with multiplicity 8 and `μ + κ` with multiplicity 7 (so no other one). -/
def TwoRootHyp (R : CurvTensor 16) (μ κ : ℝ) : Prop :=
  κ ≠ 0 ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ = 8 ∧ R.redMult x (μ + κ) = 7

/-- `A(x) = (J_x - μΠ(x))/κ` (l. 339). -/
noncomputable def Amat (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : Matrix (Fin 16) (Fin 16) ℝ :=
  κ⁻¹ • (R.jacobi x - μ • Pi x)

/-- `Q(x) = A(x) + xxᵀ` (l. 367). -/
noncomputable def Qmat (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : Matrix (Fin 16) (Fin 16) ℝ :=
  Amat R μ κ x + vecMulVec x x

/-- `L(x) = ℝx + Im A(x)` (l. 367). -/
noncomputable def Lsub (R : CurvTensor 16) (μ κ : ℝ) (x : Vec 16) : Submodule ℝ (Vec 16) :=
  Submodule.span ℝ {x} ⊔ LinearMap.range (Matrix.toLin' (Amat R μ κ x))

/-- A matrix family is quadratic: `A(x) = ∑_{a,b} x_a x_b M_{ab}` for some matrices `M_{ab}`. -/
def IsQuadFamily {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ M : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ, ∀ x, A x = ∑ a, ∑ b, (x a * x b) • M a b

/-- `𝓑(u,v) = (A(u+v) - A(u) - A(v))/2` (l. 347). -/
noncomputable def Bpol {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) (u v : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / 2 : ℝ) • (A (u + v) - A u - A v)

/-- The reconstructed tensor `R_A(u,v)w = (2/3)(𝓑(v,w)u - 𝓑(u,w)v)` (eq:reconstruct, l. 357). -/
noncomputable def RAfun {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) (u v w : Vec n) : Vec n :=
  (2 / 3 : ℝ) • (Bpol A v w *ᵥ u - Bpol A u w *ᵥ v)

/-- Form (eq:Cl7) (l. 255): `A(x) = ∑_{i=1}^7 (J_ix)(J_ix)ᵀ`. -/
def IsFormCl7 (A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ) : Prop :=
  ∃ J : Fin 7 → Matrix (Fin 16) (Fin 16) ℝ, IsCliffordStr J ∧ ∀ x, A x = ∑ i, vecMulVec (J i *ᵥ x) (J i *ᵥ x)

/-- Form (eq:Cl8) (l. 257): `A(x) = Π(x) - ∑_{i=1}^8 (J_ix)(J_ix)ᵀ`. -/
def IsFormCl8 (A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ) : Prop :=
  ∃ J : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ, IsCliffordStr J ∧
    ∀ x, A x = Pi x - ∑ i, vecMulVec (J i *ᵥ x) (J i *ᵥ x)

/-- The Cayley family of a system `H_0, …, H_8` (eq:Cayley, l. 259-260):
`A(x) = ½(|x|²I + ∑ ⟨H_ix,x⟩H_i) - xxᵀ`. -/
noncomputable def Acay (H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) : Matrix (Fin 16) (Fin 16) ℝ :=
  (1 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) + ∑ i, (x ⬝ᵥ (H i *ᵥ x)) • H i) - vecMulVec x x

/-- Form (eq:Cayley) (l. 259-261), for a symmetric Clifford system `H_0, …, H_8` on `ℝ^16`. -/
def IsFormCayley (A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ) : Prop :=
  ∃ H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ, IsSymmCliffordSystem H ∧ ∀ x, A x = Acay H x

end Osserman
