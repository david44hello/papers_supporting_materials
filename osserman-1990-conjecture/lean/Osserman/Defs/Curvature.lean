/-
Osserman/Defs/Curvature.lean — algebraic curvature tensors, Jacobi operators, reduced multiplicities, Osserman and
Clifford tensors, `R_1`, `T^*R`, Jacobi-proportionality (paper 013, §1, l. 165-192 and l. 282-293).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE.
* `CurvTensor n`: a trilinear `R(u,v)w` with `R(u,v) = -R(v,u)`, `⟨R(u,v)w,z⟩ = -⟨R(u,v)z,w⟩` and the first Bianchi
  identity (the standard axioms of an algebraic curvature tensor; pair symmetry follows from them).
* `jacobiMap R x y = R(y,x)x` (l. 167); `jacobi R x` is its matrix.
* `redMult R x μ` = the dimension of the `μ`-eigenspace of `J_x` INSIDE `x^⊥` — the multiplicity of `μ` for the
  REDUCED operator on `x^⊥` (l. 168-171; 0 if `μ` is not a reduced eigenvalue).
* `IsOsserman R`: these multiplicities are the same for all unit `x` (the reduced spectrum, with multiplicities, does
  not depend on `x`, l. 168-169). `IsOssermanSet R` is the paper's literal reading (the SET of reduced eigenvalues does
  not depend on `x`); the row `isOsserman_iff_set` of Paper/Statements.lean states that the two agree, which is what
  makes the paper's "multiplicity pattern of R" (l. 171-173) well defined.
-/
import Osserman.Defs.Basic

namespace Osserman

open Matrix

/-- Build a trilinear map from a function that is linear in each argument. -/
def mkTri {n : ℕ} (f : Vec n → Vec n → Vec n → Vec n)
    (h1 : ∀ u u' v w, f (u + u') v w = f u v w + f u' v w) (h1s : ∀ (c : ℝ) u v w, f (c • u) v w = c • f u v w)
    (h2 : ∀ u v v' w, f u (v + v') w = f u v w + f u v' w) (h2s : ∀ (c : ℝ) u v w, f u (c • v) w = c • f u v w)
    (h3 : ∀ u v w w', f u v (w + w') = f u v w + f u v w') (h3s : ∀ (c : ℝ) u v w, f u v (c • w) = c • f u v w) :
    Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Vec n where
  toFun u := LinearMap.mk₂ ℝ (f u) (h2 u) (fun c v w => h2s c u v w) (h3 u) (fun c v w => h3s c u v w)
  map_add' u u' := LinearMap.ext fun v => LinearMap.ext fun w => by simp [h1]
  map_smul' c u := LinearMap.ext fun v => LinearMap.ext fun w => by simp [h1s]

/-- An algebraic curvature tensor on `ℝ^n` (l. 166). -/
structure CurvTensor (n : ℕ) where
  /-- `R(u, v) w`. -/
  op : Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Vec n →ₗ[ℝ] Vec n
  antisymm : ∀ u v w, op u v w = -op v u w
  skew : ∀ u v w z, op u v w ⬝ᵥ z = -(op u v z ⬝ᵥ w)
  bianchi : ∀ u v w, op u v w + op v w u + op w u v = 0

namespace CurvTensor

variable {n : ℕ}

/-- The Jacobi operator `J_x y = R(y, x) x` (l. 167). -/
def jacobiMap (R : CurvTensor n) (x : Vec n) : Vec n →ₗ[ℝ] Vec n where
  toFun y := R.op y x x
  map_add' a b := by simp
  map_smul' c a := by simp

/-- The matrix of `J_x`. -/
noncomputable def jacobi (R : CurvTensor n) (x : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' (R.jacobiMap x)

/-- The multiplicity of `μ` as an eigenvalue of the REDUCED Jacobi operator, `J_x` on `x^⊥` (l. 168-171). -/
noncomputable def redMult (R : CurvTensor n) (x : Vec n) (μ : ℝ) : ℕ :=
  Module.finrank ℝ ↥(Module.End.eigenspace (R.jacobiMap x) μ ⊓ perp x)

/-- `R` is Osserman (l. 168-169): the reduced spectrum of `J_x`, with multiplicities, is the same for all unit `x`. -/
def IsOsserman (R : CurvTensor n) : Prop :=
  ∀ x y : Vec n, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 → ∀ μ : ℝ, R.redMult x μ = R.redMult y μ

/-- The paper's literal definition (l. 168-169): the SET of reduced eigenvalues of `J_x` is the same for all unit `x`
(the row `isOsserman_iff_set` states that this agrees with `IsOsserman`). -/
def IsOssermanSet (R : CurvTensor n) : Prop :=
  ∀ x y : Vec n, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 → ∀ μ : ℝ, (0 < R.redMult x μ ↔ 0 < R.redMult y μ)

/-- `R` is Clifford (l. 184-186): `J_x = λ_0 Π(x) + ∑ η_i (J_i x)(J_i x)ᵀ` for a `Cl(ν)`-structure and constants. -/
def IsClifford (R : CurvTensor n) : Prop :=
  ∃ (ν : ℕ) (J : Fin ν → Matrix (Fin n) (Fin n) ℝ), IsCliffordStr J ∧ ∃ (l0 : ℝ) (η : Fin ν → ℝ),
    ∀ x, R.jacobi x = l0 • Pi x + ∑ i, η i • vecMulVec (J i *ᵥ x) (J i *ᵥ x)

end CurvTensor

/-- `R_1(u,v)w = ⟨v,w⟩u - ⟨u,w⟩v` (l. 175), as a function. -/
def R1fun {n : ℕ} (u v w : Vec n) : Vec n := (v ⬝ᵥ w) • u - (u ⬝ᵥ w) • v

/-- `(T^*R)(u,v)w = T⁻¹ R(Tu,Tv)Tw` for an orthogonal `T` (l. 182), written with `Tᵀ = T⁻¹`. -/
def pullbackFun {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (f : Vec n → Vec n → Vec n → Vec n) (u v w : Vec n) : Vec n :=
  Tᵀ *ᵥ f (T *ᵥ u) (T *ᵥ v) (T *ᵥ w)

/-- The orthogonal projection onto the `μ|x|²`-eigenspace of the reduced `J_x` is `π_i(x)` of (eq:JP); we state
Jacobi-proportionality (l. 282-293) with the quadratic forms `⟨π(x)y, y⟩ = |y'|²`, `y'` the component of `y` in that
eigenspace: for every reduced eigenvalue `μ|x|²` (here `μ` = its value at unit vectors) and nonzero `x, y`,
`|x|² ⟨π_μ(x)y,y⟩ = |y|² ⟨π_μ(y)x,x⟩`. The projection is onto `E_μ(x) := eigenspace ⊓ x^⊥`. -/
def IsJacobiProportional {n : ℕ} (R : CurvTensor n) : Prop :=
  ∀ μ : ℝ, ∀ x y : Vec n, x ≠ 0 → y ≠ 0 →
    ∀ (px : Vec n →ₗ[ℝ] Vec n) (py : Vec n →ₗ[ℝ] Vec n),
      -- `px` is the orthogonal projection onto the reduced `μ|x|²`-eigenspace of `J_x`, `py` likewise for `y`
      (LinearMap.range px = Module.End.eigenspace (R.jacobiMap x) (μ * (x ⬝ᵥ x)) ⊓ perp x ∧
        ∀ z w, px z ⬝ᵥ w = z ⬝ᵥ px w ∧ px (px z) = px z) →
      (LinearMap.range py = Module.End.eigenspace (R.jacobiMap y) (μ * (y ⬝ᵥ y)) ⊓ perp y ∧
        ∀ z w, py z ⬝ᵥ w = z ⬝ᵥ py w ∧ py (py z) = py z) →
      (x ⬝ᵥ x) * (px y ⬝ᵥ y) = (y ⬝ᵥ y) * (py x ⬝ᵥ x)

end Osserman
