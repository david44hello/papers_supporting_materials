/-
Osserman/Defs/ThreeRoot.lean — the objects of Section 7 of paper 013 ("Tensors with three eigenvalues, and
Jacobi-proportionality", P013_short.tex l. 689-841, and Corollary D / Theorem E, l. 295-311): E(x), N(x) of the
standard Cayley family, the Cayley lines, the multiplicity patterns, R_J, and the data of Remark 7.2.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.TwoRoot
import Osserman.Defs.Poly

namespace Osserman

open Matrix MvPolynomial

/-! ## New definitions for Section 7 -/

/-- `L(x) = ℝx + Im A(x)` for the STANDARD Cayley family `A = Acay stdSys` ((eq:Cayley) with `H_i = S_i`), lines
691-694 of P013_short.tex (with §2, line 367).
TRUST SURFACE: the span of `x` together with the image of the matrix `A(x)`. -/
noncomputable def Lstd (x : Vec 16) : Submodule ℝ (Vec 16) :=
  Submodule.span ℝ {x} ⊔ LinearMap.range (Matrix.toLin' (Acay stdSys x))

/-- The orthogonal complement `W^⊥ = {y | ⟨w, y⟩ = 0 for all w ∈ W}` of a subspace (Section 7, line 692,
"$N(x)=L(x)^\perp$"; also sec_common_lemmas.tex l. 12 `E^⊥` and l. 44-45).
TRUST SURFACE: the vectors perpendicular (for the dot product `⬝ᵥ`) to every vector of `W`. -/
def orthSub {n : ℕ} (W : Submodule ℝ (Vec n)) : Submodule ℝ (Vec n) where
  carrier := {y | ∀ w ∈ W, w ⬝ᵥ y = 0}
  add_mem' := by
    intro a b ha hb w hw
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [dotProduct_add, ha w hw, hb w hw, add_zero]
  zero_mem' := by
    intro w _
    exact dotProduct_zero w
  smul_mem' := by
    intro c y hy w hw
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [dotProduct_smul, hy w hw, smul_zero]

/-- `E(x) = L(x) ∩ x^⊥` for the standard Cayley family (lines 691-692).
TRUST SURFACE: the vectors of `L(x)` orthogonal to `x`. -/
noncomputable def Estd (x : Vec 16) : Submodule ℝ (Vec 16) := Lstd x ⊓ perp x

/-- `N(x) = L(x)^⊥` for the standard Cayley family (line 692).
TRUST SURFACE: the vectors orthogonal to all of `L(x)`. -/
noncomputable def Nstd (x : Vec 16) : Submodule ℝ (Vec 16) := orthSub (Lstd x)

/-- The octonion `1` in `ℝ^8` (proof of Lemma 7.1, lines 717-728: "$\mathcal C_1$", "$c=D(1)$", "$\gamma=C(1)$").
TRUST SURFACE: the first standard basis vector, i.e. the quaternion pair `(1, 0)`, the unit of `omul`; NOT
`(1 : Oct)`, which is the componentwise unit `(1, 1)`. -/
def oone : Vec 8 := Pi.single 0 1

/-- The coordinate change `(x_1, x_2) ↦ (x_1, x̄_2)` of the proof of Lemma 7.1 (line 702), as a function.
TRUST SURFACE: keep the first octonion coordinate, conjugate the second. -/
def conjChangeFun (x : Vec 16) : Vec 16 := octPair (oct1 x) (oconj (oct2 x))

/-- The matrix of `conjChangeFun` (line 702); the row `lem_7_1_conj_change` proves that it acts as the formula.
TRUST SURFACE: the matrix whose `c`-th column is `conjChangeFun e_c`. -/
def conjChange : Matrix (Fin 16) (Fin 16) ℝ := matOfFun conjChangeFun

/-- The Cayley line `𝒞_ω = {(u, ωu) : u ∈ 𝕆}` (line 704), in the NEW coordinates `y = (x_1, x̄_2)`.
TRUST SURFACE: the vectors whose second octonion coordinate is `ω` times (octonion product) the first. -/
def cayLine (ω : Vec 8) : Set (Vec 16) := {y | oct2 y = omul ω (oct1 y)}

/-- The Cayley line `𝒞_∞ = {(0, v) : v ∈ 𝕆}` (line 705), in the new coordinates.
TRUST SURFACE: the vectors whose first octonion coordinate is zero. -/
def cayLineInf : Set (Vec 16) := {y | oct1 y = 0}

/-- `S_{(w_0,a)} = w_0S_0 + ∑_{i=1}^8 a_iS_i` with `a = ∑ a_ie_i` (lines 707-708).
TRUST SURFACE: the combination of the standard system with coefficient `w_0` on `S_0` and `a_k` on `S_{k+1}`. -/
def stdComb (w0 : ℝ) (a : Vec 8) : Matrix (Fin 16) (Fin 16) ℝ := w0 • stdSys 0 + ∑ k : Fin 8, a k • stdSys k.succ

/-- The value at `x` of a polynomial vector field `E = (E_0, …, E_{n-1})` (proof of Theorem E, lines 745-748).
TRUST SURFACE: evaluate each component polynomial at `x`. -/
noncomputable def evalField {n : ℕ} (E : Fin n → MvPolynomial (Fin n) ℝ) (x : Vec n) : Vec n :=
  fun j => eval x (E j)

/-- `R` has the multiplicity pattern `m = (m_1, …, m_k)` (lines 168-173): there are `k` DISTINCT values `μ_1, …, μ_k`
with `redMult x μ_i = m_i` at every unit `x` (as `thm_C`'s hypothesis `h2` does for `(8,7)`).
TRUST SURFACE: when `∑ m_i = n - 1` these fill `x^⊥`, so they are exactly the reduced eigenvalues ("exactly `k` reduced
eigenvalues of multiplicities `m`", row `hasPattern_osserman`); the order of the list does not matter. -/
def HasPattern {n k : ℕ} (R : CurvTensor n) (m : Fin k → ℕ) : Prop :=
  ∃ ev : Fin k → ℝ, Function.Injective ev ∧ ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i

/-- The four patterns of Theorem E (lines 308-310), written `(a, b, t)` with the smallest multiplicity `t` LAST and the
multiplicity `b` into which `t` is merged in the proof (lines 753-758) SECOND.
TRUST SURFACE: `m` is one of `(7,7,1)`, `(8,6,1)`, `(8,5,2)`, `(7,6,2)`. -/
def IsThmEPattern (m : Fin 3 → ℕ) : Prop :=
  m = ![7, 7, 1] ∨ m = ![8, 6, 1] ∨ m = ![8, 5, 2] ∨ m = ![7, 6, 2]

/-- The rank-one Jacobi family `(Jx)(Jx)ᵀ` (lines 759-761).
TRUST SURFACE: `vecMulVec (Jx) (Jx)`, the map `z ↦ ⟨Jx, z⟩ Jx`. -/
def jfam {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec (J *ᵥ x) (J *ᵥ x)

/-- `R_J`, "the curvature tensor whose Jacobi family is $(Jx)(Jx)^T$, obtained for example from (eq:reconstruct)"
(lines 759-761): `R_J = R_A` of (eq:reconstruct) for `A = jfam J`.
TRUST SURFACE: `R_J(u,v)w = (2/3)(𝓑(v,w)u - 𝓑(u,w)v)` with `𝓑` the polarization of `x ↦ (Jx)(Jx)ᵀ`. -/
noncomputable def RJfun {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (u v w : Vec n) : Vec n := RAfun (jfam J) u v w

/-- The data of the proof of Theorem E after its first paragraph (lines 740-751): `m` is a Theorem E pattern, `ev`
are the corresponding DISTINCT reduced eigenvalues (`τ = ev 2` of the smallest multiplicity `t = m 2`, `μ = ev 1` the
eigenvalue into which `τ` is merged), and `J_1, …, J_t` is a `Cl(t)`-structure whose fields `J_ax` lie in the
`τ`-eigenspace at every unit `x`.
TRUST SURFACE: the hypotheses of Theorem E plus the linear orthonormal frame `J_1x, …, J_tx` of the `τ`-eigenspace
(orthonormal because the `J_a` are a Clifford structure; a frame because there are `t` of them). -/
def ThmEFrame (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) : Prop :=
  IsThmEPattern m ∧ Function.Injective ev ∧ (∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) ∧
    IsCliffordStr J ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (R.jacobiMap x) (ev 2)

/-- The setting of Remark 7.2 (lines 787-801) AFTER its normalization "subtracting $\lambda_0R_1$ from $R$ we may take
$\lambda_0=0$": `J` is orthogonal and skew, `c ≠ 0`, `R' = R - cR_J`, both `R` and `R'` are Osserman, and
`J_x(R') = ∑_α μ_α(J_αx)(J_αx)ᵀ` for a `Cl(ν)`-structure `J_1, …, J_ν` with every `μ_α ≠ 0`.
TRUST SURFACE: exactly these nine conditions. -/
def Rem72Hyp (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) : Prop :=
  Jᵀ = -J ∧ Jᵀ * J = 1 ∧ c ≠ 0 ∧ (∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w) ∧ R.IsOsserman ∧
    R'.IsOsserman ∧ IsCliffordStr Jα ∧ (∀ α, μ α ≠ 0) ∧ ∀ x, R'.jacobi x = ∑ α, μ α • jfam (Jα α) x

/-- The setting of Remark 7.2 after "an orthogonal change of the $J_\alpha$ with $\mu_\alpha=\lambda_i$" (lines
817-819): `⟨J_αx, Jx⟩ = d_α|x|²` for constants `d_α`, and inside each block `{α : μ_α = λ}` at most one `d_α` is
nonzero (that `J_α` is the paper's `J^{(i)}`, and `|d_α| = c_i`).
TRUST SURFACE: `Rem72Hyp` plus these two conditions. -/
def Rem72Rot (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) : Prop :=
  Rem72Hyp R R' J c Jα μ ∧ (∀ α x, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) ∧
    ∀ α β, α ≠ β → μ α = μ β → d α = 0 ∨ d β = 0

/-- `J_{ν+1} = J - ∑_α d_αJ_α`, the matrix of `x ↦ π_0(Jx) = Jx - ∑_{i≥1} c_iJ^{(i)}x` (lines 819-820).
TRUST SURFACE: `J` minus its components along the `J_α`. -/
def resid (J : Matrix (Fin 16) (Fin 16) ℝ) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (d : Fin ν → ℝ) :
    Matrix (Fin 16) (Fin 16) ℝ :=
  J - ∑ α, d α • Jα α

/-- `‖π_ℓ(Kx)‖²` for a nonzero value `ℓ` of the `μ_α` and a unit `x`, written in the orthonormal basis
`{J_αx : μ_α = ℓ}` of the eigenspace `E_ℓ(x)` (lines 803-806 and 808-811; row `rem_7_2_eigenspaces`).
TRUST SURFACE: `∑_{μ_α = ℓ} ⟨J_αx, Kx⟩²`. -/
noncomputable def blockSq {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ)
    (K : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) (ℓ : ℝ) : ℝ :=
  ∑ α ∈ Finset.univ.filter (fun α => μ α = ℓ), ((Jα α *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2

/-- `‖π_0(Kx)‖²` for a unit `x` and `Kx ⊥ x`, `π_0` the projection onto `E_0(x) = x^⊥ ∩ (∑_α ℝJ_αx)^⊥` (lines
805-806).
TRUST SURFACE: `|Kx|² - ∑_α ⟨J_αx, Kx⟩²`. -/
def zeroSq {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (K : Matrix (Fin 16) (Fin 16) ℝ) (x : Vec 16) : ℝ :=
  (K *ᵥ x) ⬝ᵥ (K *ᵥ x) - ∑ α, ((Jα α *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2

end Osserman
