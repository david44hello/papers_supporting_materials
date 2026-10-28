/-
Osserman/Defs/SixPieces.lean — the objects of the six pieces of paper 013 that are formalized beside Sections 2-8:
Setting (T) and Lemmas 12.1, 12.4, 12.5, 12.6 (sec_common_lemmas.tex), the anisotropy step of the proof of Theorem G
(sec_polynomial_gram.tex l. 234-270) and Lemma 24.5 (sec_singular_integral_extraction.tex l. 155-169).
`orthSub` (the orthogonal complement of a subspace) lives in Defs/ThreeRoot.lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.ThreeRoot

namespace Osserman

open Matrix

/-! ## New definitions -/

/-- **Setting (T)** (cl l. 11-19, eq. (12.1)). TRUST SURFACE: `V = ℝ^16 = E ⊕ E^⊥` with `dim E = 8`; `B` is a real
linear map from `ℝ^8` to the `16 × 8` matrices (`Hom(ℝ^8, V)`) with `rank B(a) = 8` for every real `a ≠ 0`; `L` is a
linear isomorphism of `ℝ^8` onto `E` (injective `16 × 8` matrix with image `E`); `K` is an isometry of `ℝ^8` onto `E^⊥`
(`KᵀK = I`, image `E^⊥`); `g₀ ≠ 0`; and for all `a`: `B(a)g₀ = -La` and `KᵀB(a)` is skew-symmetric. -/
def SettingT (B : Vec 8 → Matrix (Fin 16) (Fin 8) ℝ) (E : Submodule ℝ (Vec 16)) (L K : Matrix (Fin 16) (Fin 8) ℝ)
    (g0 : Vec 8) : Prop :=
  Module.finrank ℝ E = 8 ∧ IsLinearMap ℝ B ∧ (∀ a : Vec 8, a ≠ 0 → (B a).rank = 8) ∧
    LinearMap.ker (Matrix.toLin' L) = ⊥ ∧ LinearMap.range (Matrix.toLin' L) = E ∧
    Kᵀ * K = 1 ∧ LinearMap.range (Matrix.toLin' K) = orthSub E ∧ g0 ≠ 0 ∧
    ∀ a : Vec 8, B a *ᵥ g0 = -(L *ᵥ a) ∧ (Kᵀ * B a)ᵀ = -(Kᵀ * B a)

/-- The Pfaffian `A₁₂A₃₄ - A₁₃A₂₄ + A₁₄A₂₃` of a `4 × 4` matrix (cl l. 84; indices shifted to `0, …, 3`). TRUST
SURFACE: this exact quadratic polynomial in the entries. -/
def pf4 (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- The skew `4 × 4` matrix with upper entries `(A₀₁, A₀₂, A₀₃, A₁₂, A₁₃, A₂₃) = (y₀, …, y₅)` (Lean-only coordinates
for "the six entries", cl l. 84-85). TRUST SURFACE: a linear bijection of `ℝ^6` onto the skew `4 × 4` matrices (the
row `lem_12_4_signature` states that every skew matrix is of this form). -/
def skew4 (y : Fin 6 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, y 0, y 1, y 2; -y 0, 0, y 3, y 4; -y 1, -y 3, 0, y 5; -y 2, -y 4, -y 5, 0]

/-- The normal form `y₀² + y₁² + y₂² - y₃² - y₄² - y₅²` of a real quadratic form of signature `(3,3)` (cl l. 85).
TRUST SURFACE: "a form of signature `(3,3)`" means a form that becomes this one after an invertible linear change of
the six variables. -/
def sig33 (y : Fin 6 → ℝ) : ℝ := y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 - y 3 ^ 2 - y 4 ^ 2 - y 5 ^ 2

/-- A symmetric bilinear form on `K²` (given by its Gram matrix) is hyperbolic (sie l. 158, "hyperbolic over
`Frac(T)`"). TRUST SURFACE: in some basis of `K²` its Gram matrix is the hyperbolic plane `[[0,1],[1,0]]`. -/
def IsHyperbolic2 {K : Type*} [Field K] (Bm : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ P : Matrix (Fin 2) (Fin 2) K, IsUnit P.det ∧ Pᵀ * Bm * P = !![0, 1; 1, 0]

/-- The field `𝔽 = ℝ(y₁, …, y₁₅)` (pg l. 240-241; the variables are `y_0, …, y_14` here). TRUST SURFACE: the field of
fractions of the real polynomial ring in fifteen variables. -/
abbrev RatF15 := FractionRing (MvPolynomial (Fin 15) ℝ)

/-- The real constants inside `𝔽`. TRUST SURFACE: `r ↦ r/1`, the constant rational function. -/
noncomputable def ofRealF : ℝ →+* RatF15 := (algebraMap (MvPolynomial (Fin 15) ℝ) RatF15).comp MvPolynomial.C

/-- The coordinate `y_i ∈ 𝔽` (pg l. 239-240). TRUST SURFACE: the `i`-th variable as a rational function. -/
noncomputable def yF (i : Fin 15) : RatF15 := algebraMap (MvPolynomial (Fin 15) ℝ) RatF15 (MvPolynomial.X i)

/-- `d = ∑ y_i²` (pg l. 241). TRUST SURFACE: the sum of the squares of the fifteen variables, in `𝔽`. -/
noncomputable def dF : RatF15 := ∑ i, yF i ^ 2

/-- The shifted Jacobi matrix `J_z - μ₀Π(z)` at a vector `z` whose coordinates lie in a commutative ring `A` with a
ring map `φ : ℝ → A` (used for `z = sX + Y` with polynomial / rational coordinates, pg l. 208, 238-250). TRUST SURFACE:
entry `(j,k)` is `∑_{a,b} z_a z_b R(e_k,e_a,e_b)_j - μ₀(δ_jk ∑_a z_a² - z_j z_k)`, the entries of `J_x` and `Π(x)` as
quadratic polynomials (as `jacEntryP` in Defs/Poly.lean); for `A = ℝ` it is `R.jacobi z - μ₀ • Pi z` (row
`jacAlg_real`). -/
noncomputable def jacAlg (R : CurvTensor 16) (μ0 : ℝ) {A : Type*} [CommRing A] (φ : ℝ →+* A) (z : Fin 16 → A) :
    Matrix (Fin 16) (Fin 16) A :=
  Matrix.of fun j k => (∑ a, ∑ b, z a * z b * φ (R.op (Pi.single k 1) (Pi.single a 1) (Pi.single b 1) j)) -
    φ μ0 * ((if j = k then ∑ a, z a ^ 2 else 0) - z j * z k)

/-- The point `z = sX + Y`, `Y = ∑ y_i f_i`, with `s` the polynomial variable over `𝔽` (pg l. 238-241: "coordinates
`Y = (y_1, …, y_15)` on `X^⊥`"). TRUST SURFACE: coordinate `a` of `z` is `X_a s + ∑_i y_i (f_i)_a` in `𝔽[s]`. -/
noncomputable def pointS (Xa : Vec 16) (f : Fin 15 → Vec 16) : Fin 16 → Polynomial RatF15 :=
  fun a => Polynomial.C (ofRealF (Xa a)) * Polynomial.X + Polynomial.C (∑ i, yF i * ofRealF (f i a))

/-- The coherent factor `M_{sX+Y} = sM_X + M_Y` (pg l. 26-28, 208, 231) as a matrix over `𝔽[s]`. TRUST SURFACE: `s`
times the real frame `M_X` plus the rational partner `M_Y`. -/
noncomputable def factorS {ν : ℕ} (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15) :
    Matrix (Fin 16) (Fin ν) (Polynomial RatF15) :=
  (Polynomial.X : Polynomial RatF15) • MX.map (Polynomial.C.comp ofRealF) + MY.map Polynomial.C

/-- The output of **Lemma 9.3** (pg l. 203-209) for the tensor shifted by `μ₀`, in the coordinates of pg l. 239-241.
TRUST SURFACE: `X` is a real unit vector; `f_0, …, f_14` is an orthonormal basis of `X^⊥` (the coordinates `y_i`);
`M_X` is an orthonormal eigenframe (`M_XᵀM_X = I`, `J'_X = M_XΛM_Xᵀ` — also the `s²`-coefficient of the identity
below, kept because it is the tex's "eigenframe"); `M_Y` is a matrix of rational functions of
`y` with `J'_{sX+Y} = (sM_X+M_Y)Λ(sM_X+M_Y)ᵀ` as an identity over `𝔽[s]` (a rational identity in `(s, Y)`). The
homogeneity of `M_Y` is NOT included (no row below uses it). -/
def IsRationalPartner (R : CurvTensor 16) (μ0 : ℝ) {ν : ℕ} (Λ : Matrix (Fin ν) (Fin ν) ℝ) (Xa : Vec 16)
    (f : Fin 15 → Vec 16) (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15) : Prop :=
  Xa ⬝ᵥ Xa = 1 ∧ (∀ i, Xa ⬝ᵥ f i = 0) ∧ (∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) ∧ MXᵀ * MX = 1 ∧
    R.jacobi Xa - μ0 • Pi Xa = MX * Λ * MXᵀ ∧
    jacAlg R μ0 (Polynomial.C.comp ofRealF) (pointS Xa f) =
      factorS MX MY * Λ.map (Polynomial.C.comp ofRealF) * (factorS MX MY)ᵀ

/-- `Φ₁ = M_XᵀM_Y + M_YᵀM_X` (pg l. 242). TRUST SURFACE: this matrix over `𝔽`. -/
noncomputable def Phi1 {ν : ℕ} (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15) :
    Matrix (Fin ν) (Fin ν) RatF15 :=
  (MX.map ofRealF)ᵀ * MY + MYᵀ * MX.map ofRealF

/-- `Φ₀ = M_YᵀM_Y` (pg l. 242). TRUST SURFACE: this matrix over `𝔽`. -/
noncomputable def Phi0 {ν : ℕ} (MY : Matrix (Fin 16) (Fin ν) RatF15) : Matrix (Fin ν) (Fin ν) RatF15 := MYᵀ * MY

/-- `G(s) = s²I + sΦ₁ + Φ₀` (pg l. 241) over `𝔽[s]`. TRUST SURFACE: this quadratic matrix polynomial in `s`. -/
noncomputable def GramS {ν : ℕ} (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) : Matrix (Fin ν) (Fin ν) (Polynomial RatF15) :=
  (Polynomial.X ^ 2 : Polynomial RatF15) • (1 : Matrix (Fin ν) (Fin ν) (Polynomial RatF15)) +
    (Polynomial.X : Polynomial RatF15) • Φ1.map Polynomial.C + Φ0.map Polynomial.C

/-- `G(α) = α²I + αΦ₁ + Φ₀` over a field `𝔼 ⊇ 𝔽` (pg l. 258-259, "at `s = α`"). TRUST SURFACE: `G(s)` evaluated at
`s = α`. -/
noncomputable def GramAt {𝔼 : Type*} [Field 𝔼] [Algebra RatF15 𝔼] {ν : ℕ} (α : 𝔼) (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) :
    Matrix (Fin ν) (Fin ν) 𝔼 :=
  α ^ 2 • (1 : Matrix (Fin ν) (Fin ν) 𝔼) + α • Φ1.map (algebraMap RatF15 𝔼) + Φ0.map (algebraMap RatF15 𝔼)

/-- Equation (9.3) (eq:spectralpencil, pg l. 246-249) for `Λ = diag(μ)`: `det(tI - ΛG(s)) = ∏_i (t - (s² + d)μ_i)` in
`𝔽[s,t] = (𝔽[s])[t]`. TRUST SURFACE: Mathlib's `charpoly M = det(tI - M)` of `ΛG(s)` over `𝔽[s]` equals this product. -/
def SpectralPencil {ν : ℕ} (μ : Fin ν → ℝ) (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) : Prop :=
  ((diagonal μ).map (Polynomial.C.comp ofRealF) * GramS Φ1 Φ0).charpoly =
    ∏ i, (Polynomial.X - Polynomial.C ((Polynomial.X ^ 2 + Polynomial.C dF) * Polynomial.C (ofRealF (μ i))))

/-- `μ₀` is the smallest reduced eigenvalue (pg l. 6-7). TRUST SURFACE: at every unit `x`, every reduced eigenvalue
`μ` of `J_x` (multiplicity `> 0`) satisfies `μ₀ ≤ μ`. -/
def IsSmallestRed (R : CurvTensor 16) (μ0 : ℝ) : Prop :=
  ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ μ : ℝ, 0 < R.redMult x μ → μ0 ≤ μ

/-- `μ₀` is the largest reduced eigenvalue (pg l. 6-7). TRUST SURFACE: as `IsSmallestRed` with `μ ≤ μ₀`. -/
def IsLargestRed (R : CurvTensor 16) (μ0 : ℝ) : Prop :=
  ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ μ : ℝ, 0 < R.redMult x μ → μ ≤ μ0

/-- The hypothesis on `μ₀` of Theorem G (pg l. 6-7): "an eigenvalue of multiplicity seven or eight is the smallest or
the largest reduced eigenvalue". TRUST SURFACE: `μ₀` has reduced multiplicity `m ∈ {7, 8}` at every unit `x`, and it
is the smallest or the largest reduced eigenvalue. -/
def IsExtremeSevenEight (R : CurvTensor 16) (μ0 : ℝ) : Prop :=
  (∃ m : ℕ, (m = 7 ∨ m = 8) ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ0 = m) ∧ (IsSmallestRed R μ0 ∨ IsLargestRed R μ0)

end Osserman
