/-
Osserman/Paper/Statements.lean — one theorem per claim of the paper (Sections 1-6 so far: Theorem C and its proof)
"The Riemannian Osserman (1990) conjecture" (Dave Goel), Zenodo posting copy:
P013_short.tex (md5 6e130b95; PDF md5 ea4bb54b); "line" = line of
P013_short.tex.
Bodies link to proofs elsewhere; the audit marks any row without a proof as OPEN.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.TwoRoot
import Osserman.Defs.Threshold
import Osserman.Defs.Blocks
import Osserman.Cited.Isoparametric
import Osserman.Proofs.Curv
import Osserman.Proofs.Poly
import Osserman.Proofs.Threshold
import Osserman.Proofs.Threshold2
import Osserman.Proofs.Spectral
import Osserman.Proofs.Sec2
import Osserman.Proofs.Cayley
import Osserman.Proofs.CayleyProducts
import Osserman.Proofs.Lem21
import Osserman.Proofs.OssTop
import Osserman.Proofs.Hopf
import Osserman.Proofs.PlusMinus
import Osserman.Proofs.StdSystem
import Osserman.Proofs.CayleyEigenspaces
import Osserman.Proofs.CayleyJacobi
import Osserman.Proofs.Sec5a
import Osserman.Proofs.CayleyCurvature
import Osserman.Proofs.CayleySectional
import Osserman.Proofs.FKMWitness
import Osserman.Proofs.CayleyIdentify
import Osserman.Proofs.Sec5bCore
import Osserman.Proofs.Sec5b
import Osserman.Proofs.Sec5c
import Osserman.Proofs.ThmC
import Osserman.Proofs.CayleyMonomial

namespace Osserman.Paper

open Osserman Osserman.Cited Matrix MvPolynomial

/-! ## Section 1: notation and Theorem C -/

/-- **§1, Notation** (lines 166-173): the paper's literal "Osserman" (the SET of reduced eigenvalues of `J_x` does not
depend on the unit vector `x`) agrees with the form with multiplicities, so "the multiplicity pattern of `R`" is well
defined. -/
theorem isOsserman_iff_set {n : ℕ} (R : CurvTensor n) : R.IsOsserman ↔ R.IsOssermanSet :=
  Osserman.Proofs.OssTop.isOsserman_iff_set_proved R

/-- **§1, Notation** (lines 175-178): "so that $\Jac_x(R_1)=\Pi(x)$". -/
theorem sec1_jacobi_R1 (n : ℕ) (x y : Vec n) : R1fun y x x = Pi x *ᵥ y :=
  Osserman.Proofs.Curv.sec1_jacobi_R1_proved n x y

/-- **§1, Notation** (line 175): `R_1` is an algebraic curvature tensor. -/
theorem sec1_R1_curv (n : ℕ) : ∃ R : CurvTensor n, ∀ u v w, R.op u v w = R1fun u v w :=
  Osserman.Proofs.Curv.sec1_R1_curv_proved n

/-- **§1, Notation** (lines 190-192): `R_Cay` (Brown–Gray, lines 654-666) is an algebraic curvature tensor. -/
theorem sec1_Rcay_curv : ∃ R : CurvTensor 16, ∀ u v w, R.op u v w = RCayFun u v w :=
  Osserman.Proofs.CayleyCurvature.sec1_Rcay_curv_proved

/-- **§1, Notation** (lines 190-192): "$R_{\rm Cay}$ is the curvature tensor of the Cayley projective plane, normalized
to have sectional curvatures between $1$ and $4$": for orthonormal `u, v`, `K(u,v) = ⟨R(v,u)u, v⟩ ∈ [1, 4]`, and both
ends are attained. -/
theorem sec1_Rcay_sectional :
    (∀ u v : Vec 16, u ⬝ᵥ u = 1 → v ⬝ᵥ v = 1 → u ⬝ᵥ v = 0 → 1 ≤ RCayFun v u u ⬝ᵥ v ∧ RCayFun v u u ⬝ᵥ v ≤ 4) ∧
    (∃ u v : Vec 16, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧ RCayFun v u u ⬝ᵥ v = 1) ∧
    (∃ u v : Vec 16, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧ RCayFun v u u ⬝ᵥ v = 4) :=
  Osserman.Proofs.CayleySectional.sec1_Rcay_sectional_proved

/-- **Theorem C** (thm:A, lines 248-267): an Osserman algebraic curvature tensor on `ℝ^16` with exactly two reduced
eigenvalues, of multiplicities 7 and 8 (named `μ₁` with multiplicity 8 and `μ₂` with multiplicity 7; together they fill
`x^⊥`, so they are all the reduced eigenvalues and `R` is Osserman), has `J_x = μΠ(x) + κA(x)` with `κ ≠ 0` and `A` of
the form (eq:Cl7), (eq:Cl8) or (eq:Cayley); "in suitable orthogonal coordinates" is built into the forms (an orthogonal
conjugate of a `Cl(ν)`-structure or symmetric Clifford system is again one). The first two cases are Clifford; in the
third, `R = (μ - κ/3)R_1 + (κ/3)T^*R_Cay` for some `T ∈ O(16)`. `TwoRootHyp R μ κ` records the paper's names (l. 337):
`μ` has multiplicity 8 and `μ + κ` multiplicity 7 at every unit `x`. -/
theorem thm_C (R : CurvTensor 16)
    (h2 : ∃ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7) :
    ∃ μ κ : ℝ, κ ≠ 0 ∧ TwoRootHyp R μ κ ∧
      ∃ A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ, (∀ x, R.jacobi x = μ • Pi x + κ • A x) ∧
      ((IsFormCl7 A ∧ R.IsClifford) ∨ (IsFormCl8 A ∧ R.IsClifford) ∨
        (IsFormCayley A ∧ ∃ T ∈ Matrix.orthogonalGroup (Fin 16) ℝ,
          ∀ u v w, R.op u v w = (μ - κ / 3) • R1fun u v w + (κ / 3) • pullbackFun T RCayFun u v w)) :=
  Osserman.Proofs.ThmC.thm_C_of_prop_5_2 Osserman.Proofs.Sec5c.prop_5_2_proved R h2

/-- **Theorem C, hypothesis** (lines 248-250): two reduced eigenvalues of multiplicities 8 and 7 make `R` Osserman, with
no other reduced eigenvalue. -/
theorem thm_C_hyp_osserman (R : CurvTensor 16) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (h : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7) :
    R.IsOsserman ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ μ, μ ≠ μ₁ → μ ≠ μ₂ → R.redMult x μ = 0 :=
  Osserman.Proofs.Spectral.thm_C_hyp_osserman_proved R μ₁ μ₂ hne h

/-- **Theorem C, hypothesis, literal reading** (lines 168-173, 248-250): Osserman in the SET sense, with reduced
eigenvalues `μ₁ ≠ μ₂` of multiplicities 8 and 7 at ONE unit `x₀`, has these multiplicities at every unit `x` (the
multiplicity pattern of `R` is well defined); this is the hypothesis `h2` of `thm_C`. -/
theorem thm_C_hyp_literal (R : CurvTensor 16) (hO : R.IsOssermanSet) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (x₀ : Vec 16) (hx₀ : x₀ ⬝ᵥ x₀ = 1) (h₀ : R.redMult x₀ μ₁ = 8 ∧ R.redMult x₀ μ₂ = 7) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7 :=
  Osserman.Proofs.OssTop.thm_C_hyp_literal_proved R hO μ₁ μ₂ hne x₀ hx₀ h₀

/-- **Theorem C, non-vacuity** (Lean-only row; lines 666-668): the hypothesis of Theorem C is met, by `R_Cay` with
`μ = 1`, `κ = 3` (reduced eigenvalues 1 and 4 of multiplicities 8 and 7). -/
theorem thm_C_hyp_nonvacuous : ∃ R : CurvTensor 16, (∀ u v w, R.op u v w = RCayFun u v w) ∧ TwoRootHyp R 1 3 :=
  Osserman.Proofs.CayleySectional.thm_C_hyp_nonvacuous_proved

/-- **Theorem C** (line 264): "The first two cases are Clifford." -/
theorem thm_C_clifford_cases (R : CurvTensor 16) (μ κ : ℝ) (A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : ∀ x, R.jacobi x = μ • Pi x + κ • A x) (hA : IsFormCl7 A ∨ IsFormCl8 A) : R.IsClifford :=
  Osserman.Proofs.OssTop.thm_C_clifford_cases_proved R μ κ A hJ hA

/-- **§1** (lines 278-279), the algebraic core of "a flat space or a space of constant curvature has one Jacobi
eigenvalue": for `R = cR_1` (`c = 0` is flat), `c` is a reduced eigenvalue of multiplicity 15 at every unit `x`. -/
theorem sec1_const_curv_one_eigenvalue (c : ℝ) (R : CurvTensor 16) (hR : ∀ u v w, R.op u v w = c • R1fun u v w) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x c = 15 :=
  Osserman.Proofs.Spectral.sec1_const_curv_one_eigenvalue_proved c R hR

/-! ## Section 2: normalization and the quartic -/

/-- **§2** (lines 337-338): the names `μ` (multiplicity 8) and `κ` (`μ + κ` has multiplicity 7). -/
theorem sec2_names (R : CurvTensor 16)
    (h2 : ∃ μ₁ μ₂ : ℝ, μ₁ ≠ μ₂ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7) :
    ∃ μ κ : ℝ, TwoRootHyp R μ κ :=
  Osserman.Proofs.Spectral.sec2_names_proved R h2

/-- **§2** (lines 339-344), (eq:Aproperties): `A` is a homogeneous quadratic symmetric matrix family with
`A(x)x = 0`, `A(x)² = |x|²A(x)`, `tr A(x) = 7|x|²`. -/
theorem sec2_A_properties (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    IsQuadFamily (Amat R μ κ) ∧ (∀ x, (Amat R μ κ x)ᵀ = Amat R μ κ x) ∧
      ∀ x, Amat R μ κ x *ᵥ x = 0 ∧ Amat R μ κ x * Amat R μ κ x = (x ⬝ᵥ x) • Amat R μ κ x ∧
        (Amat R μ κ x).trace = 7 * (x ⬝ᵥ x) :=
  Osserman.Proofs.Spectral.sec2_A_properties_proved R μ κ h

/-- **§2** (lines 345-352): for a symmetric quadratic family with `A(x)x = 0`, polarization gives
`𝓑(x,y)x = -A(x)y/2`, and `⟨A(x)y,y⟩ = ⟨A(y)x,x⟩`. -/
theorem sec2_polarization {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) (hq : IsQuadFamily A)
    (hs : ∀ x, (A x)ᵀ = A x) (hk : ∀ x, A x *ᵥ x = 0) :
    (∀ x y, Bpol A x y *ᵥ x = -(1 / 2 : ℝ) • (A x *ᵥ y)) ∧ ∀ x y, (A x *ᵥ y) ⬝ᵥ y = (A y *ᵥ x) ⬝ᵥ x :=
  Osserman.Proofs.Curv.sec2_polarization_proved A hq hs hk

/-- **§2** (lines 353-358): Jacobi-family reconstruction [AL2023, Theorem 1], PROVED here: `R_A` of
(eq:reconstruct) is an algebraic curvature tensor whose Jacobi family is `A`. -/
theorem sec2_reconstruct {n : ℕ} (A : Vec n → Matrix (Fin n) (Fin n) ℝ) (hq : IsQuadFamily A)
    (hs : ∀ x, (A x)ᵀ = A x) (hk : ∀ x, A x *ᵥ x = 0) :
    ∃ R : CurvTensor n, (∀ u v w, R.op u v w = RAfun A u v w) ∧ ∀ x, R.jacobi x = A x :=
  Osserman.Proofs.Curv.sec2_reconstruct_proved A hq hs hk

/-- **§2** (lines 359-363): for an algebraic curvature tensor with Jacobi family `J`,
`𝓑(v,w)u = ½(R(u,v)w + R(u,w)v)`, and the first Bianchi identity turns (eq:reconstruct) into `R_J = R`. -/
theorem sec2_determines {n : ℕ} (R : CurvTensor n) :
    (∀ u v w, Bpol R.jacobi v w *ᵥ u = (1 / 2 : ℝ) • (R.op u v w + R.op u w v)) ∧
      ∀ u v w, R.op u v w = RAfun R.jacobi u v w :=
  Osserman.Proofs.Curv.sec2_determines_proved R

/-- **§2** (lines 362-363): "so the Jacobi family determines the tensor". -/
theorem sec2_jacobi_determines {n : ℕ} (R R' : CurvTensor n) (h : ∀ x, R.jacobi x = R'.jacobi x) :
    ∀ u v w, R.op u v w = R'.op u v w :=
  Osserman.Proofs.Curv.sec2_jacobi_determines_proved R R' h

/-- **§2** (lines 365-374), (eq:Qproperties): `Q(x)² = |x|²Q(x)`, `Q(x)x = |x|²x`, `tr Q(x) = 8|x|²`; for `x ≠ 0`,
`Q(x) = |x|²π_{L(x)}` (an orthogonal projection onto `L(x)`) and `dim L(x) = 8`. -/
theorem sec2_Q_properties (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ x, Qmat R μ κ x * Qmat R μ κ x = (x ⬝ᵥ x) • Qmat R μ κ x ∧ Qmat R μ κ x *ᵥ x = (x ⬝ᵥ x) • x ∧
        (Qmat R μ κ x).trace = 8 * (x ⬝ᵥ x)) ∧
      ∀ x, x ≠ 0 → Module.finrank ℝ ↥(Lsub R μ κ x) = 8 ∧
        ∃ Pr : Matrix (Fin 16) (Fin 16) ℝ, Prᵀ = Pr ∧ Pr * Pr = Pr ∧
          LinearMap.range (Matrix.toLin' Pr) = Lsub R μ κ x ∧ Qmat R μ κ x = (x ⬝ᵥ x) • Pr :=
  Osserman.Proofs.Spectral.sec2_Q_properties_proved R μ κ h

/-- **§2** (lines 375-381): `b(x,y) = ⟨Q(x)y,y⟩` is symmetric in `x, y`, vanishes when `x = 0` or `y = 0`, and
`b(x,x) = |x|⁴`. -/
theorem sec2_b_properties (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ x y, (Qmat R μ κ x *ᵥ y) ⬝ᵥ y = (Qmat R μ κ y *ᵥ x) ⬝ᵥ x) ∧ (∀ y, (Qmat R μ κ 0 *ᵥ y) ⬝ᵥ y = 0) ∧
      (∀ x, (Qmat R μ κ x *ᵥ 0) ⬝ᵥ 0 = 0) ∧ ∀ x, (Qmat R μ κ x *ᵥ x) ⬝ᵥ x = (x ⬝ᵥ x) ^ 2 :=
  Osserman.Proofs.Sec2.sec2_b_properties_proved R μ κ h

/-- **§2** (eq:b), second equality (line 378): `b(x,y) = ⟨A(x)y,y⟩ + ⟨x,y⟩²`. -/
theorem sec2_b_expand (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) :
    (Qmat R μ κ x *ᵥ y) ⬝ᵥ y = (Amat R μ κ x *ᵥ y) ⬝ᵥ y + (x ⬝ᵥ y) ^ 2 :=
  Osserman.Proofs.Sec2.sec2_b_expand_proved R μ κ x y

/-- **§2** (lines 383-387): the polynomial `quarticP` is the paper's `F(z) = s² - 8b(x,y)`, `z = (x, y)`. -/
theorem sec2_F_eval (R : CurvTensor 16) (μ κ : ℝ) (x y : Vec 16) :
    eval (Fin.append x y : Vec 32) (quarticP R μ κ) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 - 8 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) :=
  Osserman.Proofs.Sec2.sec2_F_eval_proved R μ κ x y

/-- **§2** (line 386): `F` is a homogeneous quartic. -/
theorem sec2_F_homogeneous (R : CurvTensor 16) (μ κ : ℝ) : (quarticP R μ κ).IsHomogeneous 4 :=
  Osserman.Proofs.Sec2.sec2_F_homogeneous_proved R μ κ

/-- **Lemma 2.1** (lem:quartic, lines 389-395): `|∇F|² = 16s³`, `ΔF = 8s`, and `F` takes both values `1` and `-1` on
`S^31`. -/
theorem lem_2_1 (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    gradSqP (quarticP R μ κ) = 16 * sqP 32 ^ 3 ∧ lapP (quarticP R μ κ) = 8 * sqP 32 ∧
      (∃ z : Vec 32, z ⬝ᵥ z = 1 ∧ eval z (quarticP R μ κ) = 1) ∧
      ∃ z : Vec 32, z ⬝ᵥ z = 1 ∧ eval z (quarticP R μ κ) = -1 :=
  Osserman.Proofs.Lem21.lem_2_1_proved R μ κ h

/-- **Lemma 2.1, proof** (lines 397-403): `∇_y b = 2Q(x)y`, `∇_x b = 2Q(y)x`, `|∇b|² = 4sb`, `⟨z,∇b⟩ = 4b`,
`Δb = 16s`. -/
theorem lem_2_1_b_steps (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ (x y : Vec 16) (j : Fin 16),
        eval (Fin.append x y : Vec 32) (pderiv (Fin.natAdd 16 j) (bP R μ κ)) = 2 * (Qmat R μ κ x *ᵥ y) j ∧
        eval (Fin.append x y : Vec 32) (pderiv (Fin.castAdd 16 j) (bP R μ κ)) = 2 * (Qmat R μ κ y *ᵥ x) j) ∧
      gradSqP (bP R μ κ) = 4 * sqP 32 * bP R μ κ ∧ ∑ i, X i * pderiv i (bP R μ κ) = 4 * bP R μ κ ∧
      lapP (bP R μ κ) = 16 * sqP 32 :=
  Osserman.Proofs.Lem21.lem_2_1_b_steps_proved R μ κ h

/-- **Lemma 2.1, proof** (line 403): `Δb = 2 tr Q(x) + 2 tr Q(y)`. -/
theorem lem_2_1_lap_b_trace (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (x y : Vec 16) :
    eval (Fin.append x y : Vec 32) (lapP (bP R μ κ)) = 2 * (Qmat R μ κ x).trace + 2 * (Qmat R μ κ y).trace :=
  Osserman.Proofs.Lem21.lem_2_1_lap_b_trace_proved R μ κ h x y

/-- **Lemma 2.1, proof** (lines 406-408): `|∇F|² = 16s³ - 64s⟨z,∇b⟩ + 64|∇b|²`. -/
theorem lem_2_1_grad_expand (R : CurvTensor 16) (μ κ : ℝ) :
    gradSqP (quarticP R μ κ) =
      16 * sqP 32 ^ 3 - 64 * sqP 32 * ∑ i, X i * pderiv i (bP R μ κ) + 64 * gradSqP (bP R μ κ) :=
  Osserman.Proofs.Sec2.lem_2_1_grad_expand_proved R μ κ

/-- **Lemma 2.1, proof** (line 410): `Δs² = 4(32 + 2)s = 136s`. -/
theorem lem_2_1_lap_s2 : lapP (sqP 32 ^ 2) = 136 * sqP 32 :=
  Osserman.Proofs.Poly.lem_2_1_lap_s2_proved

/-- **Lemma 2.1, proof** (lines 411-412): `F(x,0) = 1` for unit `x`; `F((x,y)/√2) = -1` for unit `x, y` with
`y ∈ L(x)`. -/
theorem lem_2_1_values (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∀ x : Vec 16, x ⬝ᵥ x = 1 → eval (Fin.append x (0 : Vec 16) : Vec 32) (quarticP R μ κ) = 1) ∧
      ∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 → y ∈ Lsub R μ κ x →
        eval ((Real.sqrt 2)⁻¹ • (Fin.append x y : Vec 32)) (quarticP R μ κ) = -1 :=
  Osserman.Proofs.Lem21.lem_2_1_values_proved R μ κ h

/-! ## Section 3: the classification of isoparametric hypersurfaces (cited result (A), in Osserman/Cited/) -/

/-- **§3** (line 473): "Absorb $U$ into the matrices $P_i$": `F_P ∘ U = F_{UᵀPU}`, and `UᵀP_iU` is again a symmetric
Clifford system. -/
theorem sec3_absorb_U {N k : ℕ} (P : Fin k → Matrix (Fin N) (Fin N) ℝ) (hP : IsSymmCliffordSystem P)
    (U : Matrix (Fin N) (Fin N) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin N) ℝ) :
    IsSymmCliffordSystem (fun i => Uᵀ * P i * U) ∧
      ∀ z, eval (U *ᵥ z) (FKMP P) = eval z (FKMP (fun i => Uᵀ * P i * U)) :=
  Osserman.Proofs.Poly.sec3_absorb_U_proved P hP U hU

/-- **§3** (line 474): "$\Delta F_P=(136-16(m+1))s$" (for a system of at least two matrices; then every `P_i` is
traceless). -/
theorem sec3_lap_FKM (m : ℕ) (hm : 1 ≤ m) (P : Fin (m + 1) → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P) : lapP (FKMP P) = C (136 - 16 * ((m : ℝ) + 1)) * sqP 32 :=
  Osserman.Proofs.Poly.sec3_lap_FKM_proved m hm P hP

/-- **§3** (lines 474-475): comparison with `ΔF = 8s` fixes `ε` and `m`: `ε = 1, m = 7` or `ε = -1, m = 8` (for the
FKM systems, `m ≥ 1`, as the cited result (A) provides; the tex assumes it silently at line 474). -/
theorem sec3_eps_m (m : ℕ) (hm : 1 ≤ m) (P : Fin (m + 1) → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (F : MvPolynomial (Fin 32) ℝ) (hlap : lapP F = 8 * sqP 32)
    (hF : ∀ z, eval z F = ε * eval z (FKMP P)) : (ε = 1 ∧ m = 7) ∨ (ε = -1 ∧ m = 8) :=
  Osserman.Proofs.Sec2.sec3_eps_m_proved m hm P hP ε hε F hlap hF

/-- **§3** (lines 473-482): (eq:plus) or (eq:minus) holds, in the original coordinates `z = (x, y)` (from Lemma 2.1 and
the cited classification (A)). -/
theorem sec3_plus_or_minus (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) :
    (∃ P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P ∧ ∀ x y : Vec 16,
        4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) ∨
      ∃ P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P ∧ ∀ x y : Vec 16,
        4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
          ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2 :=
  Osserman.Proofs.PlusMinus.sec3_plus_or_minus_proved R μ κ h

/-- **§3, non-vacuity of the cited result (A)** (Lean-only row): a symmetric Clifford system of 8 matrices on `ℝ^32`
exists, and its `F_P` satisfies every hypothesis of `isoparametric_quartic_R32`. -/
theorem sec3_axiom_nonvacuous : ∃ P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ, IsSymmCliffordSystem P ∧
    (FKMP P).IsHomogeneous 4 ∧ gradSqP (FKMP P) = 16 * sqP 32 ^ 3 ∧ lapP (FKMP P) = 8 * sqP 32 ∧
    ∃ z w : Vec 32, z ⬝ᵥ z = 1 ∧ w ⬝ᵥ w = 1 ∧ eval z (FKMP P) ≠ eval w (FKMP P) :=
  Osserman.Proofs.FKMWitness.sec3_axiom_nonvacuous_proved

/-! ## Section 4: Lemma 4.1 (quadratic maps between spheres) -/

/-- **Lemma 4.1, proof** (lines 504-505): for unit `a, x`, `⟨H(a)x,x⟩ = ⟨a,h(x)⟩ ≤ 1`, with equality exactly when
`h(x) = a`. -/
theorem lem_4_1_le_one {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) :
    ∀ (a : Fin (m + 1) → ℝ) (x : Vec n), a ⬝ᵥ a = 1 → x ⬝ᵥ x = 1 →
      x ⬝ᵥ (Hcomb H a *ᵥ x) ≤ 1 ∧ (x ⬝ᵥ (Hcomb H a *ᵥ x) = 1 ↔ hvec H x = a) :=
  Osserman.Proofs.Threshold.lem_4_1_le_one_proved H hsym hnorm

/-- **Lemma 4.1, proof** (eq:rankidentity, lines 507-516), without rotating the index space: for unit `x`,
`I - H(h(x)) = 2∑_i (H_ix)(H_ix)ᵀ - 2xxᵀ`; after rotating so that `h(x) = e_0` (then `H_0x = x`) this is the paper's
`I - H_0 = 2∑_{i≥1}(H_ix)(H_ix)ᵀ`. Its quadratic form is the t²-coefficient identity of lines 508-512. -/
theorem lem_4_1_rank_identity {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (x : Vec n) (hx : x ⬝ᵥ x = 1) :
    1 - Hcomb H (hvec H x) = (2 : ℝ) • ∑ i, vecMulVec (H i *ᵥ x) (H i *ᵥ x) - (2 : ℝ) • vecMulVec x x :=
  Osserman.Proofs.Threshold.rank_identity H hsym hnorm x hx

/-- **Lemma 4.1(a)** (lines 496-497): if `a ∈ h(S^{n-1})`, then `I - H(a) ≥ 0`, the fibre over `a` is the unit sphere of
`U_a = ker(I - H(a))`, and `dim U_a ≥ n - m`. -/
theorem lem_4_1_a {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) :
    ∀ a : Fin (m + 1) → ℝ, (∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a) →
      (1 - Hcomb H a).PosSemidef ∧ (∀ x, x ⬝ᵥ x = 1 → (hvec H x = a ↔ (1 - Hcomb H a) *ᵥ x = 0)) ∧
        n - m ≤ Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) :=
  Osserman.Proofs.Threshold.lem_4_1_a_proved H hsym hnorm

/-- **Lemma 4.1, proof** (line 519): the subspaces `U_a, U_b` for distinct values `a ≠ b` meet only at zero. -/
theorem lem_4_1_fibres_disjoint {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (a b : Fin (m + 1) → ℝ)
    (ha : ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a) (hb : ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = b) (hab : a ≠ b) :
    LinearMap.ker (Matrix.toLin' (1 - Hcomb H a)) ⊓ LinearMap.ker (Matrix.toLin' (1 - Hcomb H b)) = ⊥ :=
  Osserman.Proofs.Threshold.lem_4_1_fibres_disjoint_proved H hsym hnorm a b ha hb hab

/-- **Lemma 4.1(b)** (line 498): if `n > 2m`, then `h` is constant on `S^{n-1}`. -/
theorem lem_4_1_b {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : 2 * m < n) :
    ∀ x y : Vec n, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 → hvec H x = hvec H y :=
  Osserman.Proofs.Threshold.lem_4_1_b_proved H hsym hnorm hn

/-- **Lemma 4.1, proof** (lines 523-524): for `n = 2m` and `h` not constant, every value `a` has `dim U_a = m`. -/
theorem lem_4_1_dim_eq {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) (a : Fin (m + 1) → ℝ)
    (ha : ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a) :
    Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) = m :=
  Osserman.Proofs.Threshold2.lem_4_1_dim_eq_proved H hsym hnorm hn hnc a ha

/-- **Lemma 4.1, proof** (lines 524-526), without rotating: for `u ⊥ h(x)`, `H(u)x ⊥ x`, and `u ↦ H(u)x` is
injective there ("H_1x, …, H_mx are independent and perpendicular to x"). -/
theorem lem_4_1_indep {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) (x : Vec n) (hx : x ⬝ᵥ x = 1) :
    ∀ u : Fin (m + 1) → ℝ, u ⬝ᵥ hvec H x = 0 →
      x ⬝ᵥ (Hcomb H u *ᵥ x) = 0 ∧ (Hcomb H u *ᵥ x = 0 → u = 0) :=
  Osserman.Proofs.Threshold2.lem_4_1_indep_proved H hsym hnorm hn hm hnc x hx

/-- **Lemma 4.1, proof** (lines 525-529): for `n = 2m` and `h` not constant, at a unit `x` the differential
`(dh)_x(y) = 2(⟨H_ix,y⟩)_i` has rank `m` on `x^⊥` (stated without the factor 2, which does not change the rank). -/
theorem lem_4_1_dh_rank {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) (x : Vec n) (hx : x ⬝ᵥ x = 1) :
    Module.finrank ℝ ↥((perp x).map (Matrix.toLin' (Matrix.of fun i j => (H i *ᵥ x) j))) = m :=
  Osserman.Proofs.Threshold.lem_4_1_dh_rank_proved H hsym hnorm hn hm hnc x hx

/-- **Lemma 4.1, proof** (line 530): the image of `h` is open in `S^m` and compact (the paper's open-map sentence; the
Lean route proves `lem_4_1_onto` first, and this follows — AUDIT.md, route differences). -/
theorem lem_4_1_image_open {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    IsOpen {a : {a : Fin (m + 1) → ℝ // a ⬝ᵥ a = 1} | ∃ x : Vec n, x ⬝ᵥ x = 1 ∧ hvec H x = a.1} ∧
      IsCompact {a : Fin (m + 1) → ℝ | ∃ x : Vec n, x ⬝ᵥ x = 1 ∧ hvec H x = a} :=
  Osserman.Proofs.Threshold2.lem_4_1_image_open_proved H hsym hnorm hn hm hnc

/-- **Lemma 4.1, proof** (lines 530-531): for `n = 2m`, `m ≥ 1` and `h` not constant, the image of `h` is all of `S^m`. -/
theorem lem_4_1_onto {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ a : Fin (m + 1) → ℝ, a ⬝ᵥ a = 1 → ∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = a :=
  Osserman.Proofs.Threshold.lem_4_1_onto_proved H hsym hnorm hn hm hnc

/-- **Lemma 4.1, proof** (lines 531-533): `a` and `-a` are values; their fibres are the `+1` and `-1` eigenspaces of
`H(a)`, each of dimension `m`. -/
theorem lem_4_1_pm_eigenspaces {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ a : Fin (m + 1) → ℝ, a ⬝ᵥ a = 1 →
      (∃ x, x ⬝ᵥ x = 1 ∧ hvec H x = -a) ∧
      Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 - Hcomb H a))) = m ∧
      Module.finrank ℝ ↥(LinearMap.ker (Matrix.toLin' (1 + Hcomb H a))) = m :=
  Osserman.Proofs.Threshold2.lem_4_1_pm_eigenspaces_proved H hsym hnorm hn hm hnc

/-- **Lemma 4.1, proof** (line 533): "Thus $H(a)^2=I$ for every unit $a$". -/
theorem lem_4_1_sq {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ a : Fin (m + 1) → ℝ, a ⬝ᵥ a = 1 → Hcomb H a * Hcomb H a = 1 :=
  Osserman.Proofs.Threshold.lem_4_1_sq_proved H hsym hnorm hn hm hnc

/-- **Lemma 4.1(c)** (lines 499-500): if `n = 2m`, `m ≥ 1`, and `h` is not constant on `S^{n-1}`, then
`H_iH_j + H_jH_i = 2δ_ij I`. -/
theorem lem_4_1_c {n m : ℕ} (H : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hsym : ∀ i, (H i).IsSymm)
    (hnorm : ∀ x : Vec n, ∑ i, hvec H x i ^ 2 = (x ⬝ᵥ x) ^ 2) (hn : n = 2 * m) (hm : 1 ≤ m)
    (hnc : ∃ x y : Vec n, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y) :
    ∀ i j, H i * H j + H j * H i = if i = j then 2 else 0 :=
  Osserman.Proofs.Threshold.lem_4_1_c_proved H hsym hnorm hn hm hnc

/-! ## Section 5: recovering the original eigenspaces -/

/-- **Proposition 5.1** (prop:plus, lines 539-540): identity (eq:plus) implies (eq:Cl7). -/
theorem prop_5_1 (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    IsFormCl7 (Amat R μ κ) :=
  Osserman.Proofs.Sec5a.prop_5_1_proved R μ κ h P hP hplus

/-! ### Proposition 5.1, the steps of its proof (lines 542-562)
`C_i = blkYX (P i)`, the lower-left block. "Rotating the index space" is stated without coordinates, through the unit
vector `w` (the rotation takes `w` to `e_0`; then `C_0 = C_w` and `C_1, …, C_7` span the `C_u` with `u ⊥ w`). -/

/-- **Prop. 5.1, proof** (lines 542-544): setting `y = 0`, then `x = 0`, in (eq:plus): both diagonal blocks of every
`P_i` are zero. -/
theorem prop_5_1_diag_zero (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∀ i, blkXX (P i) = 0 ∧ blkYY (P i) = 0 :=
  Osserman.Proofs.Sec5a.prop_5_1_diag_zero_proved R μ κ h P hP hplus

/-- **Prop. 5.1, proof** (lines 545-548): `P_i = [[0, C_iᵀ], [C_i, 0]]` and `Q(x) = ∑_{i=0}^7 (C_ix)(C_ix)ᵀ`. -/
theorem prop_5_1_offdiag_Q (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    (∀ i, blkXY (P i) = (blkYX (P i))ᵀ) ∧
      ∀ x : Vec 16, Qmat R μ κ x = ∑ i, vecMulVec (blkYX (P i) *ᵥ x) (blkYX (P i) *ᵥ x) :=
  Osserman.Proofs.Sec5a.prop_5_1_offdiag_Q_proved R μ κ h P hP hplus

/-- **Prop. 5.1, proof** (lines 549-553): the Clifford relations give `C_iᵀC_j + C_jᵀC_i = 2δ_ij I` and
`C_iC_jᵀ + C_jC_iᵀ = 2δ_ij I`. -/
theorem prop_5_1_C_relations (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∀ i j, (blkYX (P i))ᵀ * blkYX (P j) + (blkYX (P j))ᵀ * blkYX (P i) = (if i = j then 2 else 0) ∧
      blkYX (P i) * (blkYX (P j))ᵀ + blkYX (P j) * (blkYX (P i))ᵀ = (if i = j then 2 else 0) :=
  Osserman.Proofs.Sec5a.prop_5_1_C_relations_proved R μ κ h P hP hplus

/-- **Prop. 5.1, proof** (lines 554-556): `Q(x)x = |x|²x` implies `∑_i ⟨C_ix,x⟩² = |x|⁴`. -/
theorem prop_5_1_sum_sq (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∀ x : Vec 16, ∑ i, (x ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 = (x ⬝ᵥ x) ^ 2 :=
  Osserman.Proofs.Sec5a.prop_5_1_sum_sq_proved R μ κ h P hP hplus

/-- **Prop. 5.1, proof** (lines 557-559): Lemma 4.1(b), applied to the symmetric parts of the `C_i` (`n = 16`,
`m = 7`), gives a unit `w ∈ ℝ^8` with `(⟨C_ix,x⟩)_i = |x|²w`. -/
theorem prop_5_1_const_w (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ∃ w : Fin 8 → ℝ, w ⬝ᵥ w = 1 ∧ ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w :=
  Osserman.Proofs.Sec5a.prop_5_1_const_w_proved R μ κ h P hP hplus

/-- **Prop. 5.1, proof** (lines 559-560): "Rotating the index space gives `w = e_0`. Since `C_0` is orthogonal and
`⟨C_0x,x⟩ = |x|²`, we have `C_0 = I`"; without coordinates: `C_w = ∑ w_iC_i` is orthogonal and equals `I`. -/
theorem prop_5_1_C_w (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w) :
    (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 1 ∧
      (∀ x : Vec 16, x ⬝ᵥ ((∑ i, w i • blkYX (P i)) *ᵥ x) = x ⬝ᵥ x) ∧ ∑ i, w i • blkYX (P i) = 1 :=
  Osserman.Proofs.Sec5a.prop_5_1_C_w_proved R μ κ h P hP hplus w hw hcw

/-- **Prop. 5.1, proof** (lines 561-562): "The remaining `C_i` are skew, and their relations become
`C_iC_j + C_jC_i = -2δ_ij I`"; without coordinates: for `u, v ⊥ w`, `C_u` is skew and `C_uC_v + C_vC_u = -2⟨u,v⟩I`. -/
theorem prop_5_1_C_skew (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w) :
    ∀ u v : Fin 8 → ℝ, u ⬝ᵥ w = 0 → v ⬝ᵥ w = 0 →
      (∑ i, u i • blkYX (P i))ᵀ = -(∑ i, u i • blkYX (P i)) ∧
      (∑ i, u i • blkYX (P i)) * (∑ i, v i • blkYX (P i)) + (∑ i, v i • blkYX (P i)) * (∑ i, u i • blkYX (P i)) =
        (-2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) :=
  Osserman.Proofs.Sec5a.prop_5_1_C_skew_proved R μ κ h P hP hplus w hw hcw

/-- **Prop. 5.1, proof** (lines 562-563): "Subtracting `xxᵀ` from `Q(x)` proves the claim"; without choosing the
rotation: for EVERY orthonormal `u_1, …, u_7` in `w^⊥` (the rows 1-7 of any rotation taking `w` to `e_0`), the
`C_{u_j} = ∑_i (u_j)_i C_i` form a `Cl(7)`-structure and `A(x) = ∑_j (C_{u_j}x)(C_{u_j}x)ᵀ` (eq:Cl7). -/
theorem prop_5_1_A_Cl7 (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 8 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hplus : ∀ x y : Vec 16,
      4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 8 → ℝ) (hw : w ⬝ᵥ w = 1) (hcw : ∀ x : Vec 16, (fun i => x ⬝ᵥ (blkYX (P i) *ᵥ x)) = (x ⬝ᵥ x) • w)
    (u : Fin 7 → Fin 8 → ℝ) (hu : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0) (huw : ∀ j, u j ⬝ᵥ w = 0) :
    IsCliffordStr (fun j => ∑ i, u j i • blkYX (P i)) ∧
      ∀ x : Vec 16, Amat R μ κ x =
        ∑ j, vecMulVec ((∑ i, u j i • blkYX (P i)) *ᵥ x) ((∑ i, u j i • blkYX (P i)) *ᵥ x) :=
  Osserman.Proofs.Sec5a.prop_5_1_A_Cl7_proved R μ κ h P hP hplus w hw hcw u hu huw

/-- **Proposition 5.2** (prop:minus, lines 566-567): identity (eq:minus) implies (eq:Cl8) or (eq:Cayley). -/
theorem prop_5_2 (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ) (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ)
    (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    IsFormCl8 (Amat R μ κ) ∨ IsFormCayley (Amat R μ κ) :=
  Osserman.Proofs.Sec5c.prop_5_2_proved R μ κ h P hP hminus

/-! ### Proposition 5.2, the steps of its proof (lines 569-606)
`P_i = [[H_i, B_iᵀ], [B_i, D_i]]` with `H_i = blkXX (P i)`, `B_i = blkYX (P i)`, `D_i = blkYY (P i)`;
`h(x) = (⟨H_ix,x⟩)_i` and `d(y) = (⟨D_iy,y⟩)_i` are `hvec` of these families. "Rotating the index" is stated without
coordinates, through the unit vector `w` with `h(x) = |x|²w`. -/

/-- **Prop. 5.2, proof** (lines 569-576): the block form, and setting `y = 0`, then `x = 0`, in (eq:minus):
`∑_i ⟨H_ix,x⟩² = |x|⁴` and `∑_i ⟨D_iy,y⟩² = |y|⁴`. -/
theorem prop_5_2_blocks (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    (∀ i, blkXY (P i) = (blkYX (P i))ᵀ ∧ (blkXX (P i))ᵀ = blkXX (P i) ∧ (blkYY (P i))ᵀ = blkYY (P i)) ∧
      (∀ x : Vec 16, ∑ i, hvec (fun i => blkXX (P i)) x i ^ 2 = (x ⬝ᵥ x) ^ 2) ∧
      ∀ y : Vec 16, ∑ i, hvec (fun i => blkYY (P i)) y i ^ 2 = (y ⬝ᵥ y) ^ 2 :=
  Osserman.Proofs.Sec5bCore.prop_5_2_blocks_proved R μ κ h P hP hminus

/-- **Prop. 5.2, proof** (lines 578-580): "If `h` is constant on the unit sphere, rotate the index so that `H_0 = I`,
`H_i = 0` for `i ≥ 1`"; without coordinates: `h(x) = |x|²w` for a unit `w`, `H_w = I`, and `H_u = 0` for `u ⊥ w`. -/
theorem prop_5_2_const_rotate (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hconst : ∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
      hvec (fun i => blkXX (P i)) x = hvec (fun i => blkXX (P i)) y) :
    ∃ w : Fin 9 → ℝ, w ⬝ᵥ w = 1 ∧ (∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) ∧
      Hcomb (fun i => blkXX (P i)) w = 1 ∧ ∀ u : Fin 9 → ℝ, u ⬝ᵥ w = 0 → Hcomb (fun i => blkXX (P i)) u = 0 :=
  Osserman.Proofs.Sec5b.prop_5_2_const_rotate_proved R μ κ h P hP hminus hconst

/-- **Prop. 5.2, proof** (lines 580-581): "The upper block of `P_0² = I` gives `B_0 = 0`"; without coordinates:
`B_w = ∑ w_iB_i = 0`. -/
theorem prop_5_2_B_w (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    (∑ i, w i • blkXX (P i)) * (∑ i, w i • blkXX (P i)) + (∑ i, w i • blkYX (P i))ᵀ * (∑ i, w i • blkYX (P i)) = 1 ∧
      ∑ i, w i • blkYX (P i) = 0 :=
  Osserman.Proofs.Sec5b.prop_5_2_B_w_proved R μ κ h P hP hminus w hw hhw

/-- **Prop. 5.2, proof** (line 581): "`tr P_0 = 0`, because `P_0 = -P_1P_0P_1`"; for every combination of the `P_i`. -/
theorem prop_5_2_trace (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P) :
    (∀ i j, i ≠ j → P i = -(P j * P i * P j)) ∧ ∀ v : Fin 9 → ℝ, (∑ i, v i • P i).trace = 0 :=
  Osserman.Proofs.Sec5bCore.prop_5_2_trace_proved P hP

/-- **Prop. 5.2, proof** (line 582): "`D_0² = I` and `tr D_0 = -16`, forcing `D_0 = -I`"; without coordinates, for
`D_w = ∑ w_iD_i`. -/
theorem prop_5_2_D_w (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    (∑ i, w i • blkYY (P i)) * (∑ i, w i • blkYY (P i)) = 1 ∧ (∑ i, w i • blkYY (P i)).trace = -16 ∧
      ∑ i, w i • blkYY (P i) = -1 :=
  Osserman.Proofs.Sec5b.prop_5_2_D_w_proved R μ κ h P hP hminus w hw hhw

/-- **Prop. 5.2, proof** (lines 583-584): "Anticommutation with `P_0 = diag(I,-I)` makes the other eight matrices
off-diagonal"; without coordinates: for `u ⊥ w`, `H_u = 0` and `D_u = 0`. -/
theorem prop_5_2_offdiag (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    ∀ u : Fin 9 → ℝ, u ⬝ᵥ w = 0 → ∑ i, u i • blkXX (P i) = 0 ∧ ∑ i, u i • blkYY (P i) = 0 :=
  Osserman.Proofs.Sec5b.prop_5_2_offdiag_proved R μ κ h P hP hminus w hw hhw

/-- **Prop. 5.2, proof** (lines 584-588): "expanding (eq:minus) yields `Q(x) = |x|²I - ∑_{i=1}^8 (C_ix)(C_ix)ᵀ`"; without
coordinates the sum runs over all nine lower-left blocks `B_i` (`B_w = 0`, and the sum does not change under an
orthogonal change of the index). -/
theorem prop_5_2_Q_Cl8 (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    ∀ x : Vec 16, Qmat R μ κ x =
      (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ i, vecMulVec (blkYX (P i) *ᵥ x) (blkYX (P i) *ᵥ x) :=
  Osserman.Proofs.Sec5b.prop_5_2_Q_Cl8_proved R μ κ h P hP hminus w hw hhw

/-- **Prop. 5.2, proof** (lines 589-591): "`Q(x)x = |x|²x` gives `∑_i ⟨C_ix,x⟩² = 0`. Each `C_i` is therefore skew, and
the Clifford relations become those of a `Cl(8)`-structure"; without coordinates: every `B_i` is skew, and
`B_uB_v + B_vB_u = -2⟨u,v⟩I` for `u, v ⊥ w`. -/
theorem prop_5_2_B_skew (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w) :
    (∀ x : Vec 16, ∑ i, (x ⬝ᵥ (blkYX (P i) *ᵥ x)) ^ 2 = 0) ∧ (∀ i, (blkYX (P i))ᵀ = -blkYX (P i)) ∧
      ∀ u v : Fin 9 → ℝ, u ⬝ᵥ w = 0 → v ⬝ᵥ w = 0 →
        (∑ i, u i • blkYX (P i)) * (∑ i, v i • blkYX (P i)) + (∑ i, v i • blkYX (P i)) * (∑ i, u i • blkYX (P i)) =
          (-2 * (u ⬝ᵥ v)) • (1 : Matrix (Fin 16) (Fin 16) ℝ) :=
  Osserman.Proofs.Sec5b.prop_5_2_B_skew_proved R μ κ h P hP hminus w hw hhw

/-- **Prop. 5.2, proof** (lines 583-592), `h` constant: "Calling their lower blocks `C_1, …, C_8` … This is (eq:Cl8)";
for EVERY orthonormal `u_1, …, u_8` in `w^⊥`, the `B_{u_j}` form a `Cl(8)`-structure and
`A(x) = Π(x) - ∑_j (B_{u_j}x)(B_{u_j}x)ᵀ`. -/
theorem prop_5_2_A_Cl8 (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (w : Fin 9 → ℝ) (hw : w ⬝ᵥ w = 1) (hhw : ∀ x : Vec 16, hvec (fun i => blkXX (P i)) x = (x ⬝ᵥ x) • w)
    (u : Fin 8 → Fin 9 → ℝ) (hu : ∀ j k, u j ⬝ᵥ u k = if j = k then 1 else 0) (huw : ∀ j, u j ⬝ᵥ w = 0) :
    IsCliffordStr (fun j => ∑ i, u j i • blkYX (P i)) ∧
      ∀ x : Vec 16, Amat R μ κ x =
        Pi x - ∑ j, vecMulVec ((∑ i, u j i • blkYX (P i)) *ᵥ x) ((∑ i, u j i • blkYX (P i)) *ᵥ x) :=
  Osserman.Proofs.Sec5b.prop_5_2_A_Cl8_proved R μ κ h P hP hminus w hw hhw u hu huw

/-- **Prop. 5.2, proof** (lines 594-595): "If `h` is not constant, Lemma 4.1(c) makes the `H_i` a symmetric Clifford
system" (`n = 16`, `m = 8`). -/
theorem prop_5_2_H_clifford (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    IsSymmCliffordSystem (fun i => blkXX (P i)) :=
  Osserman.Proofs.Sec5c.prop_5_2_H_clifford_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 595-596): "The equation `H_i² + B_iᵀB_i = I` forces `B_i = 0`." -/
theorem prop_5_2_B_zero (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ i, blkXX (P i) * blkXX (P i) + (blkYX (P i))ᵀ * blkYX (P i) = 1 ∧ blkYX (P i) = 0 :=
  Osserman.Proofs.Sec5c.prop_5_2_B_zero_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 596-599): "Expanding (eq:minus) now gives `b(x,y) = ½(|x|²|y|² - ⟨h(x),d(y)⟩)`." -/
theorem prop_5_2_b_formula (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ x y : Vec 16, (Qmat R μ κ x *ᵥ y) ⬝ᵥ y =
      (1 / 2 : ℝ) * ((x ⬝ᵥ x) * (y ⬝ᵥ y) - hvec (fun i => blkXX (P i)) x ⬝ᵥ hvec (fun i => blkYY (P i)) y) :=
  Osserman.Proofs.Sec5c.prop_5_2_b_formula_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 600-601): "Since `b(x,x) = |x|⁴` and `|h(x)| = |d(x)| = |x|²`, equality in
Cauchy–Schwarz forces `d(x) = -h(x)`." -/
theorem prop_5_2_d_eq (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ x : Vec 16, hvec (fun i => blkYY (P i)) x = -hvec (fun i => blkXX (P i)) x :=
  Osserman.Proofs.Sec5c.prop_5_2_d_eq_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 601-602): "Polarization gives `D_i = -H_i`." -/
theorem prop_5_2_D_eq (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ i, blkYY (P i) = -blkXX (P i) :=
  Osserman.Proofs.Sec5c.prop_5_2_D_eq_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 602-606): "Consequently `Q(x) = ½(|x|²I + ∑_{i=0}^8 ⟨H_ix,x⟩H_i)`, which proves
(eq:Cayley)." -/
theorem prop_5_2_Q_cayley (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    ∀ x : Vec 16, Qmat R μ κ x = (1 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      ∑ i, (x ⬝ᵥ (blkXX (P i) *ᵥ x)) • blkXX (P i)) :=
  Osserman.Proofs.Sec5c.prop_5_2_Q_cayley_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 594-606), `h` not constant: "which proves (eq:Cayley)": the `H_i` are a symmetric
Clifford system and `A(x) = ½(|x|²I + ∑⟨H_ix,x⟩H_i) - xxᵀ` with these `H_i`. -/
theorem prop_5_2_A_cayley (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
      hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) :
    IsSymmCliffordSystem (fun i => blkXX (P i)) ∧ ∀ x : Vec 16, Amat R μ κ x = Acay (fun i => blkXX (P i)) x :=
  Osserman.Proofs.Sec5c.prop_5_2_A_cayley_proved R μ κ h P hP hminus hnc

/-- **Prop. 5.2, proof** (lines 578-606), the case split: if `h` is constant on the unit sphere, `A` has the form
(eq:Cl8); if not, the form (eq:Cayley). -/
theorem prop_5_2_cases (R : CurvTensor 16) (μ κ : ℝ) (h : TwoRootHyp R μ κ)
    (P : Fin 9 → Matrix (Fin 32) (Fin 32) ℝ) (hP : IsSymmCliffordSystem P)
    (hminus : ∀ x y : Vec 16, 4 * ((Qmat R μ κ x *ᵥ y) ⬝ᵥ y) = ((x ⬝ᵥ x) + (y ⬝ᵥ y)) ^ 2 -
      ∑ i, ((Fin.append x y : Vec 32) ⬝ᵥ (P i *ᵥ (Fin.append x y : Vec 32))) ^ 2) :
    ((∀ x y : Vec 16, x ⬝ᵥ x = 1 → y ⬝ᵥ y = 1 →
        hvec (fun i => blkXX (P i)) x = hvec (fun i => blkXX (P i)) y) → IsFormCl8 (Amat R μ κ)) ∧
      ((∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧
        hvec (fun i => blkXX (P i)) x ≠ hvec (fun i => blkXX (P i)) y) → IsFormCayley (Amat R μ κ)) :=
  Osserman.Proofs.Sec5c.prop_5_2_cases_proved R μ κ h P hP hminus

/-! ## Section 6: identification of the Cayley tensor -/

/-- **§6** (lines 648-653): the octonionic `S_0, …, S_8` are linear maps (their matrices act as the formulas), and form
a symmetric Clifford system on `ℝ^16`. -/
theorem sec6_std_system : (∀ i x, stdSys i *ᵥ x = stdSysFun i x) ∧ IsSymmCliffordSystem stdSys :=
  Osserman.Proofs.StdSystem.sec6_std_system_proved

/-- **§6** (lines 611-626): for a symmetric Clifford system `S_0, …, S_8` on `ℝ^16`, the products of 0, 1 and 4
distinct generators (in increasing order) are symmetric and trace-orthogonal, there are `1 + 9 + 126 = 136` of them, they
form a basis of the symmetric matrices (linearly independent and spanning), and `𝒯(Y) = ∑ S_iYS_i` acts on a product of
`k` generators by `(-1)^k(9 - 2k)`. -/
theorem sec6_basis_136 (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    let prod := fun s : Finset (Fin 9) => ((s.sort (· ≤ ·)).map S).prod
    let idx := (Finset.univ : Finset (Finset (Fin 9))).filter fun s => s.card = 0 ∨ s.card = 1 ∨ s.card = 4
    idx.card = 136 ∧ (∀ s ∈ idx, (prod s)ᵀ = prod s) ∧
      (∀ s ∈ idx, ∀ t ∈ idx, s ≠ t → (prod s * prod t).trace = 0) ∧
      LinearIndependent ℝ (fun s : ↥idx => prod s.1) ∧
      Submodule.span ℝ ((fun s => prod s) '' (idx : Set (Finset (Fin 9)))) =
        {M : Matrix (Fin 16) (Fin 16) ℝ | Mᵀ = M} ∧
      ∀ s ∈ idx, ∑ i, S i * prod s * S i = ((-1 : ℝ) ^ s.card * (9 - 2 * (s.card : ℝ))) • prod s :=
  Osserman.Proofs.CayleyProducts.sec6_basis_136_proved S hS

/-- **§6** (lines 615-621 of P013_short.tex): the products of zero, one and four distinct generators are trace-orthogonal because "the
product of two distinct such monomials is, up to sign, a product of $j$ distinct generators with $1\le j\le8$, which
anticommutes with a generator outside it if $j$ is odd and with one inside it if $j$ is even, so has trace zero": for
distinct `s, t` among the 136 index sets, `prod s * prod t = ± prod (s ∆ t)`, `1 ≤ |s ∆ t| ≤ 8`, and it anticommutes
with a generator outside `s ∆ t` (odd size) or inside it (even size). -/
theorem sec6_monomial_product (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) :
    let prod := fun s : Finset (Fin 9) => ((s.sort (· ≤ ·)).map S).prod
    let idx := (Finset.univ : Finset (Finset (Fin 9))).filter fun s => s.card = 0 ∨ s.card = 1 ∨ s.card = 4
    ∀ s ∈ idx, ∀ t ∈ idx, s ≠ t →
      (prod s * prod t = prod (symmDiff s t) ∨ prod s * prod t = -prod (symmDiff s t)) ∧
      1 ≤ (symmDiff s t).card ∧ (symmDiff s t).card ≤ 8 ∧
      (Odd (symmDiff s t).card →
        ∃ i, i ∉ symmDiff s t ∧ S i * (prod s * prod t) = -((prod s * prod t) * S i)) ∧
      (Even (symmDiff s t).card →
        ∃ i, i ∈ symmDiff s t ∧ S i * (prod s * prod t) = -((prod s * prod t) * S i)) :=
  Osserman.Proofs.CayleyMonomial.sec6_monomial_product_proved S hS

/-- **§6** (lines 627-628): "Expanding `xxᵀ = qI/16 + S_h/16 + Y_4`", with `Y_4` a combination of the products of four
generators. -/
theorem sec6_xxT_expansion (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) :
    let prod := fun s : Finset (Fin 9) => ((s.sort (· ≤ ·)).map S).prod
    ∃ c : Finset (Fin 9) → ℝ, vecMulVec x x = (1 / 16 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) + ∑ s ∈ (Finset.univ.filter fun s : Finset (Fin 9) => s.card = 4), c s • prod s :=
  Osserman.Proofs.Hopf.sec6_xxT_expansion_proved S hS x

/-- **§6** (lines 627-634): (eq:HopfM) `Z_x = ∑(S_ix)(S_ix)ᵀ = xxᵀ + ½(qI - S_h)` and `|h| = q` (`q = |x|²`,
`h_i = ⟨S_ix,x⟩`, `S_h = ∑h_iS_i`). -/
theorem sec6_hopf (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) :
    ∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x) = vecMulVec x x + (1 / 2 : ℝ) •
        ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i) ∧
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) ^ 2 = (x ⬝ᵥ x) ^ 2 :=
  Osserman.Proofs.Hopf.sec6_hopf_proved S hS x

/-- **§6** (lines 633-634): contraction of (eq:HopfM) with `x` gives `|h|² = q² + (q² - |h|²)/2` (both sides of the
contracted identity). -/
theorem sec6_hopf_contraction (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) :
    x ⬝ᵥ ((∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x)) *ᵥ x) = ∑ i, (x ⬝ᵥ (S i *ᵥ x)) ^ 2 ∧
      x ⬝ᵥ ((vecMulVec x x + (1 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
        ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i)) *ᵥ x) =
        (x ⬝ᵥ x) ^ 2 + ((x ⬝ᵥ x) ^ 2 - ∑ i, (x ⬝ᵥ (S i *ᵥ x)) ^ 2) / 2 :=
  Osserman.Proofs.Cayley.sec6_hopf_contraction_proved S hS x

/-- **§6** (lines 636-646): with `Q(x) = (qI + S_h)/2` (so `A = Q - xxᵀ` is (eq:Cayley) with `H_i = S_i`) and, for
`x ≠ 0`, `w = h/q`: `S_wx = x`, `S_w` is an orthogonal involution with eigenspaces of dimension 8, `S_ux` lies in its
negative eigenspace for `u ⊥ w`, `Z_x = xxᵀ + qI - Q(x)`, `S_h = 2Q(x) - qI`, `S_h = qS_w` and `Q(x) = (q/2)(I + S_w)`. -/
theorem sec6_Sw (S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S) (x : Vec 16) (hx : x ≠ 0) :
    let q := x ⬝ᵥ x
    let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (S i *ᵥ x)) / q
    let Sw := ∑ i, w i • S i
    let Qx := (1 / 2 : ℝ) • (q • (1 : Matrix (Fin 16) (Fin 16) ℝ) + ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i)
    Acay S x = Qx - vecMulVec x x ∧ Sw *ᵥ x = x ∧ Sw * Sw = 1 ∧ Swᵀ = Sw ∧
      Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' Sw) 1) = 8 ∧
      Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' Sw) (-1)) = 8 ∧
      (∀ u : Fin 9 → ℝ, u ⬝ᵥ w = 0 → Sw *ᵥ ((∑ i, u i • S i) *ᵥ x) = -((∑ i, u i • S i) *ᵥ x)) ∧
      ∑ i, vecMulVec (S i *ᵥ x) (S i *ᵥ x) = vecMulVec x x + q • (1 : Matrix (Fin 16) (Fin 16) ℝ) - Qx ∧
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i = (2 : ℝ) • Qx - q • (1 : Matrix (Fin 16) (Fin 16) ℝ) ∧
      ∑ i, (x ⬝ᵥ (S i *ᵥ x)) • S i = q • Sw ∧ Qx = (q / 2) • (1 + Sw) :=
  Osserman.Proofs.CayleyEigenspaces.sec6_Sw_proved S hS x hx

/-- **§6** (lines 660-668): `J_x(R_𝕆) = 3(xxᵀ - qI) + Z_x - S_h = 4xxᵀ - qI - 3Q(x) = -Π(x) - 3A(x)` (all three
lines of the display), so `R_Cay = -R_𝕆` has Jacobi family `Π + 3A` (`A` = the Cayley family of the standard system),
with reduced eigenvalues `1` and `4` of multiplicities eight and seven. -/
theorem sec6_jacobi_Rcay :
    (∀ x y : Vec 16, ROctFun y x x = (3 : ℝ) • ((vecMulVec x x - (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ)) *ᵥ y) +
      (∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)) *ᵥ y - (∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i) *ᵥ y) ∧
    (∀ x y : Vec 16, ROctFun y x x = ((4 : ℝ) • vecMulVec x x - (x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) -
      (3 / 2 : ℝ) • ((x ⬝ᵥ x) • (1 : Matrix (Fin 16) (Fin 16) ℝ) + ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) • stdSys i)) *ᵥ y) ∧
    (∀ x y : Vec 16, ROctFun y x x = -((Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y)) ∧
      (∀ x y : Vec 16, RCayFun y x x = (Pi x + (3 : ℝ) • Acay stdSys x) *ᵥ y) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) 1 ⊓ perp x) = 8 ∧
        Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (Pi x + (3 : ℝ) • Acay stdSys x)) 4 ⊓ perp x) = 7 :=
  Osserman.Proofs.CayleyJacobi.sec6_jacobi_Rcay_proved

/-- **§6** (line 676): "Changing a generator's sign leaves $\ip{S_ix}xS_i$ unchanged." -/
theorem sec6_sign_change (H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 9) :
    Acay (Function.update H j (-H j)) = Acay H :=
  Osserman.Proofs.Cayley.sec6_sign_change_proved H j

/-- **§6** (lines 677-680): every family (eq:Cayley) is the standard Cayley family up to `T ∈ O(16)`:
`3A(x) = J_x(T^*R_Cay) - Π(x)`. -/
theorem sec6_identify (H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hH : IsSymmCliffordSystem H) :
    ∃ T ∈ Matrix.orthogonalGroup (Fin 16) ℝ, ∀ x y : Vec 16,
      (3 : ℝ) • (Acay H x *ᵥ y) = pullbackFun T RCayFun y x x - Pi x *ᵥ y :=
  Osserman.Proofs.CayleyIdentify.sec6_identify_proved H hH

/-- **§6** (line 681, used implicitly): the pull-back `T^*R` of an algebraic curvature tensor by `T ∈ O(16)` is an
algebraic curvature tensor (so "the Jacobi family determines the tensor" applies to `T^*R_Cay`). -/
theorem pullback_curv (R : CurvTensor 16) (T : Matrix (Fin 16) (Fin 16) ℝ)
    (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ) :
    ∃ R' : CurvTensor 16, ∀ u v w, R'.op u v w = pullbackFun T (fun a b c => R.op a b c) u v w :=
  Osserman.Proofs.Cayley.pullback_curv_proved R T hT

end Osserman.Paper
