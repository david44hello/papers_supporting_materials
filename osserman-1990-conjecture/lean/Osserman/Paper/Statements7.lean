/-
Osserman/Paper/Statements7.lean — one theorem per claim of Section 7 of paper 013 ("Tensors with three eigenvalues,
and Jacobi-proportionality", P013_short.tex l. 689-841) and of Corollary D and Theorem E (l. 295-311), the Zenodo posting copy
P013_short.tex (md5 6e130b95; PDF md5 ea4bb54b); "line" = line of that file.
Bodies link to proofs elsewhere; the audit marks any row without a proof as OPEN.
Results of OTHER papers are NOT rows here: they are cited statements in Osserman/Cited/Nik2006.lean (Nikolayevsky,
Lemmas 3.1 and 3.11) and Osserman/Cited/Andrejic.lean (Andrejić, Theorem 5), checked against their sources;
rows that use them are PROVED-FROM-CITED.
Rule (review a2-six SHOULD-3): no conjunct of a row may be provable only ex falso from another conjunct.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Paper.Statements
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.OctonionFacts
import Osserman.Proofs.OctonionNucleus
import Osserman.Proofs.OctonionQuaternion
import Osserman.Proofs.HurwitzRadon
import Osserman.Proofs.Lemma71Algebra
import Osserman.Proofs.Lemma71Coordinates
import Osserman.Proofs.Lemma71Geometry
import Osserman.Proofs.Lemma71Blocks
import Osserman.Proofs.ThmECayley
import Osserman.Proofs.ThmEElementary
import Osserman.Proofs.ThmEFrames
import Osserman.Proofs.ThmEFrameConstruction
import Osserman.Proofs.ThmE
import Osserman.Proofs.CorD
import Osserman.Proofs.CorDNonvacuous
import Osserman.Proofs.Rem72a
import Osserman.Proofs.ThmEClosed
import Osserman.Proofs.Rem72b
import Osserman.Proofs.Rem72c
import Osserman.Proofs.Rem72d
import Osserman.Proofs.Rem72e

namespace Osserman.Paper

open Osserman Osserman.Cited Matrix MvPolynomial

/-! ## Statements of Corollary D and Theorem E (lines 295-311) -/

/-- **Theorem E** (thm:D, lines 307-311 of P013_short.tex): "Let $R$ be an Osserman algebraic curvature tensor on $\R^{16}$ with exactly
three reduced eigenvalues. If their multiplicities are $(7,7,1)$, $(8,6,1)$, $(8,5,2)$ or $(7,6,2)$, then $R$ is
Clifford." The pattern hypothesis implies "Osserman" and "exactly three" (row `hasPattern_osserman`), so neither is
repeated. Also row S7.42 ("This proves the theorem", line 784). -/
theorem thm_E (R : CurvTensor 16)
    (h3 : HasPattern R ![7, 7, 1] ∨ HasPattern R ![8, 6, 1] ∨ HasPattern R ![8, 5, 2] ∨ HasPattern R ![7, 6, 2]) :
    R.IsClifford :=
  Osserman.Proofs.ThmEClosed.thm_E_of_lem_nik_3_2_1 Osserman.Proofs.Rem72c.lem_nik_3_2_1_proved R h3

/-- **Corollary D** (cor:C, lines 295-299 of P013_short.tex): "Every Jacobi-proportional Riemannian Osserman algebraic curvature tensor
on $\R^{16}$ is Clifford or a linear combination of $R_1$ and an orthogonal conjugate of $R_{\rm Cay}$" (Riemannian =
the Euclidean dot product of `Vec 16`). Stated after `thm_E` (v0.81), because its proof uses Theorem E. -/
theorem cor_D (R : CurvTensor 16) (hO : R.IsOsserman) (hJP : IsJacobiProportional R) :
    R.IsClifford ∨ IsCayleyType R :=
  Osserman.Proofs.CorD.cor_D_proved thm_E R hO hJP

/-- **Patterns, hypothesis** (Lean-only row; lines 168-173 and 307-308 of P013_short.tex): a pattern whose multiplicities add up to
`n - 1 = dim x^⊥` makes `R` Osserman, and its values are ALL the reduced eigenvalues ("exactly `k`"). -/
theorem hasPattern_osserman {n k : ℕ} (R : CurvTensor n) (m : Fin k → ℕ) (hsum : ∑ i, m i + 1 = n)
    (hR : HasPattern R m) :
    R.IsOsserman ∧ ∃ ev : Fin k → ℝ, Function.Injective ev ∧
      (∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) ∧
      ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ μ : ℝ, (∀ i, μ ≠ ev i) → R.redMult x μ = 0 :=
  Osserman.Proofs.CorD.hasPattern_osserman_proved R m hsum hR

/-- **Patterns, literal reading** (Lean-only row; lines 168-173 of P013_short.tex): Osserman in the SET sense with distinct reduced
eigenvalues of multiplicities `m` at ONE unit `x₀` has the pattern `m` (as `thm_C_hyp_literal` for `(8,7)`). -/
theorem hasPattern_of_literal {k : ℕ} (R : CurvTensor 16) (hO : R.IsOssermanSet) (m : Fin k → ℕ)
    (ev : Fin k → ℝ) (hev : Function.Injective ev) (x₀ : Vec 16) (hx₀ : x₀ ⬝ᵥ x₀ = 1)
    (h₀ : ∀ i, R.redMult x₀ (ev i) = m i) : HasPattern R m :=
  Osserman.Proofs.CorD.hasPattern_of_literal_proved R hO m ev hev x₀ hx₀ h₀

/-! ## Section 7, preamble (lines 691-694): `E(x)` and `N(x)` for the standard Cayley family -/

/-- **§7, preamble** (lines 691-694 of P013_short.tex, with line 369 and lines 636-642), (hidden): the standard Cayley family
`A = Acay stdSys` satisfies (eq:Aproperties): a homogeneous quadratic symmetric family with `A(x)x = 0`,
`A(x)² = |x|²A(x)` and `tr A(x) = 7|x|²` (so §2's "$Q(x)=\norm{x}^2\pi_{L(x)}$ and $\dim L(x)=8$" applies to it). -/
theorem sec7_cayley_A_props :
    IsQuadFamily (Acay stdSys) ∧ (∀ x, (Acay stdSys x)ᵀ = Acay stdSys x) ∧
      ∀ x, Acay stdSys x *ᵥ x = 0 ∧ Acay stdSys x * Acay stdSys x = (x ⬝ᵥ x) • Acay stdSys x ∧
        (Acay stdSys x).trace = 7 * (x ⬝ᵥ x) :=
  Osserman.Proofs.Lemma71Geometry.sec7_cayley_A_props_proved

/-- **§7, preamble** (lines 691-694 of P013_short.tex, with lines 636-642), (hidden): for `x ≠ 0`, `L(x) = Im Q(x)` with
`Q(x) = A(x) + xxᵀ`; `L(x)` is the `+1`-eigenspace of `S_w = ∑ w_iS_i`, `w = h(x)/|x|²`; it has dimension 8 and
contains `x`. -/
theorem sec7_L_eigenspace (x : Vec 16) (hx : x ≠ 0) :
    let w : Fin 9 → ℝ := fun i => (x ⬝ᵥ (stdSys i *ᵥ x)) / (x ⬝ᵥ x)
    Lstd x = LinearMap.range (Matrix.toLin' (Acay stdSys x + vecMulVec x x)) ∧
      Lstd x = Module.End.eigenspace (Matrix.toLin' (∑ i, w i • stdSys i)) 1 ∧
      Module.finrank ℝ ↥(Lstd x) = 8 ∧ x ∈ Lstd x :=
  Osserman.Proofs.Lemma71Geometry.sec7_L_eigenspace_proved x hx

/-- **§7, preamble** (lines 691-694 of P013_short.tex): "let $E(x)=L(x)\cap x^\perp$ and $N(x)=L(x)^\perp$, of dimensions seven and
eight" (for `x ≠ 0`). -/
theorem sec7_EN_dims (x : Vec 16) (hx : x ≠ 0) :
    Module.finrank ℝ ↥(Estd x) = 7 ∧ Module.finrank ℝ ↥(Nstd x) = 8 :=
  Osserman.Proofs.Lemma71Geometry.sec7_EN_dims_proved x hx

/-! ## Lemma 7.1 (lem:nofield, lines 696-736) -/

/-- **Lemma 7.1, first sentence** (lem:nofield, lines 696-697 of P013_short.tex): "There is no nonzero linear map $K$ with $Kx\in E(x)$
for every $x\ne0$." -/
theorem lem_7_1_a (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Estd x) : K = 0 :=
  Osserman.Proofs.Lemma71Blocks.lem_7_1_a_proved K hK

/-- **Lemma 7.1, second sentence** (lem:nofield, line 698 of P013_short.tex): "There is also no nonzero linear map $K$ with
$Kx\in N(x)$ for every $x\ne0$." -/
theorem lem_7_1_b (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x) : K = 0 :=
  Osserman.Proofs.Lemma71Blocks.lem_7_1_b_proved K hK

/-- **Lemma 7.1, proof** (lines 701-702 of P013_short.tex), (hidden): "the orthogonal coordinate change
$(x_1,x_2)\mapsto(x_1,\overline{x_2})$": its matrix acts as the formula, is orthogonal and is an involution, because
octonion conjugation preserves the dot product. -/
theorem lem_7_1_conj_change :
    (∀ x : Vec 16, conjChange *ᵥ x = conjChangeFun x) ∧ conjChange ∈ Matrix.orthogonalGroup (Fin 16) ℝ ∧
      conjChange * conjChange = 1 ∧ ∀ a b : Vec 8, oconj a ⬝ᵥ oconj b = a ⬝ᵥ b :=
  Osserman.Proofs.Lemma71Coordinates.lem_7_1_conj_change_proved

/-- **Lemma 7.1, proof** (lines 709-711 of P013_short.tex), (hidden): the alternativity identity `a(āu) = |a|²u` used to check the
eigenspaces of `S_{(w_0,a)}`. -/
theorem oct_left_alt (a u : Vec 8) : omul a (omul (oconj a) u) = (a ⬝ᵥ a) • u :=
  Osserman.Proofs.OctonionFacts.oct_left_alt_proved a u

/-- **Lemma 7.1, proof** (lines 707-711 of P013_short.tex), (hidden): in the new coordinates `y = (u, v)`,
`S_{(w_0,a)}(u,v) = (w_0u + av, āu - w_0v)`. -/
theorem lem_7_1_S_new_coords (w0 : ℝ) (a : Vec 8) (y : Vec 16) :
    conjChange *ᵥ (stdComb w0 a *ᵥ (conjChange *ᵥ y)) =
      octPair (w0 • oct1 y + omul a (oct2 y)) (omul (oconj a) (oct1 y) - w0 • oct2 y) :=
  Osserman.Proofs.Lemma71Coordinates.lem_7_1_S_new_coords_proved w0 a y

/-- **Lemma 7.1, proof** (lines 707-711 of P013_short.tex): for `w_0² + |a|² = 1`, "Its positive eigenspace becomes $\mathcal C_\omega$
with $\omega=\overline a/(1+w_0)$ when $w_0\ne-1$, and becomes $\mathcal C_\infty$ otherwise" (the `+1`-eigenspace of
`S_{(w_0,a)}`, written in the new coordinates `y` with `x = conjChange y`). -/
theorem lem_7_1_eigenspace_line (w0 : ℝ) (a : Vec 8) (hw : w0 ^ 2 + a ⬝ᵥ a = 1) :
    (w0 ≠ -1 → {y : Vec 16 | stdComb w0 a *ᵥ (conjChange *ᵥ y) = conjChange *ᵥ y} =
        cayLine ((1 + w0)⁻¹ • oconj a)) ∧
      (w0 = -1 → {y : Vec 16 | stdComb w0 a *ᵥ (conjChange *ᵥ y) = conjChange *ᵥ y} = cayLineInf) :=
  Osserman.Proofs.Lemma71Coordinates.lem_7_1_eigenspace_line_proved w0 a hw

/-- **Lemma 7.1, proof** (lines 711-712 of P013_short.tex): "$\OCT$ has no zero divisors". -/
theorem oct_no_zero_divisors (a b : Vec 8) (h : omul a b = 0) : a = 0 ∨ b = 0 :=
  Osserman.Proofs.OctonionFacts.oct_no_zero_divisors_proved a b h

/-- **Lemma 7.1, proof** (lines 711-712 of P013_short.tex): "Distinct lines among the $\mathcal C_\omega$ and $\mathcal C_\infty$ meet
only in $0$". -/
theorem cayley_lines_meet_zero :
    (∀ ω ω' : Vec 8, ω ≠ ω' → cayLine ω ∩ cayLine ω' = {0}) ∧ ∀ ω : Vec 8, cayLine ω ∩ cayLineInf = {0} :=
  Osserman.Proofs.OctonionNucleus.cayley_lines_meet_zero_proved

/-- **Lemma 7.1, proof** (lines 712-713 of P013_short.tex): "$x\in L(x)$; so for $x$ in such a line, $L(x)$ is that line" (for
`x ≠ 0`; `L` read in the new coordinates: `{z | conjChange z ∈ L(conjChange y)}`). -/
theorem lem_7_1_L_line :
    (∀ x : Vec 16, x ∈ Lstd x) ∧
      (∀ (ω : Vec 8) (y : Vec 16), y ≠ 0 → y ∈ cayLine ω →
        {z : Vec 16 | conjChange *ᵥ z ∈ Lstd (conjChange *ᵥ y)} = cayLine ω) ∧
      ∀ y : Vec 16, y ≠ 0 → y ∈ cayLineInf →
        {z : Vec 16 | conjChange *ᵥ z ∈ Lstd (conjChange *ᵥ y)} = cayLineInf :=
  Osserman.Proofs.Lemma71Geometry.lem_7_1_L_line_proved

/-- **Lemma 7.1(a), proof** (line 715 of P013_short.tex): "Suppose first $Kx\in E(x)$. Since $\ip{Kx}x=0$, $K$ is skew." -/
theorem lem_7_1_a_skew (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Estd x) :
    (∀ x : Vec 16, (K *ᵥ x) ⬝ᵥ x = 0) ∧ Kᵀ = -K :=
  Osserman.Proofs.Lemma71Coordinates.lem_7_1_a_skew_proved K hK

/-- **Lemma 7.1(a), proof** (lines 716-718 of P013_short.tex): `K` (written in the new coordinates, `K' = conjChange·K·conjChange`)
maps every Cayley line `𝒞_ω` and `𝒞_∞` into itself ("Preservation of $\mathcal C_0,\mathcal C_\infty,\mathcal C_1$",
"Preservation of $\mathcal C_\omega$"). -/
theorem lem_7_1_a_lines (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Estd x) :
    (∀ ω : Vec 8, ∀ y ∈ cayLine ω, (conjChange * K * conjChange) *ᵥ y ∈ cayLine ω) ∧
      ∀ y ∈ cayLineInf, (conjChange * K * conjChange) *ᵥ y ∈ cayLineInf :=
  Osserman.Proofs.Lemma71Geometry.lem_7_1_a_lines_proved K hK

/-- **Lemma 7.1(a), proof** (lines 716-717 of P013_short.tex): "Preservation of $\mathcal C_0,\mathcal C_\infty,\mathcal C_1$ forces
$K=\operatorname{diag}(D,D)$" (for any linear map of `ℝ^16` in the new coordinates). -/
theorem lem_7_1_a_diag (K' : Matrix (Fin 16) (Fin 16) ℝ) (h0 : ∀ y ∈ cayLine 0, K' *ᵥ y ∈ cayLine 0)
    (hinf : ∀ y ∈ cayLineInf, K' *ᵥ y ∈ cayLineInf) (h1 : ∀ y ∈ cayLine oone, K' *ᵥ y ∈ cayLine oone) :
    ∃ D : Matrix (Fin 8) (Fin 8) ℝ, ∀ y : Vec 16, K' *ᵥ y = octPair (D *ᵥ oct1 y) (D *ᵥ oct2 y) :=
  Osserman.Proofs.Lemma71Blocks.lem_7_1_a_diag_proved K' h0 hinf h1

/-- **Lemma 7.1(a), proof** (line 718 of P013_short.tex): "Preservation of $\mathcal C_\omega$ gives $D(\omega u)=\omega D(u)$". -/
theorem lem_7_1_a_left_linear (D : Matrix (Fin 8) (Fin 8) ℝ)
    (hD : ∀ ω : Vec 8, ∀ y ∈ cayLine ω, octPair (D *ᵥ oct1 y) (D *ᵥ oct2 y) ∈ cayLine ω) :
    ∀ ω u : Vec 8, D *ᵥ omul ω u = omul ω (D *ᵥ u) :=
  Osserman.Proofs.Lemma71Algebra.lem_7_1_a_left_linear_proved D hD

/-- **Lemma 7.1(a), proof** (lines 719-720 of P013_short.tex): "Put $c=D(1)$; then $D(u)=uc$ and $(\omega u)c=\omega(uc)$ for all
$\omega,u$." -/
theorem lem_7_1_a_right_mult (D : Matrix (Fin 8) (Fin 8) ℝ)
    (hD : ∀ ω u : Vec 8, D *ᵥ omul ω u = omul ω (D *ᵥ u)) :
    (∀ u : Vec 8, D *ᵥ u = omul u (D *ᵥ oone)) ∧
      ∀ ω u : Vec 8, omul (omul ω u) (D *ᵥ oone) = omul ω (omul u (D *ᵥ oone)) :=
  Osserman.Proofs.Lemma71Algebra.lem_7_1_a_right_mult_proved D hD

/-- **Lemma 7.1(a), proof** (lines 720-721 of P013_short.tex): "$c$ lies in the right nucleus of $\OCT$, which is $\R$" (used with no
proof and no citation, flag F10); both inclusions. -/
theorem oct_right_nucleus (c : Vec 8) :
    (∀ ω u : Vec 8, omul (omul ω u) c = omul ω (omul u c)) ↔ ∃ r : ℝ, c = r • oone :=
  Osserman.Proofs.OctonionNucleus.oct_right_nucleus_proved c

/-- **Lemma 7.1(a), proof** (lines 721-722 of P013_short.tex): "Hence $K=cI$, and skewness forces $c=0$." -/
theorem lem_7_1_a_scalar (K : Matrix (Fin 16) (Fin 16) ℝ) (D : Matrix (Fin 8) (Fin 8) ℝ) (r : ℝ)
    (hdiag : ∀ y : Vec 16, (conjChange * K * conjChange) *ᵥ y = octPair (D *ᵥ oct1 y) (D *ᵥ oct2 y))
    (hD : ∀ u : Vec 8, D *ᵥ u = omul u (r • oone)) (hskew : Kᵀ = -K) :
    K = r • (1 : Matrix (Fin 16) (Fin 16) ℝ) ∧ r = 0 :=
  Osserman.Proofs.Lemma71Blocks.lem_7_1_a_scalar_proved K D r hdiag hD hskew

/-- **Lemma 7.1(b), proof** (lines 724-725 of P013_short.tex): "Suppose next $Kx\in N(x)$. The lines $\mathcal C_0$ and
$\mathcal C_\infty$ force $K=\left(\begin{smallmatrix}0&B\\ C&0\end{smallmatrix}\right)$" (in the new coordinates). -/
theorem lem_7_1_b_offdiag (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x) :
    ∃ B C : Matrix (Fin 8) (Fin 8) ℝ,
      ∀ y : Vec 16, (conjChange * K * conjChange) *ᵥ y = octPair (B *ᵥ oct2 y) (C *ᵥ oct1 y) :=
  Osserman.Proofs.Lemma71Blocks.lem_7_1_b_offdiag_proved K hK

/-- **Lemma 7.1(b), proof** (lines 724-727 of P013_short.tex), (hidden): in the new coordinates, for `y ≠ 0` on `𝒞_ω`,
`N = 𝒞_ω^⊥ = {(-ω̄r, r)}`; for `y ≠ 0` on `𝒞_∞`, `N = 𝒞_0` (so "for $x\in\mathcal C_0$, $N(x)=\mathcal C_\infty$, and
the other way round", the case `ω = 0`). -/
theorem lem_7_1_N_line :
    (∀ (ω : Vec 8) (y : Vec 16), y ≠ 0 → y ∈ cayLine ω →
        {z : Vec 16 | conjChange *ᵥ z ∈ Nstd (conjChange *ᵥ y)} = {z | oct1 z = -omul (oconj ω) (oct2 z)}) ∧
      ∀ y : Vec 16, y ≠ 0 → y ∈ cayLineInf →
        {z : Vec 16 | conjChange *ᵥ z ∈ Nstd (conjChange *ᵥ y)} = cayLine 0 :=
  Osserman.Proofs.Lemma71Geometry.lem_7_1_N_line_proved

/-- **Lemma 7.1(b), proof** (lines 726-727 of P013_short.tex), (hidden): the adjoint identity `⟨ωu, r⟩ = ⟨u, ω̄r⟩`. -/
theorem oct_adjoint (ω u r : Vec 8) : omul ω u ⬝ᵥ r = u ⬝ᵥ omul (oconj ω) r :=
  Osserman.Proofs.OctonionFacts.oct_adjoint_proved ω u r

/-- **Lemma 7.1(b), proof** (lines 726-727 of P013_short.tex): "The graph condition for $\mathcal C_\omega^\perp$ is
$B(\omega u)=-\overline\omega C(u)$." -/
theorem lem_7_1_b_graph (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : ∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Nstd x)
    (B C : Matrix (Fin 8) (Fin 8) ℝ)
    (hBC : ∀ y : Vec 16, (conjChange * K * conjChange) *ᵥ y = octPair (B *ᵥ oct2 y) (C *ᵥ oct1 y)) :
    ∀ ω u : Vec 8, B *ᵥ omul ω u = -omul (oconj ω) (C *ᵥ u) :=
  Osserman.Proofs.Lemma71Blocks.lem_7_1_b_graph_proved K hK B C hBC

/-- **Lemma 7.1(b), proof** (lines 727-728 of P013_short.tex): "Taking $\omega=1$ gives $B=-C$; taking $u=1$ then gives
$C(\omega)=\overline\omega\gamma$, where $\gamma=C(1)$." -/
theorem lem_7_1_b_gamma (B C : Matrix (Fin 8) (Fin 8) ℝ)
    (hBC : ∀ ω u : Vec 8, B *ᵥ omul ω u = -omul (oconj ω) (C *ᵥ u)) :
    B = -C ∧ ∀ ω : Vec 8, C *ᵥ ω = omul (oconj ω) (C *ᵥ oone) :=
  Osserman.Proofs.Lemma71Algebra.lem_7_1_b_gamma_proved B C hBC

/-- **Lemma 7.1(b), proof** (lines 729-731 of P013_short.tex), (hidden): octonion conjugation reverses products, `(ωu)‾ = ū ω̄`. -/
theorem oct_conj_mul (a b : Vec 8) : oconj (omul a b) = omul (oconj b) (oconj a) :=
  Osserman.Proofs.OctonionFacts.oct_conj_mul_proved a b

/-- **Lemma 7.1(b), proof** (lines 729-731 of P013_short.tex): "Substitution yields $(ab)\gamma=b(a\gamma)$ $(a,b\in\OCT)$" (from
`C(ωu) = ω̄C(u)`, which is `B(ωu) = -ω̄C(u)` with `B = -C`, and `C(ω) = ω̄γ`). -/
theorem lem_7_1_b_rel (C : Matrix (Fin 8) (Fin 8) ℝ) (γ : Vec 8)
    (hC : ∀ ω u : Vec 8, C *ᵥ omul ω u = omul (oconj ω) (C *ᵥ u)) (hγ : ∀ ω : Vec 8, C *ᵥ ω = omul (oconj ω) γ) :
    ∀ a b : Vec 8, omul (omul a b) γ = omul b (omul a γ) :=
  Osserman.Proofs.Lemma71Algebra.lem_7_1_b_rel_proved C γ hC hγ

/-- **Lemma 7.1(b), proof** (line 733 of P013_short.tex): "Choose a quaternion subalgebra containing $\gamma$" (used with no proof, flag
F10): the image of an injective real-linear map `f : ℍ → ℝ^8` with `f(1) = 1` and `f(pq) = f(p)f(q)` contains `γ`. -/
theorem oct_quaternion_subalgebra (γ : Vec 8) :
    ∃ f : Quaternion ℝ →ₗ[ℝ] Vec 8, Function.Injective f ∧ f 1 = oone ∧
      (∀ p q : Quaternion ℝ, f (p * q) = omul (f p) (f q)) ∧ γ ∈ LinearMap.range f :=
  Osserman.Proofs.OctonionQuaternion.oct_quaternion_subalgebra_proved γ

/-- **Lemma 7.1(b), proof** (lines 735-736 of P013_short.tex): "Multiplicativity of the octonion norm". -/
theorem oct_norm_mul (a b : Vec 8) : omul a b ⬝ᵥ omul a b = (a ⬝ᵥ a) * (b ⬝ᵥ b) :=
  Osserman.Proofs.OctonionFacts.oct_norm_mul_proved a b

/-- **Lemma 7.1(b), proof** (lines 733-736 of P013_short.tex): "choose noncommuting $a,b$ in it. Associativity in that subalgebra gives
$(ab-ba)\gamma=0$. Multiplicativity of the octonion norm forces $\gamma=0$". -/
theorem lem_7_1_b_gamma_zero (γ : Vec 8) (hγ : ∀ a b : Vec 8, omul (omul a b) γ = omul b (omul a γ)) : γ = 0 :=
  Osserman.Proofs.Lemma71Algebra.lem_7_1_b_gamma_zero_proved γ hγ

/-! ## Proof of Theorem E (lines 738-785) -/

/-- **Theorem E, proof** (line 740 of P013_short.tex): "Let $t\in\{1,2\}$ be the smallest multiplicity"; in each of the four patterns
(written with `t` last) the smallest multiplicity occurs only once, and the multiplicities fill `x^⊥`. -/
theorem thm_E_smallest (m : Fin 3 → ℕ) (hm : IsThmEPattern m) :
    (m 2 = 1 ∨ m 2 = 2) ∧ m 2 < m 0 ∧ m 2 < m 1 ∧ m 0 + m 1 + m 2 = 15 :=
  Osserman.Proofs.ThmEElementary.thm_E_smallest_proved m hm

/-- **Theorem E, proof** (lines 741-744 of P013_short.tex): "shift a different reduced eigenvalue to zero by subtracting a multiple of
$R_1$"; (hidden) subtracting `cR_1` shifts every reduced eigenvalue by `-c` and keeps its multiplicity. Consequence
(not a separate conjunct): with `c` one of the reduced eigenvalues, the shifted tensor has `k = 3` reduced eigenvalues,
one of them zero (l. 743-744). -/
theorem thm_E_shift {n : ℕ} (R R0 : CurvTensor n) (c : ℝ)
    (h0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w) :
    ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ μ : ℝ, R0.redMult x (μ - c) = R.redMult x μ :=
  Osserman.Proofs.ThmEElementary.thm_E_shift_proved R R0 c h0

/-- **Theorem E, proof** (line 741 of P013_short.tex) and **Remark 7.2** (lines 799-801), (hidden): `R - cR_1` is an algebraic
curvature tensor with Jacobi family `J_x(R) - cΠ(x)`; it is Osserman iff `R` is, and Clifford iff `R` is. -/
theorem shift_R1 {n : ℕ} (R : CurvTensor n) (c : ℝ) :
    ∃ R0 : CurvTensor n, (∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w) ∧
      (∀ x, R0.jacobi x = R.jacobi x - c • Pi x) ∧ (R0.IsOsserman ↔ R.IsOsserman) ∧
      (R0.IsClifford ↔ R.IsClifford) :=
  Osserman.Proofs.Rem72a.shift_R1_proved R c

/-- **Theorem E, proof** (lines 746-747 of P013_short.tex): "odd homogeneous polynomial fields of degree at most $k-1=2$. They are
therefore linear". -/
theorem thm_E_linear_fields (E : Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hodd : Odd d) (hd : d ≤ 2)
    (hE : ∀ j, (E j).IsHomogeneous d) : ∃ J : Matrix (Fin 16) (Fin 16) ℝ, ∀ x : Vec 16, evalField E x = J *ᵥ x :=
  Osserman.Proofs.ThmEFrames.thm_E_linear_fields_proved E d hodd hd hE

/-- **Theorem E, proof** (lines 748-749 of P013_short.tex): "Their norm and orthogonality identities make each $J_i$ skew and orthogonal
and make the $J_i$ anticommute" (an orthonormal family `J_ax ⊥ x` at unit `x` is a `Cl(t)`-structure of orthogonal
maps). -/
theorem thm_E_frame_clifford {n t : ℕ} (J : Fin t → Matrix (Fin n) (Fin n) ℝ)
    (horth : ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ a b, (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0)
    (hperp : ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ a, x ⬝ᵥ (J a *ᵥ x) = 0) :
    IsCliffordStr J ∧ ∀ a, (J a)ᵀ * J a = 1 :=
  Osserman.Proofs.ThmEFrames.thm_E_frame_clifford_proved J horth hperp

/-- **Theorem E, proof** (lines 750-751 of P013_short.tex): "Return to the original tensor, whose eigenspaces are unchanged by the
shift": for `R0 = R - cR_1`, the reduced `(μ - c|x|²)`-eigenspace of `R0` is the reduced `μ`-eigenspace of `R`. -/
theorem thm_E_shift_eigenspaces {n : ℕ} (R R0 : CurvTensor n) (c : ℝ)
    (h0 : ∀ u v w, R0.op u v w = R.op u v w - c • R1fun u v w) :
    ∀ (x : Vec n) (μ : ℝ), Module.End.eigenspace (R0.jacobiMap x) (μ - c * (x ⬝ᵥ x)) ⊓ perp x =
      Module.End.eigenspace (R.jacobiMap x) μ ⊓ perp x :=
  Osserman.Proofs.ThmEElementary.thm_E_shift_eigenspaces_proved R R0 c h0

/-- **Theorem E, proof, first paragraph** (lines 740-751 of P013_short.tex; rows S7.25-S7.29 together): for a Theorem E pattern with
distinct reduced eigenvalues `ev` (`τ = ev 2` of the smallest multiplicity `t`), there is a `Cl(t)`-structure
`J_1, …, J_t` whose fields `J_ax` lie in the `τ`-eigenspace (from the cited `Osserman.Cited.nik2006_lemma_3_1`). -/
theorem thm_E_frame (R : CurvTensor 16) (m : Fin 3 → ℕ) (hm : IsThmEPattern m) (ev : Fin 3 → ℝ)
    (hev : Function.Injective ev) (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) :
    ∃ J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ, ThmEFrame R m ev J :=
  Osserman.Proofs.ThmEFrameConstruction.thm_E_frame_proved R m hm ev hev hpat

/-- **Theorem E, proof**, hidden step (not stated in the paper; used at lines 746-748 of P013_short.tex): for a unit
`x`, the vectors `J_a x` are orthonormal and span the `τ`-eigenspace on `x^⊥` (the fact behind "is Osserman with two
distinct eigenvalues", lines 765-766, and "the mutually orthogonal eigenlines $\R J_ix$", lines 777-778). -/
theorem thm_E_frame_span (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → (∀ a b, (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0) ∧
      Module.End.eigenspace (R.jacobiMap x) (ev 2) ⊓ perp x = Submodule.span ℝ (Set.range fun a => J a *ᵥ x) :=
  Osserman.Proofs.ThmEFrames.thm_E_frame_span_proved R m ev J h

/-- **Theorem E, proof** (lines 753-758 of P013_short.tex): "Choose another reduced eigenvalue $\tau'$ so that moving $\tau$ to
$\tau'$ merges the multiplicities as $(7,7,1)\to(7,8)$, $(8,6,1)\to(8,7)$, $(8,5,2)\to(8,7)$, $(7,6,2)\to(7,8)$"
(the paper's `τ'` is the second entry of the pattern as written in `IsThmEPattern`). -/
theorem thm_E_merge (m : Fin 3 → ℕ) (hm : IsThmEPattern m) :
    (m 0 = 7 ∧ m 1 + m 2 = 8) ∨ (m 0 = 8 ∧ m 1 + m 2 = 7) :=
  Osserman.Proofs.ThmEElementary.thm_E_merge_proved m hm

/-- **Theorem E, proof** (lines 759-761 of P013_short.tex): "For a skew orthogonal $J$, let $R_J$ denote the curvature tensor whose
Jacobi family is $(Jx)(Jx)^T$, obtained for example from (eq:reconstruct)"; (hidden) `(Jx)(Jx)ᵀ` is a symmetric
quadratic family killing `x`, and `⟨Jx,y⟩² = ⟨Jy,x⟩²`. Only skewness is assumed (orthogonality is not needed). -/
theorem RJ_curv {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : Jᵀ = -J) :
    (IsQuadFamily (jfam J) ∧ (∀ x, (jfam J x)ᵀ = jfam J x) ∧ (∀ x, jfam J x *ᵥ x = 0) ∧
        ∀ x y : Vec n, ((J *ᵥ x) ⬝ᵥ y) ^ 2 = ((J *ᵥ y) ⬝ᵥ x) ^ 2) ∧
      ∃ R : CurvTensor n, (∀ u v w, R.op u v w = RJfun J u v w) ∧ ∀ x, R.jacobi x = jfam J x :=
  Osserman.Proofs.Rem72a.RJ_curv_proved J hJ

/-- **Theorem E, proof** (lines 762-766 of P013_short.tex): "$\widetilde R=R-(\tau-\tau')\sum_{i=1}^t R_{J_i}$ is Osserman with two distinct
eigenvalues of multiplicities seven and eight" (precisely: `ev 0` keeps multiplicity `m 0`, and the paper's
`τ' = ev 1` gets `m 1 + m 2`); (hidden) the Jacobi operator is linear in the tensor. Last conjunct (lines 768-769,
review a2-s7 M-3): "each $J_ix$ remains an eigenfield in one of the two merged distributions" — the merged
`τ' = ev 1` one. -/
theorem thm_E_tilde (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) :
    ∃ Rt : CurvTensor 16, (∀ u v w, Rt.op u v w = R.op u v w - (ev 2 - ev 1) • ∑ a, RJfun (J a) u v w) ∧
      (∀ x, Rt.jacobi x = R.jacobi x - (ev 2 - ev 1) • ∑ a, jfam (J a) x) ∧ Rt.IsOsserman ∧
      (∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x (ev 0) = m 0 ∧ Rt.redMult x (ev 1) = m 1 + m 2) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) (ev 1) :=
  Osserman.Proofs.ThmEClosed.thm_E_tilde_proved R m ev J h

/-- **Theorem E, proof** (line 767 of P013_short.tex): "Apply Theorem C": the two-eigenvalue tensor meets the hypothesis `h2` of
`thm_C`. -/
theorem thm_E_apply_C (Rt : CurvTensor 16) (μ₀ μ₁ : ℝ) (hne : μ₀ ≠ μ₁) (a b : ℕ)
    (hab : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7))
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₀ = a ∧ Rt.redMult x μ₁ = b) :
    ∃ μ₁' μ₂' : ℝ, μ₁' ≠ μ₂' ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₁' = 8 ∧ Rt.redMult x μ₂' = 7 :=
  Osserman.Proofs.ThmEElementary.thm_E_apply_C_proved Rt μ₀ μ₁ hne a b hab hpat

/-- **Theorem E, proof** (lines 767-770 of P013_short.tex), (hidden): a Cayley-type tensor `aR_1 + bT^*R_Cay` with `b ≠ 0` has, at a
unit `x`, the reduced eigenspaces `T⁻¹N(Tx)` (eigenvalue `a + b`, dimension 8) and `T⁻¹E(Tx)` (eigenvalue `a + 4b`,
dimension 7): the two distributions of the standard model, moved by `T`. The eigenvalues come from the a1 row
`sec6_jacobi_Rcay` (`J_x(R_Cay) = Π + 3A`: reduced eigenvalue 1 on `N(x)`, 4 on `E(x)`). -/
theorem thm_E_cayley_eigendistributions (Rt : CurvTensor 16) (a b : ℝ) (hb : b ≠ 0)
    (T : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ)
    (hR : ∀ u v w, Rt.op u v w = a • R1fun u v w + b • pullbackFun T RCayFun u v w) (x : Vec 16)
    (hx : x ⬝ᵥ x = 1) :
    Module.End.eigenspace (Rt.jacobiMap x) (a + b) ⊓ perp x = (Nstd (T *ᵥ x)).comap (Matrix.toLin' T) ∧
      Module.End.eigenspace (Rt.jacobiMap x) (a + 4 * b) ⊓ perp x = (Estd (T *ᵥ x)).comap (Matrix.toLin' T) :=
  Osserman.Proofs.ThmECayley.thm_E_cayley_eigendistributions_proved Rt a b hb T hT hR x hx

/-- **Theorem E, proof** (lines 769-770 of P013_short.tex): "after conjugating the field to the standard model:
$K=TJ_iT^{-1}$" (review a2-s7 N-2): for orthogonal `T`, a field `Jx` in `T⁻¹N(Tx)` (resp. `T⁻¹E(Tx)`) at every unit
`x` gives `K = TJTᵀ` with `Kz ∈ N(z)` (resp. `E(z)`) for every `z ≠ 0`, the hypothesis of Lemma 7.1. -/
theorem thm_E_conj_standard (T J : Matrix (Fin 16) (Fin 16) ℝ) (hT : T ∈ Matrix.orthogonalGroup (Fin 16) ℝ) :
    ((∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ (Nstd (T *ᵥ x)).comap (Matrix.toLin' T)) →
        ∀ z : Vec 16, z ≠ 0 → (T * J * Tᵀ) *ᵥ z ∈ Nstd z) ∧
      ((∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ (Estd (T *ᵥ x)).comap (Matrix.toLin' T)) →
        ∀ z : Vec 16, z ≠ 0 → (T * J * Tᵀ) *ᵥ z ∈ Estd z) :=
  Osserman.Proofs.ThmECayley.thm_E_conj_standard_proved T J hT

/-- **Theorem E, proof** (lines 767-770 of P013_short.tex): "Its Cayley alternative is impossible: each $J_ix$ remains an eigenfield in
one of the two merged distributions, contradicting Lemma 7.1 after conjugating the field to the standard model:
$K=TJ_iT^{-1}$." Stated for any nonzero skew `J` whose field lies in one eigen-distribution of a two-eigenvalue tensor
of multiplicities `{7, 8}`; the conclusion excludes every Cayley-type form (`b = 0` included). -/
theorem thm_E_no_cayley (Rt : CurvTensor 16) (μ₀ μ₁ : ℝ) (hne : μ₀ ≠ μ₁) (a b : ℕ)
    (hab : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7))
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₀ = a ∧ Rt.redMult x μ₁ = b)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJ0 : J ≠ 0)
    (hfield : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) μ₁) :
    ¬ IsCayleyType Rt :=
  Osserman.Proofs.ThmECayley.thm_E_no_cayley_proved Rt μ₀ μ₁ hne a b hab hpat J hJs hJ0 hfield

/-- **Theorem E, proof** (line 771 of P013_short.tex): "Thus $\widetilde R$ is Clifford" (the first two cases of Theorem C). -/
theorem thm_E_tilde_clifford (Rt : CurvTensor 16) (μ₀ μ₁ : ℝ) (hne : μ₀ ≠ μ₁) (a b : ℕ)
    (hab : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7))
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → Rt.redMult x μ₀ = a ∧ Rt.redMult x μ₁ = b)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJ0 : J ≠ 0)
    (hfield : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) μ₁) :
    Rt.IsClifford :=
  Osserman.Proofs.ThmECayley.thm_E_tilde_clifford_proved Rt μ₀ μ₁ hne a b hab hpat J hJs hJ0 hfield

/-- **Theorem E, proof** (lines 773-776 of P013_short.tex): "By [Nik2006, Lemma 3.2(1), pp. 383-384], if $R$ is Osserman, $J$ is
orthogonal and skew, $c\ne0$, and $R-cR_J$ is Osserman and Clifford, then $R$ is Clifford." ADAPTED-CITED: the paper
re-proves it as Remark 7.2 (flag F1), so this is a theorem to PROVE, via `rem_7_2_normalize` and
`rem_7_2_normalized`. -/
theorem lem_nik_3_2_1 (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w) (hO : R.IsOsserman)
    (hO' : R'.IsOsserman) (hC' : R'.IsClifford) : R.IsClifford :=
  Osserman.Proofs.Rem72c.lem_nik_3_2_1_proved R R' J hJs hJo c hc hR' hO hO' hC'

/-- **Theorem E, proof** (lines 776-778 of P013_short.tex): "Each intermediate tensor here is Osserman: only the constant eigenvalues on
the mutually orthogonal eigenlines $\R J_ix$ change" (for any coefficients `s_a`, `R - ∑ s_aR_{J_a}` is Osserman when
the `J_ax` form a Clifford frame inside one eigen-distribution of an Osserman `R`). -/
theorem thm_E_intermediate_osserman (R : CurvTensor 16) (hO : R.IsOsserman) {t : ℕ}
    (J : Fin t → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr J) (τ : ℝ)
    (hfr : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ a, J a *ᵥ x ∈ Module.End.eigenspace (R.jacobiMap x) τ) (s : Fin t → ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - ∑ a, s a • RJfun (J a) u v w) ∧ R'.IsOsserman :=
  Osserman.Proofs.ThmEClosed.thm_E_intermediate_osserman_proved R hO J hJ τ hfr s

/-- **Theorem E, proof** (lines 779-782 of P013_short.tex), (hidden): "the intermediate pattern $(7,7,1)$ reached from $(7,6,2)$": for
`t = 2`, removing ONE rank-one term moves one field `J_ax` from `τ` to `μ`, giving the pattern
`(m 0, m 1 + 1, 1)` (so `(7,6,2) → (7,7,1)` and `(8,5,2) → (8,6,1)`). -/
theorem thm_E_intermediate_pattern (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) (h2 : m 2 = 2) (a : Fin (m 2)) :
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - (ev 2 - ev 1) • RJfun (J a) u v w) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        R'.redMult x (ev 0) = m 0 ∧ R'.redMult x (ev 1) = m 1 + 1 ∧ R'.redMult x (ev 2) = 1 :=
  Osserman.Proofs.ThmEClosed.thm_E_intermediate_pattern_proved R m ev J h h2 a

/-- **Theorem E, proof** (lines 763 of P013_short.tex, 767), (hidden): the coefficient `c = τ - μ` of the restoring steps is nonzero,
since the reduced eigenvalues are distinct. -/
theorem thm_E_c_ne_zero (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) : ev 2 - ev 1 ≠ 0 :=
  Osserman.Proofs.ThmEElementary.thm_E_c_ne_zero_proved R m ev J h

/-- **Theorem E, proof** (lines 773-779 of P013_short.tex): "Restore the rank-one terms successively" (at most `t ≤ 2` steps): if
`R̃ = R - (τ - μ)∑_a R_{J_a}` is Clifford, then so is `R`. -/
theorem thm_E_restore (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) (Rt : CurvTensor 16)
    (hRt : ∀ u v w, Rt.op u v w = R.op u v w - (ev 2 - ev 1) • ∑ a, RJfun (J a) u v w) (hC : Rt.IsClifford) :
    R.IsClifford :=
  Osserman.Proofs.ThmEClosed.thm_E_restore_of_lem_nik_3_2_1 Osserman.Proofs.Rem72c.lem_nik_3_2_1_proved R m ev J h Rt hRt hC

/-! ## Remark 7.2 (rem:lemma32-cl8, lines 787-832): Nik2006 Lemma 3.2(1) in the form used here, every `ν ≤ 8` -/

/-- **Remark 7.2** (lines 794-797 of P013_short.tex): "with the generators of zero coefficient dropped, $\lambda_0$ has
multiplicity $15-\nu$; for $\nu\le7$ it is the unique eigenvalue of largest multiplicity": for a Clifford form with
`ν ≤ 7` and every `μ_α ≠ 0`, `λ_0` has multiplicity `15 - ν ≥ 8` and is the unique reduced eigenvalue of largest
multiplicity. -/
theorem rem_7_2_nu_le_7 (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (hν : ν ≤ 7) (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x l0 = 15 - ν ∧ 8 ≤ R'.redMult x l0 ∧
      ∀ ℓ : ℝ, ℓ ≠ l0 → R'.redMult x ℓ < R'.redMult x l0 :=
  Osserman.Proofs.Rem72d.rem_7_2_nu_le_7_proved R' Jα hJ hν l0 μ hμ hjac

/-- **Remark 7.2** (lines 792-794 of P013_short.tex): "that is, at an endpoint of type (eq:Cl8) or at the pattern
$(7,7,1)$" - at an (eq:Cl8) endpoint the two choices do differ (review a2-s7 S-1): for `J_x = μΠ + κ(Π - ∑_{i<8}(J_ix)(J_ix)ᵀ)` (form (eq:Cl8)), the base constant `λ_0 = μ + κ`
has multiplicity 7 and `μ` has multiplicity 8, so `λ_0` is not the eigenvalue of largest multiplicity. -/
theorem rem_7_2_cl8_differs (R' : CurvTensor 16) (μ κ : ℝ) (hκ : κ ≠ 0) (Jα : Fin 8 → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (hjac : ∀ x, R'.jacobi x = μ • Pi x + κ • (Pi x - ∑ i, jfam (Jα i) x)) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x (μ + κ) = 7 ∧ R'.redMult x μ = 8 :=
  Osserman.Proofs.Rem72d.rem_7_2_cl8_differs_proved R' μ κ hκ Jα hJ hjac

/-- **Remark 7.2** (lines 797-798 of P013_short.tex): "and at $(7,7,1)$ every Clifford structure has $\nu=8$" (stated for
EVERY Clifford form of the tensor, zero coefficients allowed; then also every coefficient is nonzero). -/
theorem rem_7_2_771_nu8 (R' : CurvTensor 16) (hpat : HasPattern R' ![7, 7, 1]) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) :
    ν = 8 ∧ ∀ α, η α ≠ 0 :=
  Osserman.Proofs.Rem72d.rem_7_2_771_nu8_proved R' hpat Jα hJ l0 η hjac

/-- **Remark 7.2** (lines 794-797 of P013_short.tex): "Indeed, with the generators of zero coefficient dropped, $\lambda_0$
has multiplicity $15-\nu$; [...] for $\nu=8$ it has multiplicity seven": for a Clifford form with every `μ_α ≠ 0`,
`λ_0` has reduced multiplicity `15 - ν` at every unit `x` (so `7` when `ν = 8`). -/
theorem rem_7_2_base_mult (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x l0 = 15 - ν :=
  Osserman.Proofs.Rem72e.rem_7_2_base_mult_proved R' Jα hJ l0 μ hμ hjac

/-- **Remark 7.2** (lines 792-794 of P013_short.tex): "The two choices differ only when $\nu=8$ and another eigenvalue also
has multiplicity at least seven, that is, at an endpoint of type (eq:Cl8) or at the pattern $(7,7,1)$": if `λ_0` is
not the unique reduced eigenvalue of largest multiplicity (the two choices differ), then `ν = 8`, `λ_0` has
multiplicity `7`, another eigenvalue has multiplicity at least `7`, and the pattern is `(8,7)` (the (eq:Cl8)
endpoint, with `ν = 8`) or `(7,7,1)`. -/
theorem rem_7_2_differ_only (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (μ : Fin ν → ℝ) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) (x : Vec 16) (hx : x ⬝ᵥ x = 1)
    (hdiff : ∃ ℓ : ℝ, ℓ ≠ l0 ∧ R'.redMult x l0 ≤ R'.redMult x ℓ) :
    ν = 8 ∧ R'.redMult x l0 = 7 ∧ (∃ ℓ : ℝ, ℓ ≠ l0 ∧ 7 ≤ R'.redMult x ℓ) ∧
      (HasPattern R' ![8, 7] ∨ HasPattern R' ![7, 7, 1]) :=
  Osserman.Proofs.Rem72e.rem_7_2_differ_only_proved R' Jα hJ l0 μ hμ hjac x hx hdiff

/-- **Remark 7.2** (lines 798-801 of P013_short.tex): "Let $\Jac_x(R-cR_J)=\lambda_0\Pi(x)+\sum_{\alpha=1}^{\nu}\mu_\alpha(J_\alpha x)
(J_\alpha x)^T$ with $\mu_\alpha\ne0$; subtracting $\lambda_0R_1$ from $R$ we may take $\lambda_0=0$"; (hidden) zero
coefficients may be dropped, and the shift keeps "Osserman" on both sides and brings "Clifford" back. -/
theorem rem_7_2_normalize (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J)
    (hJo : Jᵀ * J = 1) (c : ℝ) (hc : c ≠ 0) (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w)
    (hO : R.IsOsserman) (hO' : R'.IsOsserman) (hC' : R'.IsClifford) :
    ∃ (l0 : ℝ) (R0 R0' : CurvTensor 16) (ν : ℕ) (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ),
      (∀ u v w, R0.op u v w = R.op u v w - l0 • R1fun u v w) ∧
      (∀ u v w, R0'.op u v w = R'.op u v w - l0 • R1fun u v w) ∧
      (∀ x, R'.jacobi x = l0 • Pi x + ∑ α, μ α • jfam (Jα α) x) ∧
      Rem72Hyp R0 R0' J c Jα μ ∧ (R0.IsClifford → R.IsClifford) :=
  Osserman.Proofs.Rem72c.rem_7_2_normalize_proved R R' J hJs hJo c hc hR' hO hO' hC'

/-- **Remark 7.2** (lines 801-806 of P013_short.tex): "For unit $x$ the eigenspaces of $\Jac_x(R-cR_J)$ on $x^\perp$ are
$E_i(x)=\Span\{J_\alpha x:\mu_\alpha=\lambda_i\}$ for $i\ge1$ and $E_0(x)=x^\perp\cap(\sum_\alpha\R J_\alpha x)^\perp$";
(hidden) `⟨J_αx, J_βx⟩ = δ_αβ|x|²` and `J_αx ⊥ x`. Stated for every value `ℓ ≠ 0` (the span is `0` when `ℓ` is not
one of the `μ_α`). -/
theorem rem_7_2_eigenspaces (R' : CurvTensor 16) {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (μ : Fin ν → ℝ) (hJ : IsCliffordStr Jα) (hμ : ∀ α, μ α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = ∑ α, μ α • jfam (Jα α) x) :
    (∀ (x : Vec 16) α β, (Jα α *ᵥ x) ⬝ᵥ (Jα β *ᵥ x) = if α = β then x ⬝ᵥ x else 0) ∧
      (∀ (x : Vec 16) α, x ⬝ᵥ (Jα α *ᵥ x) = 0) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        (∀ ℓ : ℝ, ℓ ≠ 0 → Module.End.eigenspace (R'.jacobiMap x) ℓ ⊓ perp x =
          Submodule.span ℝ ((fun α => Jα α *ᵥ x) '' {α | μ α = ℓ})) ∧
        Module.End.eigenspace (R'.jacobiMap x) 0 ⊓ perp x = perp x ⊓ ⨅ α, perp (Jα α *ᵥ x) :=
  Osserman.Proofs.Rem72a.rem_7_2_eigenspaces_proved R' Jα μ hJ hμ hjac

/-- **Remark 7.2** (line 807 of P013_short.tex): "$\Jac_x(R)=\Jac_x(R-cR_J)+c(Jx)(Jx)^T$ and $Jx\perp x$" (for skew `J`). -/
theorem rem_7_2_jac_split {n : ℕ} (R R' : CurvTensor n) (J : Matrix (Fin n) (Fin n) ℝ) (hJs : Jᵀ = -J) (c : ℝ)
    (hR' : ∀ u v w, R'.op u v w = R.op u v w - c • RJfun J u v w) :
    ∀ x : Vec n, R.jacobi x = R'.jacobi x + c • jfam J x ∧ x ⬝ᵥ (J *ᵥ x) = 0 :=
  Osserman.Proofs.Rem72a.rem_7_2_jac_split_proved R R' J hJs c hR'

/-- **Remark 7.2** (lines 808-812 of P013_short.tex): "$\frac{\det(tI-\Jac_x(R))}{\det(tI-\Jac_x(R-cR_J))}
=1-c\sum_{i=0}^{p}\frac{\norm{\pi_i(Jx)}^2}{t-\lambda_i}$ on $x^\perp$", at a unit `x` and every real `t` that is not
a pole (`t ≠ 0 = λ_0`, `t ≠ μ_α`). Written with 16×16 determinants (both Jacobi operators kill `x`, so each
determinant is `t` times the one on `x^⊥` and the ratio is the paper's), cleared of the denominator, and with
`‖π_i(Jx)‖²` written in the orthonormal bases of row `rem_7_2_eigenspaces` (`blockSq`, `zeroSq`). -/
theorem rem_7_2_det_ratio (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) (x : Vec 16)
    (hx : x ⬝ᵥ x = 1) (t : ℝ) (ht0 : t ≠ 0) (htμ : ∀ α, t ≠ μ α) :
    (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R.jacobi x).det =
      (t • (1 : Matrix (Fin 16) (Fin 16) ℝ) - R'.jacobi x).det *
        (1 - c * (∑ ℓ ∈ Finset.univ.image μ, blockSq Jα μ J x ℓ / (t - ℓ) + zeroSq Jα J x / t)) :=
  Osserman.Proofs.Rem72b.rem_7_2_det_ratio_proved R R' J c Jα μ h x hx t ht0 htμ

/-- **Remark 7.2** (lines 811-813 of P013_short.tex): "so, both tensors being Osserman, partial fractions make each
$\norm{\pi_i(Jx)}=c_i$ constant on the unit sphere". -/
theorem rem_7_2_const (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    (∀ ℓ ∈ Finset.univ.image μ, ∃ cℓ : ℝ, 0 ≤ cℓ ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → blockSq Jα μ J x ℓ = cℓ ^ 2) ∧
      ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ x : Vec 16, x ⬝ᵥ x = 1 → zeroSq Jα J x = c0 ^ 2 :=
  Osserman.Proofs.Rem72b.rem_7_2_const_proved R R' J c Jα μ h

/-- **Remark 7.2** (lines 813-815 of P013_short.tex): "For $i\ge1$, $\sum_{\mu_\alpha=\lambda_i}\ip{J_\alpha x}{Jx}^2=c_i^2\norm x^4$ is a
sum of at most eight squares divisible by $\norm x^2$" (for every `x`, as functions and as polynomials; the count
`≤ 8` is `ν ≤ 8`, row `rem_7_2_nu_le_8`). -/
theorem rem_7_2_sum_squares (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∀ ℓ ∈ Finset.univ.image μ, (Finset.univ.filter fun α => μ α = ℓ).card ≤ 8 ∧
      (∃ cℓ : ℝ, ∀ x : Vec 16, blockSq Jα μ J x ℓ = cℓ ^ 2 * (x ⬝ᵥ x) ^ 2) ∧
      sqP 16 ∣ ∑ α ∈ Finset.univ.filter (fun α => μ α = ℓ), quadP ((Jα α)ᵀ * J) ^ 2 :=
  Osserman.Proofs.Rem72b.rem_7_2_sum_squares_proved R R' J c Jα μ h

/-- **Remark 7.2** (lines 815-817 of P013_short.tex): "so by [Nik2006, Lemma 3.11] each $\ip{J_\alpha x}{Jx}$ (a quadratic form) is a
constant multiple of $\norm x^2$" (the consequence used; the cited lemma is `Osserman.Cited.nik2006_lemma_3_11`). -/
theorem rem_7_2_inner_const (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∀ α, ∃ d : ℝ, ∀ x : Vec 16, (Jα α *ᵥ x) ⬝ᵥ (J *ᵥ x) = d * (x ⬝ᵥ x) :=
  Osserman.Proofs.Rem72b.rem_7_2_inner_const_proved R R' J c Jα μ h

/-- **Remark 7.2**, hidden step (not stated in the paper; used at lines 817-819 and 827-831 of P013_short.tex):
orthogonal combinations of an anticommuting orthonormal family of complex structures are again such a family: for
`O ∈ O(ν)`, `J'_a = ∑_b O_{ab}J_b` is a `Cl(ν)`-structure. -/
theorem cliffordStr_orth_comb {n ν : ℕ} (J : Fin ν → Matrix (Fin n) (Fin n) ℝ) (hJ : IsCliffordStr J)
    (O : Matrix (Fin ν) (Fin ν) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin ν) ℝ) :
    IsCliffordStr (fun a => ∑ b, O a b • J b) :=
  Osserman.Proofs.Rem72a.cliffordStr_orth_comb_proved J hJ O hO

/-- **Remark 7.2** (lines 817-819 of P013_short.tex), (hidden): an orthogonal change of the `J_α` INSIDE each block `{α : μ_α = λ}` keeps
the Clifford relations and the Jacobi formula `∑_α μ_α(J_αx)(J_αx)ᵀ`. -/
theorem rem_7_2_block_rotation {n ν : ℕ} (Jα : Fin ν → Matrix (Fin n) (Fin n) ℝ) (μ : Fin ν → ℝ)
    (hJ : IsCliffordStr Jα) (O : Matrix (Fin ν) (Fin ν) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin ν) ℝ)
    (hblk : ∀ α β, O α β ≠ 0 → μ α = μ β) :
    IsCliffordStr (fun α => ∑ β, O α β • Jα β) ∧
      ∀ x : Vec n, ∑ α, μ α • jfam (∑ β, O α β • Jα β) x = ∑ α, μ α • jfam (Jα α) x :=
  Osserman.Proofs.Rem72a.rem_7_2_block_rotation_proved Jα μ hJ O hO hblk

/-- **Remark 7.2** (lines 817-819 of P013_short.tex): "after an orthogonal change of the $J_\alpha$ with $\mu_\alpha=\lambda_i$ we get
$\pi_i(Jx)=c_iJ^{(i)}x$ for one of them, $J^{(i)}$": a block-orthogonal `O` after which `⟨J'_αx, Jx⟩ = d_α|x|²` with
at most one nonzero `d_α` per block. -/
theorem rem_7_2_rotate (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) :
    ∃ O ∈ Matrix.orthogonalGroup (Fin ν) ℝ, (∀ α β, O α β ≠ 0 → μ α = μ β) ∧
      ∃ d : Fin ν → ℝ, (∀ α (x : Vec 16), ((∑ β, O α β • Jα β) *ᵥ x) ⬝ᵥ (J *ᵥ x) = d α * (x ⬝ᵥ x)) ∧
        ∀ α β, α ≠ β → μ α = μ β → d α = 0 ∨ d β = 0 :=
  Osserman.Proofs.Rem72d.rem_7_2_rotate_proved R R' J c Jα μ h

/-- **Remark 7.2** (lines 819-822 of P013_short.tex): "$J_{\nu+1}x:=\pi_0(Jx)=Jx-\sum_{i\ge1}c_iJ^{(i)}x$ is linear and skew,
anticommutes with every $J_\alpha$ (as $J_{\nu+1}x\perp J_\alpha x$), and $\norm{J_{\nu+1}x}^2=c_0^2\norm x^2$ with
$c_0^2=1-\sum_{i\ge1}c_i^2$" (`J_{ν+1} = resid J Jα d`; also `J_{ν+1}x ⊥ x`). -/
theorem rem_7_2_residual (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d) :
    let K := resid J Jα d
    Kᵀ = -K ∧ (∀ α, K * Jα α + Jα α * K = 0) ∧ (∀ α (x : Vec 16), (K *ᵥ x) ⬝ᵥ (Jα α *ᵥ x) = 0) ∧
      (∀ x : Vec 16, x ⬝ᵥ (K *ᵥ x) = 0) ∧ 0 ≤ 1 - ∑ α, d α ^ 2 ∧
      ∀ x : Vec 16, (K *ᵥ x) ⬝ᵥ (K *ᵥ x) = (1 - ∑ α, d α ^ 2) * (x ⬝ᵥ x) :=
  Osserman.Proofs.Rem72c.rem_7_2_residual_proved R R' J c Jα μ d h

/-- **Remark 7.2** (lines 822-825 of P013_short.tex): "If $\nu=8$, then $c_0=0$: otherwise $c_0^{-1}J_9$ would be a ninth orthogonal
complex structure on $\R^{16}$ anticommuting with $J_1,\ldots,J_8$" (`J_9 = resid J Jα d = 0`). -/
theorem rem_7_2_nu8_c0 (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d)
    (hν : ν = 8) : resid J Jα d = 0 :=
  Osserman.Proofs.Rem72c.rem_7_2_nu8_c0_proved R R' J c Jα μ d h hν

/-- **Remark 7.2** (lines 823-827 of P013_short.tex): "write $Jx=\sum_{i\ge1}c_iJ^{(i)}x+c_0\bigl(c_0^{-1}J_{\nu+1}x\bigr)$, omitting the
last term if $c_0=0$"; and when `c_0 ≠ 0`, `c_0^{-1}J_{ν+1}` extends `J_1, …, J_ν` to a `Cl(ν+1)`-structure (the
"orthogonal complex structure anticommuting with" all `J_α` of line 824). -/
theorem rem_7_2_extend (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d) :
    let K := resid J Jα d
    let c0 := Real.sqrt (1 - ∑ α, d α ^ 2)
    J = ∑ α, d α • Jα α + c0 • (c0⁻¹ • K) ∧ (c0 ≠ 0 → IsCliffordStr (vecCons (c0⁻¹ • K) Jα)) :=
  Osserman.Proofs.Rem72c.rem_7_2_extend_proved R R' J c Jα μ d h

/-- **Remark 7.2** (lines 827-831 of P013_short.tex): "An orthogonal change of $J^{(1)},\ldots,J^{(p)}$ (and of $c_0^{-1}J_{\nu+1}$ if
$c_0\ne0$) that diagonalizes $\operatorname{diag}(\lambda_1,\ldots,\lambda_p,0)+c\,\gamma\gamma^T$ ... gives a Clifford
structure for $R$" (with `λ_0 = 0`: a `Cl(ν)`- or `Cl(ν+1)`-structure `J''` and constants `η` with
`J_x(R) = ∑ η_a(J''_ax)(J''_ax)ᵀ`). -/
theorem rem_7_2_diagonalize (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (d : Fin ν → ℝ) (h : Rem72Rot R R' J c Jα μ d) :
    ∃ (ν' : ℕ) (J'' : Fin ν' → Matrix (Fin 16) (Fin 16) ℝ) (η : Fin ν' → ℝ), IsCliffordStr J'' ∧
      (ν' = ν ∨ ν' = ν + 1) ∧ ∀ x : Vec 16, R.jacobi x = ∑ a, η a • jfam (J'' a) x :=
  Osserman.Proofs.Rem72c.rem_7_2_diagonalize_proved R R' J c Jα μ d h

/-- **Remark 7.2** (lines 799-801 of P013_short.tex and 819), (hidden): the conclusion in the normalized setting, for every `ν ≤ 8`:
`R` is Clifford (adding back `λ_0R_1` is `rem_7_2_normalize`; together they give `lem_nik_3_2_1`). -/
theorem rem_7_2_normalized (R R' : CurvTensor 16) (J : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) {ν : ℕ}
    (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (μ : Fin ν → ℝ) (h : Rem72Hyp R R' J c Jα μ) : R.IsClifford :=
  Osserman.Proofs.Rem72c.rem_7_2_normalized_proved R R' J c Jα μ h

/-- **Remark 7.2** (lines 813-815 and 822-825 of P013_short.tex), (hidden in l. 813-815): every `Cl(ν)`-structure on
`ℝ^16` has `ν ≤ 8` — "$\R^{16}$ carries at most eight (Hurwitz--Radon)" (line 825), also needed for "at most eight
squares". The paper names Hurwitz–Radon with no reference, so this is a row to PROVE, not a cited result (a proof: if
`ν ≥ 9`, the `2^9 = 512` products of distinct `J_1, …, J_9` are nonzero and pairwise orthogonal for
`⟨A, B⟩ = tr(AᵀB)`, in the 256-dimensional space of `16 × 16` matrices). -/
theorem rem_7_2_nu_le_8 {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) : ν ≤ 8 :=
  Osserman.Proofs.HurwitzRadon.rem_7_2_nu_le_8_proved Jα hJ

/-! ## Proof of Corollary D (lines 834-841) -/

/-- **Corollary D, proof** (lines 839-840 of P013_short.tex): "Apply Theorems C and E": pattern `(8,7)` gives Clifford or Cayley type
(Theorem C). -/
theorem cor_D_87 (R : CurvTensor 16) (h : HasPattern R ![8, 7]) : R.IsClifford ∨ IsCayleyType R :=
  Osserman.Proofs.CorD.cor_D_87_proved R h

/-- **Corollary D, proof** (lines 839-840 of P013_short.tex): pattern `(7,7,1)` gives Clifford (Theorem E). -/
theorem cor_D_771 (R : CurvTensor 16) (h : HasPattern R ![7, 7, 1]) : R.IsClifford :=
  Osserman.Proofs.CorD.cor_D_771_proved thm_E R h

/-- **Corollary D, proof** (lines 834-841 of P013_short.tex), (hidden): if `R` is Clifford the conclusion holds at once, so the cases
"Clifford", `(8,7)` and `(7,7,1)` cover every `R` that Andrejić's theorem leaves. -/
theorem cor_D_cases (R : CurvTensor 16)
    (h : R.IsClifford ∨ HasPattern R ![8, 7] ∨ HasPattern R ![7, 7, 1]) : R.IsClifford ∨ IsCayleyType R :=
  Osserman.Proofs.CorD.cor_D_cases_proved thm_E R h

/-! ## Non-vacuity of the hypotheses (review a2-s7 S-2) -/

/-- **Corollary D, non-vacuity** (Lean-only row): the hypotheses of Corollary D are met by `R_Cay`, so
`IsJacobiProportional` is not too strong and the Cayley branch occurs. -/
theorem cor_D_hyp_nonvacuous :
    ∃ R : CurvTensor 16, R.IsOsserman ∧ IsJacobiProportional R ∧ (∀ u v w, R.op u v w = RCayFun u v w) :=
  Osserman.Proofs.CorDNonvacuous.cor_D_hyp_nonvacuous_proved

/-- **Theorem E, non-vacuity** (Lean-only row): the pattern `(7,7,1)` occurs (e.g. `J_x = ∑_{α ≤ 7} (J_αx)(J_αx)ᵀ +
2(J_8x)(J_8x)ᵀ` with the `Cl(8)`-structure `J_α = S_0S_α` of the standard system). -/
theorem thm_E_hyp_nonvacuous : ∃ R : CurvTensor 16, HasPattern R ![7, 7, 1] :=
  Osserman.Proofs.CorDNonvacuous.thm_E_hyp_nonvacuous_proved

end Osserman.Paper
