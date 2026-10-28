/-
Osserman/Paper/Statements8.lean — one theorem per claim of Section 8 of paper 013 ("Further multiplicity reductions",
sec_small_roots.tex, 315 lines: Theorem F, Lemma 8.1, §8.2 and Lemma 8.2, the three-column step, Subsections 8.3-8.6),
the Zenodo posting copy sec_small_roots.tex (md5 41f1436d); "line" = line of that
file unless P013_short.tex is named. Definitions: Osserman/Defs/SmallRoots.lean.
Bodies link to proofs elsewhere; the audit marks any row without a proof as OPEN.
Results of OTHER papers are NOT rows here: they are cited statements in Osserman/Cited/Nik2006.lean (Nikolayevsky,
Lemmas 3.1, 3.11, Theorem 3.1, Proposition 2.1) and Osserman/Cited/Nik2005.lean (Nikolayevsky, Proposition 1); rows
that use them are PROVED-FROM-CITED. Results the paper re-proves or uses outside their stated hypotheses (Lemma 8.2, the
three-column step, §8.6) are rows to PROVE. "Restore with [Nik2006, Lemma 3.2(1)]" is the row `lem_nik_3_2_1` of
Statements7.lean (Remark 7.2, every `ν`).
Rule (review a2-six SHOULD-3): no row may be provable only ex falso; steps inside the paper's proofs by contradiction
(Lemma 8.1, `c > 0`; Lemma 8.2, `r = 2`, `c ≠ 0`) are stated in a general form whose hypotheses can hold.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Paper.StatementsSix
import Osserman.Defs.SmallRoots
import Osserman.Cited.Nik2006
import Osserman.Cited.Nik2005
import Osserman.Proofs.Lem81Stable
import Osserman.Proofs.S83Algebra
import Osserman.Proofs.S83Ends
import Osserman.Proofs.Lem81Rest
import Osserman.Proofs.S8Tools
import Osserman.Proofs.S83Fields
import Osserman.Proofs.S84Fields
import Osserman.Proofs.S8Cubic
import Osserman.Proofs.S83Move
import Osserman.Proofs.S84Move
import Osserman.Proofs.S83Opp1
import Osserman.Proofs.S85Alg
import Osserman.Proofs.S8TCAlgebra
import Osserman.Proofs.S8TCFactor
import Osserman.Proofs.S83Endpoint
import Osserman.Proofs.S85Fields
import Osserman.Proofs.QPrime
import Osserman.Proofs.Lem82DivQ
import Osserman.Proofs.S83Opp2
import Osserman.Proofs.S84End
import Osserman.Proofs.S85Ends
import Osserman.Proofs.S85Mult
import Osserman.Proofs.S85Clif
import Osserman.Proofs.S8TCFields
import Osserman.Proofs.S8Gen
import Osserman.Proofs.S8TCUnit
import Osserman.Proofs.S8TCOutcome
import Osserman.Proofs.S8Witness
import Osserman.Proofs.ThmF
import Osserman.Proofs.S86
import Osserman.Proofs.S8TCMove
import Osserman.Proofs.S8Opp
import Osserman.Proofs.S8TCWitness
import Osserman.Proofs.Lem82
import Osserman.Proofs.Lem82R1aAlg
import Osserman.Proofs.Lem82R1aLin
import Osserman.Proofs.Lem82R2
import Osserman.Proofs.Lem82R1
import Osserman.Proofs.S8TCBranch

namespace Osserman.Paper

open Osserman Osserman.Cited Matrix MvPolynomial

/-! ## Theorem F (thm:E, lines 6-15) -/

/-- **Theorem F** (lines 13-14 of sec_small_roots.tex), (hidden): "(nine further patterns, fifteen in all)": the
patterns (multisets of multiplicities) with sum 15, one entry `M ∈ {7, 8}` and every other entry 1 or 2 are exactly the
nine listed, and none of them is one of the six patterns of the first part. Also row S8.111 (§8.6 covers exactly these
nine). -/
theorem thm_F_nine_patterns :
    let six : List (Multiset ℕ) :=
      [{7, 6, 1, 1}, {8, 5, 1, 1}, {7, 5, 2, 1}, {8, 4, 2, 1}, {7, 5, 1, 1, 1}, {8, 4, 1, 1, 1}]
    let nine : List (Multiset ℕ) :=
      [{7, 2, 2, 2, 2}, {7, 2, 2, 2, 1, 1}, {7, 2, 2, 1, 1, 1, 1}, {7, 2, 1, 1, 1, 1, 1, 1},
        {7, 1, 1, 1, 1, 1, 1, 1, 1}, {8, 2, 2, 2, 1}, {8, 2, 2, 1, 1, 1}, {8, 2, 1, 1, 1, 1, 1},
        {8, 1, 1, 1, 1, 1, 1, 1}]
    (∀ s : Multiset ℕ,
        (s.sum = 15 ∧ ∃ M ∈ ({7, 8} : Finset ℕ), M ∈ s ∧ ∀ a ∈ s.erase M, a = 1 ∨ a = 2) ↔ s ∈ nine) ∧
      nine.Nodup ∧ nine.length = 9 ∧ ∀ s ∈ nine, s ∉ six :=
  Osserman.Proofs.ThmF.thm_F_nine_patterns_proved

/-- **Theorem F** (lines 13-14 of sec_small_roots.tex), (hidden; S8.111, review a3 S2): for a tensor with a full pattern
`m` (every entry positive, sum 15), the second hypothesis of Theorem F holds iff the multiset of `m` is one of the nine
patterns of `thm_F_nine_patterns` — "(nine further patterns, fifteen in all)" for tensors. -/
theorem thm_F_nine_patterns_tensor {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (hpat : HasPattern R m)
    (hpos : ∀ i, 0 < m i) (hsum : ∑ i, m i = 15) :
    (∃ μ0 : ℝ, ∃ M : ℕ, SmallMultHyp R μ0 M) ↔
      Finset.univ.val.map m ∈ ([{7, 2, 2, 2, 2}, {7, 2, 2, 2, 1, 1}, {7, 2, 2, 1, 1, 1, 1}, {7, 2, 1, 1, 1, 1, 1, 1},
        {7, 1, 1, 1, 1, 1, 1, 1, 1}, {8, 2, 2, 2, 1}, {8, 2, 2, 1, 1, 1}, {8, 2, 1, 1, 1, 1, 1},
        {8, 1, 1, 1, 1, 1, 1, 1}] : List (Multiset ℕ)) :=
  Osserman.Proofs.ThmF.thm_F_nine_patterns_tensor_proved R m hpat hpos hsum

/-- **Named eigenvalues** (Lean-only row, review a3 S1): `HasPattern R m` is exactly `∃ ev, PatternEv R m ev` (the
definition `PatternEv` repeats the body of `HasPattern` only to give the eigenvalues names). -/
theorem hasPattern_iff_patternEv {n k : ℕ} (R : CurvTensor n) (m : Fin k → ℕ) :
    HasPattern R m ↔ ∃ ev, PatternEv R m ev :=
  Osserman.Proofs.ThmF.hasPattern_iff_patternEv_proved R m

/-- **Theorem F, non-vacuity** (Lean-only row, review a3 R4): each of the six patterns and the hypothesis `SmallMultHyp`
is met by some tensor (e.g. Clifford tensors with a `Cl(8)`- or `Cl(7)`-structure and chosen coefficients `η_i`). With
`s8_shift_to_zero` and `s8_3_fields`, `s8_4_fields`, `s8_5_fields` this also shows that `Sec83Data`, `Sec84Data`,
`Sec85Data` can hold. -/
theorem thm_F_hyp_nonvacuous :
    (∃ R : CurvTensor 16, HasPattern R ![7, 6, 1, 1]) ∧ (∃ R : CurvTensor 16, HasPattern R ![8, 5, 1, 1]) ∧
      (∃ R : CurvTensor 16, HasPattern R ![7, 5, 2, 1]) ∧ (∃ R : CurvTensor 16, HasPattern R ![8, 4, 2, 1]) ∧
      (∃ R : CurvTensor 16, HasPattern R ![7, 5, 1, 1, 1]) ∧ (∃ R : CurvTensor 16, HasPattern R ![8, 4, 1, 1, 1]) ∧
      ∃ (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ), SmallMultHyp R μ0 M :=
  Osserman.Proofs.S8Example.thm_F_hyp_nonvacuous_proved

/-- **Three-column step, non-vacuity** (Lean-only row, review a3 R4): the hypotheses of the three-column step, with
(eq:cubicidentities) for the negative column, can hold (e.g. `R = 0`, `P_i(x) = qJ_ix` for anticommuting complex
structures `J_1, J_2, J_3`, weights `(1, 1, -1)`). -/
theorem s8_threeCol_nonvacuous :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      ThreeColHyp R μ P wt ∧ CubicIdentities (P 2) :=
  Osserman.Proofs.S8TC.s8_threeCol_nonvacuous_proved

/-- **Three-column step, branch non-vacuity** (Lean-only row, review a3 SHOULD-1): the hypothesis "all three images
`p_i` nonzero" of `s8_tc_primitive` (and `p_2 ≠ 0` of `s8_tc_lincomb`) can hold together with the three-column
hypotheses (reviewer's witness, checked numerically: `R = 0`, `μ = 0`, `ℝ¹⁶ = ℍ⁴`, `E = L_i`, `F = L_j`, `G = ±L_k`
blockwise, `K = EG`, `P_i(x) = (qI - 2(Kx)(Kx)ᵀ)D_ix` for an orthonormal frame `D_i` of `span(E, F, G)`, weights
`(1, 1, -1)`; numerical check in review a3). -/
theorem s8_threeCol_branch_nonvacuous :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      ThreeColHyp R μ P wt ∧ ∀ i, tcImg wt P i ≠ 0 :=
  Osserman.Proofs.S8TC.s8_threeCol_branch_nonvacuous_proved

/-- **Three-column step, distinct eigenvalues, non-vacuity** (Lean-only row, review a3 SHOULD-1): the hypotheses
`hO`, `μ 0 ≠ μ 1` of `s8_tc_frame_osserman` can hold together with the three-column hypotheses and (8.1) for the
negative column (e.g. a Clifford tensor with distinct `η`'s, `P_i(x) = qJ_ix`, weights of signs `(+, +, -)`). -/
theorem s8_threeCol_distinct_nonvacuous :
    ∃ (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ),
      R.IsOsserman ∧ ThreeColHyp R μ P wt ∧ CubicIdentities (P 2) ∧ μ 0 ≠ μ 1 :=
  Osserman.Proofs.S8TC.s8_threeCol_distinct_nonvacuous_proved

/-- **Lemma 8.2, non-vacuity** (Lean-only row, review a3 R4): for each `r ∈ {1, 2, 3}` the lifted data `Lem82Lift` of
the proof can hold (e.g. `P(x) = qJx` with `J² = -I`, `φ = x_0^r`, `Ψ = 0`, `C = J`). -/
theorem lem_8_2_lift_nonvacuous (r : ℕ) (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    ∃ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
      (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P r φ Ψ Cm :=
  Osserman.Proofs.Lem82.lem_8_2_lift_nonvacuous_proved r hr1 hr3

/-- **Lemma 8.2, lift step, non-vacuity** (Lean-only row, review a3 MUST-1): the hypotheses of `lem_8_2_lift` can
hold (e.g. `P = (x_0^3, 0, …, 0)`: `d = π(x_0)` is a nonunit dividing every component, and `q ∤ x_0^3`). -/
theorem lem_8_2_lift_hyp_nonvacuous :
    ∃ P : Fin 16 → MvPolynomial (Fin 16) ℝ, (∀ j, (P j).IsHomogeneous 3) ∧
      (∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)) ∧ ¬ ∀ j, sqP 16 ∣ P j :=
  Osserman.Proofs.Lem82.lem_8_2_lift_hyp_nonvacuous_proved

/-! ## Lemma 8.1 (lem:constantprojection, lines 17-52) -/

/-- **Lemma 8.1** (lem:constantprojection, lines 19-23 of sec_small_roots.tex): "Let $E(x),N(x)$ be the two Cayley
distributions of Lemma~\ref{lem:nofield}. If a skew-symmetric linear map $K$ satisfies $\norm{\pi_{N(x)}Kx}^2=c\norm
x^2$ for all $x\ne0$ and a constant $c$, then $K=0$." (`E(x) = Estd x`, `N(x) = Nstd x`, Section 7.) -/
theorem lem_8_1 (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) : K = 0 :=
  Osserman.Proofs.Lem81.lem_8_1_proved K hK c hc

/-- **Lemma 8.1** (lines 23-24 of sec_small_roots.tex): "In particular an orthogonal skew map cannot have constant
normalized projection lengths onto the two Cayley eigenspaces" (squared lengths `c_E|x|²` onto `E(x)` and `c_N|x|²`
onto `N(x)`, for all `x ≠ 0`). -/
theorem lem_8_1_orthogonal (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (hKo : Kᵀ * K = 1) (cE cN : ℝ) :
    ¬ ∀ x : Vec 16, x ≠ 0 → (∃ w, IsOrthProj (Estd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = cE * (x ⬝ᵥ x)) ∧
      ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = cN * (x ⬝ᵥ x) :=
  Osserman.Proofs.Lem81.lem_8_1_orthogonal_proved K hK hKo cE cN

/-- **Lemma 8.1** (lines 23-24 of sec_small_roots.tex), (hidden): for `x ≠ 0` and `v ⊥ x`,
`|π_{E(x)}v|² + |π_{N(x)}v|² = |v|²` (`x^⊥ = E(x) ⊕ N(x)` orthogonally), so a constant length onto one Cayley eigenspace
is a constant length onto the other. -/
theorem lem_8_1_pythagoras (x : Vec 16) (hx : x ≠ 0) (v : Vec 16) (hv : x ⬝ᵥ v = 0) (wE wN : Vec 16)
    (hE : IsOrthProj (Estd x) v wE) (hN : IsOrthProj (Nstd x) v wN) : wE ⬝ᵥ wE + wN ⬝ᵥ wN = v ⬝ᵥ v :=
  Osserman.Proofs.Lem81.lem_8_1_pythagoras_proved x hx v hv wE wN hE hN

/-- **Lemma 8.1, proof** (lines 29-30 of sec_small_roots.tex): "The Clifford relations give
$\ip{H_ix}{H_jx}=\delta_{ij}q$" (`H_i = S_i`, the standard system). -/
theorem lem_8_1_orthonormal (x : Vec 16) (i j : Fin 9) :
    (stdSys i *ᵥ x) ⬝ᵥ (stdSys j *ᵥ x) = if i = j then x ⬝ᵥ x else 0 :=
  Osserman.Proofs.Lem81.lem_8_1_orthonormal_proved x i j

/-- **Lemma 8.1, proof** (lines 30-33 of sec_small_roots.tex): "The identity $\sum_i(H_ix)(H_ix)^T=Z_x=xx^T+qI-Q(x)$ of
Section 6 (with $H_i=S_i$) and $Q(x)=q\,\pi_{L(x)}$ (Section 2), with $x\in L(x)$, give
$\sum_i(H_ix)(H_ix)^T=xx^T+q\,\pi_{N(x)}=q\,\pi_{\R x+N(x)}$" (for `x ≠ 0`; both projections written with
`IsOrthProj`). -/
theorem lem_8_1_Z_proj (x : Vec 16) (hx : x ≠ 0) :
    let Z := ∑ i, vecMulVec (stdSys i *ᵥ x) (stdSys i *ᵥ x)
    ∀ y : Vec 16, (∀ w, IsOrthProj (Nstd x) y w → Z *ᵥ y = (x ⬝ᵥ y) • x + (x ⬝ᵥ x) • w) ∧
      IsOrthProj (Submodule.span ℝ {x} ⊔ Nstd x) y ((x ⬝ᵥ x)⁻¹ • (Z *ᵥ y)) :=
  Osserman.Proofs.Lem81.lem_8_1_Z_proj_proved x hx

/-- **Lemma 8.1, proof** (lines 34-35 of sec_small_roots.tex): "So the nine orthogonal vectors $H_ix$, of norm $\sqrt
q$, span $\R x+N(x)$" (for `x ≠ 0`). -/
theorem lem_8_1_span (x : Vec 16) (hx : x ≠ 0) :
    Submodule.span ℝ (Set.range fun i => stdSys i *ᵥ x) = Submodule.span ℝ {x} ⊔ Nstd x :=
  Osserman.Proofs.Lem81.lem_8_1_span_proved x hx

/-- **Lemma 8.1, proof** (lines 35-36 of sec_small_roots.tex): "and, $K$ being skew, $\sum_i a_i^2=cq^2$", with
`a_i(x) = ⟨H_ix, Kx⟩` (line 29), at every `x`. -/
theorem lem_8_1_sum_a (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) :
    ∀ x : Vec 16, ∑ i, ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2 = c * (x ⬝ᵥ x) ^ 2 :=
  Osserman.Proofs.Lem81.lem_8_1_sum_a_proved K hK c hc

/-- **Lemma 8.1, proof** (lines 36-37 of sec_small_roots.tex): "differentiating the latter [$\sum_i h_i^2=q^2$] along
$Kx$ gives $\sum_i h_ia_i=0$" (`h_i(x) = ⟨H_ix, x⟩`; for every skew `K`, at every `x`). The identity
`∑ h_i² = q²` itself is the existing row `sec6_hopf` (with `S = stdSys`). -/
theorem lem_8_1_sum_ha (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (x : Vec 16) :
    ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) * ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) = 0 :=
  Osserman.Proofs.Lem81.lem_8_1_sum_ha_proved K hK x

/-- **Lemma 8.1, proof** (lines 37-38 of sec_small_roots.tex): "The matrix of $a_i$ is the symmetric trace-free
$A_i=(H_iK-KH_i)/2$" (for skew `K`). -/
theorem lem_8_1_A_matrix (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (i : Fin 9) :
    let Ai := (1 / 2 : ℝ) • (stdSys i * K - K * stdSys i)
    Aiᵀ = Ai ∧ Ai.trace = 0 ∧ ∀ x : Vec 16, x ⬝ᵥ (Ai *ᵥ x) = (stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x) :=
  Osserman.Proofs.Lem81.lem_8_1_A_matrix_proved K hK i

/-- **Lemma 8.1, proof** (lines 40-41 of sec_small_roots.tex): "If $c>0$, put $H_i(t)=\cos t\,H_i+c^{-1/2}\sin t\,A_i$.
Then $\sum_i\ip{H_i(t)x}x^2=q^2$ for every $t$". The case `c > 0` is the paper's proof by contradiction, so its
hypotheses can never hold together; to keep the row's content checkable (review rule a2-six SHOULD-3) it is stated as
the expansion identity, valid for every skew `K`, every `c > 0`, `t` and `x`. With `∑h_i² = q²` (`sec6_hopf`),
`∑h_ia_i = 0` (`lem_8_1_sum_ha`) and `∑a_i² = cq²` (`lem_8_1_sum_a`) it gives the sentence. -/
theorem lem_8_1_rotate (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ) (hc0 : 0 < c) (t : ℝ) (x : Vec 16) :
    ∑ i, hvec (lem81Fam K c t) x i ^ 2 =
      Real.cos t ^ 2 * ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) ^ 2 +
        2 * Real.cos t * Real.sin t * (Real.sqrt c)⁻¹ *
          ∑ i, (x ⬝ᵥ (stdSys i *ᵥ x)) * ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) +
        Real.sin t ^ 2 * c⁻¹ * ∑ i, ((stdSys i *ᵥ x) ⬝ᵥ (K *ᵥ x)) ^ 2 :=
  Osserman.Proofs.Lem81.lem_8_1_rotate_proved K hK c hc0 t x

/-- **Lemma 8.1, proof** (lines 41-43 of sec_small_roots.tex): "and this quadratic map is not constant on the unit
sphere (otherwise $H_i(t)=b_iI$ with $b$ a unit vector, but all its matrices are trace-free)"; (hidden) every `H_i(t)`
is symmetric and trace-free. Stated, as the paper argues it, for ANY nine symmetric trace-free matrices with
`∑⟨H_ix,x⟩² = 1` on the unit sphere (met by `stdSys`), so the row does not sit inside the contradiction of `c > 0`. -/
theorem lem_8_1_not_const (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c t : ℝ) :
    (∀ i, (lem81Fam K c t i).IsSymm ∧ (lem81Fam K c t i).trace = 0) ∧
      ∀ H : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ, (∀ i, (H i).IsSymm ∧ (H i).trace = 0) →
        (∀ x : Vec 16, x ⬝ᵥ x = 1 → ∑ i, hvec H x i ^ 2 = 1) →
        ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec H x ≠ hvec H y :=
  Osserman.Proofs.Lem81.lem_8_1_not_const_proved K hK c t

/-- **Lemma 8.1, proof** (line 43 of sec_small_roots.tex), (hidden): the standard system is trace-free, `tr S_i = 0`
(e.g. `S_i = -S_jS_iS_j` for `j ≠ i`). -/
theorem std_sys_trace_zero (i : Fin 9) : (stdSys i).trace = 0 :=
  Osserman.Proofs.Lem81.std_sys_trace_zero_proved i

/-- **Lemma 8.1, proof** (lines 43-45 of sec_small_roots.tex): "By Lemma~\ref{lem:threshold}(c) the $H_i(t)$ form a
symmetric Clifford system" (`n = 16`, `m = 8`; `lem_4_1_c`). The hypotheses are the two facts the paper has at this
point (rows `lem_8_1_rotate`, `lem_8_1_not_const`), not the contradictory `c > 0` bundle; they hold at `t = 0`. -/
theorem lem_8_1_clifford_t (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c t : ℝ)
    (hsum : ∀ x : Vec 16, ∑ i, hvec (lem81Fam K c t) x i ^ 2 = (x ⬝ᵥ x) ^ 2)
    (hnc : ∃ x y : Vec 16, x ⬝ᵥ x = 1 ∧ y ⬝ᵥ y = 1 ∧ hvec (lem81Fam K c t) x ≠ hvec (lem81Fam K c t) y) :
    IsSymmCliffordSystem (lem81Fam K c t) :=
  Osserman.Proofs.Lem81.lem_8_1_clifford_t_proved K hK c t hsum hnc

/-- **Lemma 8.1, proof** (line 45 of sec_small_roots.tex): "so $\Omega(t)=H_0(t)\cdots H_8(t)$ is a symmetric
involution"; (hidden) for ANY symmetric Clifford system of nine matrices, reversing the nine anticommuting factors
gives the sign `(-1)^36 = 1`. -/
theorem cliffProd_nine_symm_inv {n : ℕ} (H : Fin 9 → Matrix (Fin n) (Fin n) ℝ) (hH : IsSymmCliffordSystem H) :
    (cliffProd H)ᵀ = cliffProd H ∧ cliffProd H * cliffProd H = 1 :=
  Osserman.Proofs.Lem81.cliffProd_nine_symm_inv_proved H hH

/-- **Lemma 8.1, proof** (lines 46-47 of sec_small_roots.tex): "as nine is odd, $\Omega(0)$ commutes with every
$H_i$" — for ANY symmetric Clifford system of nine matrices, of any size (review a3 MUST-2: the paper's first reason
for `Ω(0) = ±I` gets its own row). -/
theorem cliffProd_nine_commutes {n : ℕ} (H : Fin 9 → Matrix (Fin n) (Fin n) ℝ) (hH : IsSymmCliffordSystem H)
    (i : Fin 9) : cliffProd H * H i = H i * cliffProd H :=
  Osserman.Proofs.Lem81.cliffProd_nine_commutes_proved H hH i

/-- **Lemma 8.1, proof** (lines 47-49 of sec_small_roots.tex): "and, by Section~\ref{sec:Cayley}, the products of the $H_i$
span the symmetric matrices, so a matrix commuting with every $H_i$ is scalar" (`H_i(0) = S_i`). The spanning is the
row `sec6_basis_136` (Section 6); this row proves the conclusion used, a matrix commuting with every `S_i` is scalar,
and also that the `S_i` generate all of `End(ℝ^16)` as an algebra (review a3 MUST-2). -/
theorem std_sys_generate :
    Algebra.adjoin ℝ (Set.range stdSys) = ⊤ ∧
      ∀ M : Matrix (Fin 16) (Fin 16) ℝ, (∀ i, M * stdSys i = stdSys i * M) → ∃ r : ℝ, M = r • 1 :=
  Osserman.Proofs.Lem81.std_sys_generate_proved

/-- **Lemma 8.1, proof** (lines 45-46 of sec_small_roots.tex): "and $\tr\Omega(t)$ is continuous and integer-valued, hence
constant". Stated for ANY continuous family of symmetric Clifford systems of nine matrices (met by a constant family),
so the row does not sit inside the contradiction of `c > 0`; `lem_8_1_c_pos` applies it to `lem81Fam K c`. -/
theorem lem_8_1_trace_const (H : ℝ → Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hcont : ∀ i, Continuous fun t => H t i)
    (hH : ∀ t, IsSymmCliffordSystem (H t)) :
    Continuous (fun t : ℝ => (cliffProd (H t)).trace) ∧ (∀ t : ℝ, ∃ z : ℤ, (cliffProd (H t)).trace = z) ∧
      ∀ t : ℝ, (cliffProd (H t)).trace = (cliffProd (H 0)).trace :=
  Osserman.Proofs.Lem81.lem_8_1_trace_const_proved H hcont hH

/-- **Lemma 8.1, proof** (lines 46-49 of sec_small_roots.tex): "But $\Omega(0)=\pm I$ on $\R^{16}$ (as nine is odd,
$\Omega(0)$ commutes with every $H_i$, and, by Section~\ref{sec:Cayley}, the products of the $H_i$ span the symmetric
matrices, so a matrix commuting with every $H_i$ is scalar)" (`H_i(0) = S_i`). The two reasons are the rows `cliffProd_nine_commutes` and
`std_sys_generate`. -/
theorem lem_8_1_Omega_zero (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) :
    lem81Fam K c 0 = stdSys ∧ (cliffProd stdSys = 1 ∨ cliffProd stdSys = -1) :=
  Osserman.Proofs.Lem81.lem_8_1_Omega_zero_proved K c

/-- **Lemma 8.1, proof** (lines 46-50 of sec_small_roots.tex): "and $\Omega(\pi)=-\Omega(0)$, a contradiction"
(`H_i(π) = -S_i`: nine sign changes). -/
theorem lem_8_1_Omega_pi (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) :
    lem81Fam K c Real.pi = (fun i => -stdSys i) ∧ cliffProd (lem81Fam K c Real.pi) = -cliffProd stdSys :=
  Osserman.Proofs.Lem81.lem_8_1_Omega_pi_proved K c

/-- **Lemma 8.1, proof** (lines 40-50 of sec_small_roots.tex): the case `c > 0` is impossible (the contradiction of
lines 46-50). Route: `lem_8_1_rotate` with `sec6_hopf`, `lem_8_1_sum_ha`, `lem_8_1_sum_a` (sum `q²` for every `t`);
`lem_8_1_not_const`; `lem_8_1_clifford_t`; `cliffProd_nine_symm_inv`; `lem_8_1_trace_const`; `lem_8_1_Omega_zero`
(reasons: `cliffProd_nine_commutes`, `std_sys_generate`), `lem_8_1_Omega_pi`. -/
theorem lem_8_1_c_pos (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) : ¬ 0 < c :=
  Osserman.Proofs.Lem81.lem_8_1_c_pos_proved K hK c hc

/-- **Lemma 8.1, proof** (lines 40, 50 of sec_small_roots.tex), (hidden): `c ≥ 0` (a squared length divided by
`|x|²`), so the cases "$c>0$" and "$c=0$" are all the cases. -/
theorem lem_8_1_c_nonneg (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) : 0 ≤ c :=
  Osserman.Proofs.Lem81.lem_8_1_c_nonneg_proved K c hc

/-- **Lemma 8.1, proof** (lines 50-51 of sec_small_roots.tex): "If $c=0$, then $Kx\in L(x)$, and skewness gives
$Kx\in E(x)$, so $K=0$ by Lemma~\ref{lem:nofield}" (`L(x) = Lstd x`; the last step is `lem_7_1_a`; the conjunct
`K = 0` per review a3 NIT-5). -/
theorem lem_8_1_c_zero (K : Matrix (Fin 16) (Fin 16) ℝ) (hK : Kᵀ = -K) (c : ℝ) (hc0 : c = 0)
    (hc : ∀ x : Vec 16, x ≠ 0 → ∃ w, IsOrthProj (Nstd x) (K *ᵥ x) w ∧ w ⬝ᵥ w = c * (x ⬝ᵥ x)) :
    (∀ x : Vec 16, x ≠ 0 → K *ᵥ x ∈ Lstd x ∧ K *ᵥ x ∈ Estd x) ∧ K = 0 :=
  Osserman.Proofs.Lem81.lem_8_1_c_zero_proved K hK c hc0 hc

/-! ## §8.2: polynomial tools (lines 54-77) -/

/-- **§8.2** (lines 56-60 of sec_small_roots.tex), (hidden): "$A(x)$ denotes the Jacobi operator $\Jac_x$ after one
reduced eigenvalue has been shifted to zero": for `R₀ = R - cR_1` with `c = ev i₀`, the pattern is kept with
eigenvalues `ev i - c` (now `0` at `i₀`, the others distinct and nonzero), and `R₀` is Osserman, resp. Clifford, iff `R`
is. Rows S8.061, S8.080, S8.087 (the shifts), S8.108 and S8.112 ("add back the shift"). -/
theorem s8_shift_to_zero {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ) (hR : PatternEv R m ev)
    (i₀ : Fin k) :
    ∃ R0 : CurvTensor 16, (∀ u v z, R0.op u v z = R.op u v z - ev i₀ • R1fun u v z) ∧
      (∀ x, R0.jacobi x = R.jacobi x - ev i₀ • Pi x) ∧ PatternEv R0 m (fun i => ev i - ev i₀) ∧
      (∀ i, i ≠ i₀ → ev i - ev i₀ ≠ 0) ∧ (R0.IsOsserman ↔ R.IsOsserman) ∧ (R0.IsClifford ↔ R.IsClifford) :=
  Osserman.Proofs.S8TC.s8_shift_to_zero_proved R m ev hR i₀

/-- **§8.2** (lines 60-61 of sec_small_roots.tex): "As $q$ is irreducible, it is a prime element of
$\R[x_1,\ldots,x_{16}]$"; (hidden) so `𝒪` is an integral domain. -/
theorem s8_q_prime : Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal :=
  Osserman.Proofs.QPrime.s8_q_prime_proved

/-- **§8.2** (lines 65-73 of sec_small_roots.tex), (eq:cubicidentities): "The simple eigenfields of [Nik2006,
Lemma~3.1(1), p.~383] satisfy $\ip{P(x)}x=0$, $\norm{P(x)}^2=q^3$, $P(P(x))=-q^4x$, after multiplication by $q$ if they
are linear: equation~(7) of that lemma states them for unit $x$, and homogeneity gives them for all $x$." So (8.1) is
the cited statement `Osserman.Cited.nik2006_lemma_3_1` (odd degree `d ≤ 3` in Section 8; on the unit sphere
`⟨P,x⟩ = 0`, `|P|² = 1`, `P(P(x)) = -x`, the source's eq. (7)) plus the homogeneity step this row states. -/
theorem s8_cubic_identities (d : ℕ) (hd : d = 1 ∨ d = 3) (E : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hE : ∀ j, (E j).IsHomogeneous d)
    (hunit : ∀ x : Vec 16, x ⬝ᵥ x = 1 → evalField E x ⬝ᵥ x = 0 ∧ evalField E x ⬝ᵥ evalField E x = 1 ∧
      evalField E (evalField E x) = -x) :
    let P : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => sqP 16 ^ ((3 - d) / 2) * E j
    (∀ j, (P j).IsHomogeneous 3) ∧ CubicIdentities P :=
  Osserman.Proofs.S8Cubic.s8_cubic_identities_proved d hd E hE hunit

/-! ## Lemma 8.2 (lem:cubic-gcd, lines 79-136): [Nik2006, Lemma 3.5] in the form used here -/

/-- **Lemma 8.2, proof** (lines 87-90 of sec_small_roots.tex): "If every component of $P$ is divisible by $q$, then
$P(x)=qJx$ with $J$ linear, and (eq:cubicidentities) gives $\ip{Jx}x=0$ and $\norm{Jx}^2=q$, so $J$ is skew and
orthogonal." -/
theorem lem_8_2_div_q (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hP : CubicIdentities P) (hq : ∀ j, sqP 16 ∣ P j) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, (∀ j, P j = sqP 16 * linP J j) ∧
      (∀ x : Vec 16, (J *ᵥ x) ⬝ᵥ x = 0 ∧ (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = x ⬝ᵥ x) ∧ Jᵀ = -J ∧ Jᵀ * J = 1 :=
  Osserman.Proofs.Lem82DivQ.lem_8_2_div_q_proved P hP3 hP hq

/-- **Lemma 8.2, proof** (lines 90-92 of sec_small_roots.tex): "the common divisor is homogeneous, as a divisor of a
nonzero homogeneous element of the graded domain $\mathcal O$" (a homogeneous element of `𝒪` is the image of a
homogeneous polynomial). -/
theorem lem_8_2_homog_divisor (d : Ocal) (f : MvPolynomial (Fin 16) ℝ) (n : ℕ) (hf : f.IsHomogeneous n)
    (hf0 : piO f ≠ 0) (hd : d ∣ piO f) :
    ∃ (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ), φ.IsHomogeneous r ∧ d = piO φ :=
  Osserman.Proofs.Lem82.lem_8_2_homog_divisor_proved d f n hf hf0 hd

/-- **Lemma 8.2, proof** (line 92 of sec_small_roots.tex): "the units of $\mathcal O$ are the nonzero constants". -/
theorem lem_8_2_units (u : Ocal) : IsUnit u ↔ ∃ c : ℝ, c ≠ 0 ∧ u = piO (MvPolynomial.C c) :=
  Osserman.Proofs.Lem82.lem_8_2_units_proved u

/-- **Lemma 8.2, proof** (lines 91-93 of sec_small_roots.tex): "its degree $r$ is positive, since the units of
$\mathcal O$ are the nonzero constants, and $r\le3$, since it divides a nonzero cubic" (a homogeneous nonunit divisor
`π(φ)`, `q ∤ φ`, of `π(f)`, `f` a homogeneous cubic with `q ∤ f`). -/
theorem lem_8_2_degree (φ f : MvPolynomial (Fin 16) ℝ) (r : ℕ) (hφ : φ.IsHomogeneous r) (hφq : ¬ sqP 16 ∣ φ)
    (hf : f.IsHomogeneous 3) (hfq : ¬ sqP 16 ∣ f) (hu : ¬ IsUnit (piO φ)) (hd : piO φ ∣ piO f) :
    1 ≤ r ∧ r ≤ 3 :=
  Osserman.Proofs.Lem82.lem_8_2_degree_proved φ f r hφ hφq hf hfq hu hd

/-- **Lemma 8.2, proof** (lines 93-96 of sec_small_roots.tex): "Lifting to $\R[x_1,\ldots,x_{16}]$, we get
$P(x)=\varphi(x)\Psi(x)+qCx$ with $\varphi$ homogeneous of degree $r$ and not divisible by $q$, the components of $\Psi$
homogeneous of degree $3-r$, and $C$ linear" (when not every component is divisible by `q`; `π(φ)` is the common
divisor). General form (review a3 MUST-1): the lift does not use (8.1), so `CubicIdentities P` is NOT a hypothesis
(with it the four hypotheses could never hold together, by `lem_8_2`); the conclusion is the part of `Lem82Lift`
without the hypotheses on `P` (`lem_8_2` adds `hP3` and (8.1) to get `Lem82Lift`). Hypotheses met:
`lem_8_2_lift_hyp_nonvacuous`. -/
theorem lem_8_2_lift (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hdiv : ∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)) (hnd : ¬ ∀ j, sqP 16 ∣ P j) :
    ∃ (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ),
      1 ≤ r ∧ r ≤ 3 ∧ φ.IsHomogeneous r ∧ ¬ sqP 16 ∣ φ ∧ (∀ j, (Ψ j).IsHomogeneous (3 - r)) ∧
      (∀ j, P j = φ * Ψ j + sqP 16 * linP Cm j) ∧ ¬ IsUnit (piO φ) ∧ ∀ j, piO φ ∣ piO (P j) :=
  Osserman.Proofs.Lem82.lem_8_2_lift_proved P hP3 hdiv hnd

/-- **Lemma 8.2, proof** (lines 96-97 of sec_small_roots.tex): "It suffices to show that every component of $\Psi$ is
divisible by $q$" (then every component of `P` is, and `lem_8_2_div_q` applies). -/
theorem lem_8_2_suffices (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P r φ Ψ Cm)
    (hΨ : ∀ j, sqP 16 ∣ Ψ j) : ∀ j, sqP 16 ∣ P j :=
  Osserman.Proofs.Lem82.lem_8_2_suffices_proved P r φ Ψ Cm h hΨ

/-- **Lemma 8.2, proof** (lines 99 and 115 of sec_small_roots.tex), (hidden): the first identity of
(eq:cubicidentities) in the lifted form, "$\varphi\ip\Psi x=-q\ip{Cx}x$" (as polynomials; `quadP Cm = ⟨Cx,x⟩`). -/
theorem lem_8_2_tangency (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P r φ Ψ Cm) :
    φ * ∑ j, Ψ j * X j = -(sqP 16 * quadP Cm) :=
  Osserman.Proofs.Lem82.lem_8_2_tangency_proved P r φ Ψ Cm h

/-- **Lemma 8.2, proof, `r = 3`** (lines 99-101 of sec_small_roots.tex): "If $r=3$, then $\Psi$ is constant and
$\varphi\ip \Psi x=-q\ip{Cx}x$. As $q$ is prime and does not divide $\varphi$, it divides the linear form $\ip \Psi x$, so
$\Psi=0$." -/
theorem lem_8_2_r3 (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 3 φ Ψ Cm) :
    (∃ ψ : Vec 16, ∀ j, Ψ j = MvPolynomial.C (ψ j)) ∧ sqP 16 ∣ ∑ j, Ψ j * X j ∧ ∀ j, Ψ j = 0 :=
  Osserman.Proofs.Lem82R2.lem_8_2_r3_proved lem_8_2_tangency P φ Ψ Cm h

/-- **Lemma 8.2, proof, `r = 2`** (line 103 of sec_small_roots.tex): "If $r=2$, then $\Psi(x)=Bx$ with $B$ linear". -/
theorem lem_8_2_r2_linear (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ Ψ Cm) :
    ∃ B : Matrix (Fin 16) (Fin 16) ℝ, ∀ j, Ψ j = linP B j :=
  Osserman.Proofs.Lem82R2.lem_8_2_r2_linear_proved P φ Ψ Cm h

/-- **Lemma 8.2, proof, `r = 2`** (lines 103-105 of sec_small_roots.tex): "Modulo $q$,
$\norm{P(x)}^2\equiv \varphi(x)^2\norm{Bx}^2$, so $q$ divides $\norm{Bx}^2$, and $B=cU$ with $U$ orthogonal and
$c\ge0$." -/
theorem lem_8_2_r2_conformal (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (B Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ (linP B) Cm) :
    sqP 16 ∣ (∑ j, P j ^ 2) - φ ^ 2 * ∑ j, linP B j ^ 2 ∧ sqP 16 ∣ ∑ j, linP B j ^ 2 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ U ∈ Matrix.orthogonalGroup (Fin 16) ℝ, B = c • U :=
  Osserman.Proofs.Lem82R2.lem_8_2_r2_conformal_proved P φ B Cm h

/-- **Lemma 8.2, proof, `r = 2`** (lines 105-110 of sec_small_roots.tex): "Since $\norm{P(x)}^2=q^3$ and
$P(x)\equiv \varphi(x)Bx$ modulo $q$, we get $0\equiv P(P(x))\equiv \varphi(P(x))\,BP(x)\equiv
\varphi(x)^3\varphi(Bx)\,B^2x \pmod q$" (componentwise, with `f(P(x)) = bind₁ P f`); (hidden) `q(P(x)) = q³ ≡ 0`, and
substitution respects congruences mod `q`. -/
theorem lem_8_2_r2_compose (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (B Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ (linP B) Cm) :
    ∀ j, sqP 16 ∣ bind₁ P (P j) ∧ sqP 16 ∣ bind₁ P (P j) - bind₁ P φ * bind₁ P (linP B j) ∧
      sqP 16 ∣ bind₁ P φ * bind₁ P (linP B j) - φ ^ 3 * bind₁ (linP B) φ * linP (B * B) j :=
  Osserman.Proofs.Lem82R2.lem_8_2_r2_compose_proved P φ B Cm h

/-- **Lemma 8.2, proof, `r = 2`** (line 111 of sec_small_roots.tex): "If $c\ne0$, then $B^2$ is invertible, so $q$
divides $\varphi(Bx)$". The case `c ≠ 0` is refuted in the paper (lines 111-113), so the data of `lem_8_2_r2_compose`
with `c ≠ 0` can never occur; to keep the row checkable (review rule a2-six SHOULD-3) the two inferences are stated in
general: `B = cU`, `c ≠ 0` ⇒ `B²` invertible; and for ANY invertible `B²` and `q ∤ φ`, the congruence of
`lem_8_2_r2_compose` gives `q ∣ φ(Bx)` (met, e.g., by `B = diag(2,1,…,1)`, `φ(y) = q(B⁻¹y)`). -/
theorem lem_8_2_r2_c_ne :
    (∀ (B U : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ), c ≠ 0 → U ∈ Matrix.orthogonalGroup (Fin 16) ℝ → B = c • U →
        IsUnit (B * B).det) ∧
      ∀ (φ : MvPolynomial (Fin 16) ℝ) (B : Matrix (Fin 16) (Fin 16) ℝ), ¬ sqP 16 ∣ φ → IsUnit (B * B).det →
        (∀ j, sqP 16 ∣ φ ^ 3 * bind₁ (linP B) φ * linP (B * B) j) → sqP 16 ∣ bind₁ (linP B) φ :=
  Osserman.Proofs.Lem82R2.lem_8_2_r2_c_ne_proved

/-- **Lemma 8.2, proof, `r = 2`** (lines 111-113 of sec_small_roots.tex): "and the substitution $x=B^{-1}y$ shows that
$c^{-2}\norm y^2$ divides $\varphi(y)$, which is false" (for `B = cU`, `c ≠ 0`: `q ∣ φ(Bx)` forces `q ∣ φ`). -/
theorem lem_8_2_r2_substitute (φ : MvPolynomial (Fin 16) ℝ) (B U : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) (hc : c ≠ 0)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 16) ℝ) (hB : B = c • U) (hdiv : sqP 16 ∣ bind₁ (linP B) φ) :
    sqP 16 ∣ φ :=
  Osserman.Proofs.Lem82R2.lem_8_2_r2_substitute_proved φ B U c hc hU hB hdiv

/-- **Lemma 8.2, proof, `r = 2`** (line 113 of sec_small_roots.tex): "So $c=0$ and $\Psi=0$." -/
theorem lem_8_2_r2 (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ Ψ Cm) :
    ∀ j, Ψ j = 0 :=
  Osserman.Proofs.Lem82R2.lem_8_2_r2_proved P φ Ψ Cm h

/-- **Lemma 8.2, proof, `r = 1`** (line 115 of sec_small_roots.tex): "If $r=1$, then $\varphi$ is a nonzero linear
form". -/
theorem lem_8_2_r1_form (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 φ Ψ Cm) :
    ∃ f : Vec 16, f ≠ 0 ∧ φ = formP f :=
  Osserman.Proofs.Lem82R1a.lem_8_2_r1_form_proved P φ Ψ Cm h

/-- **Lemma 8.2, proof, `r = 1`** (lines 115-117 of sec_small_roots.tex): "and $\varphi\ip \Psi x=-q\ip{Cx}x$ shows
that $\varphi$ divides $\ip{Cx}x$, say $\ip{Cx}x=\varphi(x)\ip ax$ with $a\in\R^{16}$". -/
theorem lem_8_2_r1_div (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : Vec 16) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 (formP f) Ψ Cm) :
    ∃ a : Vec 16, quadP Cm = formP f * formP a :=
  Osserman.Proofs.Lem82R1a.lem_8_2_r1_div_proved P f Ψ Cm h

/-- **Lemma 8.2, proof, `r = 1`** (lines 117-119 of sec_small_roots.tex): "Replacing $C$ by $\tilde Cx=Cx-\varphi(x)a$
and $\Psi$ by $\tilde \Psi=\Psi+qa$ keeps $P=\varphi\tilde \Psi+q\tilde Cx$ and makes $\tilde C$ skew"
(`C̃ = C - afᵀ`). -/
theorem lem_8_2_r1_skew (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : Vec 16) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 (formP f) Ψ Cm) (a : Vec 16)
    (ha : quadP Cm = formP f * formP a) :
    let Ct := Cm - vecMulVec a f
    let Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => Ψ j + sqP 16 * MvPolynomial.C (a j)
    (∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) ∧ Ctᵀ = -Ct ∧ ∀ j, (Ψt j).IsHomogeneous 2 :=
  Osserman.Proofs.Lem82R1a.lem_8_2_r1_skew_proved P f Ψ Cm h a ha

/-- **Lemma 8.2, proof, `r = 1`** (lines 119-120 of sec_small_roots.tex): "Modulo $\varphi$, the identity
$\norm{P(x)}^2=q^3$ shows that $\varphi$ divides $q-\norm{\tilde Cx}^2=x^T(I+\tilde C^2)x$". -/
theorem lem_8_2_r1_divides (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) :
    formP f ∣ sqP 16 - (∑ j, linP Ct j ^ 2) ∧ sqP 16 - (∑ j, linP Ct j ^ 2) = quadP (1 + Ct * Ct) :=
  Osserman.Proofs.Lem82R1a.lem_8_2_r1_divides_proved P hP f Ψt Ct hdec hCt

/-- **Lemma 8.2, proof, `r = 1`** (lines 120-122 of sec_small_roots.tex): "A quadratic form divisible by a linear form
has rank at most two and vanishes at a nonzero vector of every plane, so it is definite on no plane". -/
theorem quad_div_linear (f : Vec 16) (hf : f ≠ 0) (Mq : Matrix (Fin 16) (Fin 16) ℝ) (hM : Mqᵀ = Mq)
    (hdiv : formP f ∣ quadP Mq) :
    Mq.rank ≤ 2 ∧ ∀ W : Submodule ℝ (Vec 16), Module.finrank ℝ W = 2 →
      ∃ v ∈ W, v ≠ 0 ∧ v ⬝ᵥ (Mq *ᵥ v) = 0 :=
  Osserman.Proofs.Lem82R1a.quad_div_linear_proved f hf Mq hM hdiv

/-- **Lemma 8.2, proof, `r = 1`** (lines 122-124 of sec_small_roots.tex): "as every eigenvalue of the symmetric matrix
$I+\tilde C^2$ has even multiplicity"; (hidden) for the eigenvalue `1` (the kernel of `C̃`) this uses that the dimension
16 is even. Stated for every skew `S` on `ℝ^16` and every real `μ` (multiplicity 0 is even). -/
theorem skew16_even_mult (S : Matrix (Fin 16) (Fin 16) ℝ) (hS : Sᵀ = -S) (μ : ℝ) :
    Even (Module.finrank ℝ ↥(Module.End.eigenspace (Matrix.toLin' (1 + S * S)) μ)) :=
  Osserman.Proofs.Lem82R1a.skew16_even_mult_proved S hS μ

/-- **Lemma 8.2, proof, `r = 1`** (lines 123-124 of sec_small_roots.tex): "$I+\tilde C^2=0$, and $\tilde C$ is
orthogonal" (for a skew `S` with `x^T(I+S^2)x` divisible by a nonzero linear form). -/
theorem lem_8_2_r1_orth (S : Matrix (Fin 16) (Fin 16) ℝ) (hS : Sᵀ = -S) (f : Vec 16) (hf : f ≠ 0)
    (hdiv : formP f ∣ quadP (1 + S * S)) : 1 + S * S = 0 ∧ Sᵀ * S = 1 :=
  Osserman.Proofs.Lem82R1a.lem_8_2_r1_orth_proved S hS f hf hdiv

/-- **Lemma 8.2, proof, `r = 1`** (lines 124-126 of sec_small_roots.tex): "The third identity in (eq:cubicidentities)
now reads $\varphi(P(x))\tilde \Psi(P(x))=-q^3\varphi(x)\tilde C\tilde \Psi(x)$" (as polynomials). -/
theorem lem_8_2_r1_third (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1) :
    ∀ j, bind₁ P (formP f) * bind₁ P (Ψt j) =
      -(sqP 16 ^ 3 * formP f * ∑ k, MvPolynomial.C (Ct j k) * Ψt k) :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_third_proved P hP f Ψt Ct hdec hCt hCo

/-- **Lemma 8.2, proof, `r = 1`** (lines 126-128 of sec_small_roots.tex): "On the hyperplane $\varphi=0$ we have
$P(x)=q\tilde Cx$, so $\varphi(\tilde Cx)\tilde \Psi(\tilde Cx)$ vanishes there". -/
theorem lem_8_2_r1_hyperplane (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1)
    (hΨt : ∀ j, (Ψt j).IsHomogeneous 2) :
    ∀ x : Vec 16, f ⬝ᵥ x = 0 → evalField P x = (x ⬝ᵥ x) • (Ct *ᵥ x) ∧
      ∀ j, (f ⬝ᵥ (Ct *ᵥ x)) * eval (Ct *ᵥ x) (Ψt j) = 0 :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_hyperplane_proved P hP f Ψt Ct hdec hCt hCo hΨt

/-- **Lemma 8.2, proof, `r = 1`** (lines 128-130 of sec_small_roots.tex): "Writing $\varphi(x)=\ip fx$, the form
$\varphi(\tilde Cx)=-\ip{\tilde Cf}x$ does not vanish identically on $f^\perp$, since $\tilde Cf\ne0$ is orthogonal to
$f$." -/
theorem lem_8_2_r1_nonvanish (S : Matrix (Fin 16) (Fin 16) ℝ) (hS : Sᵀ = -S) (hSo : Sᵀ * S = 1) (f : Vec 16)
    (hf : f ≠ 0) :
    (∀ x : Vec 16, f ⬝ᵥ (S *ᵥ x) = -((S *ᵥ f) ⬝ᵥ x)) ∧ S *ᵥ f ≠ 0 ∧ (S *ᵥ f) ⬝ᵥ f = 0 ∧
      ∃ x : Vec 16, f ⬝ᵥ x = 0 ∧ f ⬝ᵥ (S *ᵥ x) ≠ 0 :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_nonvanish_proved S hS hSo f hf

/-- **Lemma 8.2, proof, `r = 1`** (lines 130-132 of sec_small_roots.tex): "Hence $\varphi$ divides every component of
$\tilde \Psi(\tilde Cx)$, and, as $\tilde C^{-1}=-\tilde C$, we get $\tilde \Psi(x)=\varphi(\tilde Cx)B'x$ with $B'$
linear" (`g(C̃x) = bind₁ (linP C̃) g`). -/
theorem lem_8_2_r1_factor (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16) (hf : f ≠ 0)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1)
    (hΨt : ∀ j, (Ψt j).IsHomogeneous 2) :
    (∀ j, formP f ∣ bind₁ (linP Ct) (Ψt j)) ∧
      ∃ B' : Matrix (Fin 16) (Fin 16) ℝ, ∀ j, Ψt j = bind₁ (linP Ct) (formP f) * linP B' j :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_factor_proved P hP f hf Ψt Ct hdec hCt hCo hΨt

/-- **Lemma 8.2, proof, `r = 1`** (lines 133-134 of sec_small_roots.tex): "where $\varphi(x)\varphi(\tilde Cx)$ is a
quadratic form not divisible by $q$" (for `f ≠ 0` and `C̃` orthogonal). -/
theorem lem_8_2_r1_not_div (S : Matrix (Fin 16) (Fin 16) ℝ) (hSo : Sᵀ * S = 1) (f : Vec 16) (hf : f ≠ 0) :
    ¬ sqP 16 ∣ formP f * bind₁ (linP S) (formP f) :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_not_div_proved S hSo f hf

/-- **Lemma 8.2, proof, `r = 1`** (lines 132-134 of sec_small_roots.tex): "Then
$P(x)=\varphi(x)\varphi(\tilde Cx)\,B'x+q\tilde Cx$ ... and the case $r=2$ applies" (the new decomposition is a lift
with `r = 2`). -/
theorem lem_8_2_r1_to_r2 (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hP : CubicIdentities P) (f : Vec 16) (hf : f ≠ 0) (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Ct B' : Matrix (Fin 16) (Fin 16) ℝ) (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct)
    (hCo : Ctᵀ * Ct = 1) (hB' : ∀ j, Ψt j = bind₁ (linP Ct) (formP f) * linP B' j) :
    Lem82Lift P 2 (formP f * bind₁ (linP Ct) (formP f)) (linP B') Ct :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_to_r2_proved P hP3 hP f hf Ψt Ct B' hdec hCt hCo hB'

/-- **Lemma 8.2, proof, `r = 1`** (lines 134-135 of sec_small_roots.tex): "$B'=0$, so $\tilde \Psi=0$, and $\Psi=-qa$ is
divisible by $q$". -/
theorem lem_8_2_r1 (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 1 φ Ψ Cm) :
    ∀ j, sqP 16 ∣ Ψ j :=
  Osserman.Proofs.Lem82R1.lem_8_2_r1_given lem_8_2_r1_form lem_8_2_r1_div lem_8_2_r1_skew lem_8_2_r1_divides
    lem_8_2_r1_orth lem_8_2_r2 P φ Ψ Cm h

/-- **Lemma 8.2** (lem:cubic-gcd, lines 79-84 of sec_small_roots.tex): "Let $P\colon\R^{16}\to\R^{16}$ have
homogeneous cubic components that satisfy (eq:cubicidentities). If the images in $\mathcal O$ of the sixteen components
of $P$ have a nonunit common divisor, then $P(x)=qJx$ for an orthogonal skew map $J$." ADAPTED-CITED: [Nik2006, Lemma 3.5,
pp. 388-390] used outside its standing hypotheses ("its proof uses neither", lines 73-77; flag F2), so a theorem to
PROVE (proof: lines 86-136). -/
theorem lem_8_2 (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3) (hP : CubicIdentities P)
    (hdiv : ∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧ ∀ x : Vec 16, evalField P x = (x ⬝ᵥ x) • (J *ᵥ x) :=
  Osserman.Proofs.Lem82.lem_8_2_proved lem_8_2_r1 lem_8_2_r2 lem_8_2_r3 P hP3 hP hdiv

/-! ## The three-column step (lines 138-169): Nik2006 pp. 387-389 as written in the paper (ADAPTED, flag F3) -/

/-- **Three-column step** (lines 142-145 of sec_small_roots.tex), (eq:rankoneK): "After rescaling the columns by
nonzero constants, their images $p_i\in\mathcal O^{16}$ satisfy $p_1p_1^T+p_2p_2^T=p_3p_3^T$" (constants `√|w_i|`). -/
theorem s8_tc_rankone (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) :
    (∀ i, Real.sqrt |wt i| ≠ 0) ∧ ∀ a b : Fin 16,
      tcImg wt P 0 a * tcImg wt P 0 b + tcImg wt P 1 a * tcImg wt P 1 b = tcImg wt P 2 a * tcImg wt P 2 b :=
  Osserman.Proofs.S8TC.s8_tc_rankone_proved R μ P wt h

/-- **Three-column step** (lines 147-151 of sec_small_roots.tex): "The right side of (eq:rankoneK) has rank at most one,
so every $2\times2$ minor of the left side vanishes; by Lagrange's identity its principal minor in rows and columns
$a,b$ is $(p_{1a}p_{2b}-p_{2a}p_{1b})^2$, so, $\mathcal O$ being a domain, all the minors $p_{1a}p_{2b}-p_{2a}p_{1b}$
of $[p_1\ p_2]$ vanish". -/
theorem s8_tc_minors (p : Fin 3 → Fin 16 → Ocal) (hp : ∀ a b, p 0 a * p 0 b + p 1 a * p 1 b = p 2 a * p 2 b) :
    ∀ a b : Fin 16,
      (p 0 a ^ 2 + p 1 a ^ 2) * (p 0 b ^ 2 + p 1 b ^ 2) - (p 0 a * p 0 b + p 1 a * p 1 b) ^ 2 =
        (p 0 a * p 1 b - p 1 a * p 0 b) ^ 2 ∧
      p 2 a ^ 2 * p 2 b ^ 2 - (p 2 a * p 2 b) ^ 2 = 0 ∧ p 0 a * p 1 b - p 1 a * p 0 b = 0 :=
  Osserman.Proofs.S8TC.s8_tc_minors_of_s8_q_prime s8_q_prime p hp

/-- **Three-column step** (lines 151-152 of sec_small_roots.tex): "If some $p_i=0$, then $P_i$ is $q$ times a linear
eigenfield" (the linear field is also skew and orthogonal, by norm and tangency; stated, as it is used). -/
theorem s8_tc_zero_column (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (i : Fin 3) (hi : tcImg wt P i = 0) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      (∀ x : Vec 16, evalField (P i) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ i) (linP J) :=
  Osserman.Proofs.S8TC.s8_tc_zero_column_proved R μ P wt h i hi

/-- **Three-column step** (lines 152-153 of sec_small_roots.tex): "Otherwise unique factorization gives a primitive $v$
with $p_1=u_1v$, $p_2=u_2v$" (primitive: every common divisor of the components of `v` is a unit). -/
theorem s8_tc_primitive (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hne : ∀ i, tcImg wt P i ≠ 0) :
    ∃ (u0 u1 : Ocal) (v : Fin 16 → Ocal), (∀ d : Ocal, (∀ a, d ∣ v a) → IsUnit d) ∧
      tcImg wt P 0 = u0 • v ∧ tcImg wt P 1 = u1 • v :=
  Osserman.Proofs.S8TC.s8_tc_primitive_of_s8_q_prime s8_q_prime R μ P wt h hne

/-- **Three-column step** (lines 153-154 of sec_small_roots.tex): "then (eq:rankoneK) gives $p_3=u_3v$ and
$u_1^2+u_2^2=u_3^2$". -/
theorem s8_tc_third (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (u0 u1 : Ocal) (v : Fin 16 → Ocal)
    (hv : ∀ d : Ocal, (∀ a, d ∣ v a) → IsUnit d) (h0 : tcImg wt P 0 = u0 • v) (h1 : tcImg wt P 1 = u1 • v) :
    ∃ u3 : Ocal, tcImg wt P 2 = u3 • v ∧ u0 ^ 2 + u1 ^ 2 = u3 ^ 2 :=
  Osserman.Proofs.S8TC.s8_tc_third_of_s8_q_prime s8_q_prime R μ P wt h u0 u1 v hv h0 h1

/-- **Three-column step** (lines 154-155 of sec_small_roots.tex): "a nonzero component of $v$ gives a square root of
$u_1^2+u_2^2$ in the fraction field" (`z = p_{3a}/v_a`). -/
theorem s8_tc_sqrt_frac (u0 u1 : Ocal) (v p2 : Fin 16 → Ocal)
    (hp : ∀ a b, (u0 ^ 2 + u1 ^ 2) * (v a * v b) = p2 a * p2 b) (a : Fin 16) (ha : v a ≠ 0) :
    ∃ z : FractionRing Ocal, z ^ 2 = algebraMap Ocal (FractionRing Ocal) (u0 ^ 2 + u1 ^ 2) ∧
      z * algebraMap Ocal (FractionRing Ocal) (v a) = algebraMap Ocal (FractionRing Ocal) (p2 a) :=
  Osserman.Proofs.S8TC.s8_tc_sqrt_frac_of_s8_q_prime s8_q_prime u0 u1 v p2 hp a ha

/-- **Three-column step** (lines 155-156 of sec_small_roots.tex): "integral over the integrally closed ring
$\mathcal O$, hence in $\mathcal O$" (an element of `Frac(𝒪)` whose square lies in `𝒪` lies in `𝒪`; `𝒪` is a UFD,
`Osserman.Cited.nik2006_thm_3_1`). -/
theorem s8_tc_integral (z : FractionRing Ocal) (y : Ocal) (hz : z ^ 2 = algebraMap Ocal (FractionRing Ocal) y) :
    ∃ y' : Ocal, z = algebraMap Ocal (FractionRing Ocal) y' :=
  Osserman.Proofs.S8TC.s8_tc_integral_of_s8_q_prime s8_q_prime z y hz

/-- **Three-column step** (line 156 of sec_small_roots.tex): "cross entries fix one sign in all components" (if
`(u₃v)(u₃v)ᵀ = p₃p₃ᵀ` then `p₃ = ±u₃v` with one sign). -/
theorem s8_tc_sign (u3 : Ocal) (v p2 : Fin 16 → Ocal) (hp : ∀ a b, (u3 * v a) * (u3 * v b) = p2 a * p2 b) :
    p2 = u3 • v ∨ p2 = (-u3) • v :=
  Osserman.Proofs.S8TC.s8_tc_sign_of_s8_q_prime s8_q_prime u3 v p2 hp

/-- **Three-column step** (lines 157-159 of sec_small_roots.tex): "Suppose the negative column comes from a simple
eigenvalue. If $u_3$ is a nonunit, Lemma~\ref{lem:cubic-gcd} makes $P_3/q$ linear" (`P 2` satisfies (8.1)). -/
theorem s8_tc_nonunit (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hP2 : CubicIdentities (P 2)) (u3 : Ocal) (v : Fin 16 → Ocal)
    (h2 : tcImg wt P 2 = u3 • v) (hu : ¬ IsUnit u3) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      (∀ x : Vec 16, evalField (P 2) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ 2) (linP J) :=
  Osserman.Proofs.S8TC.s8_tc_nonunit_of_lem_8_2 lem_8_2 R μ P wt h hP2 u3 v h2 hu

/-- **Three-column step** (lines 159-160 of sec_small_roots.tex): "If $u_3$ is a unit, homogeneity makes $p_1,p_2$
constant multiples of $p_3$". -/
theorem s8_tc_unit_const (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (u0 u1 u3 : Ocal) (v : Fin 16 → Ocal)
    (h0 : tcImg wt P 0 = u0 • v) (h1 : tcImg wt P 1 = u1 • v) (h2 : tcImg wt P 2 = u3 • v) (hu : IsUnit u3) :
    ∃ k0 k1 : ℝ, tcImg wt P 0 = piO (MvPolynomial.C k0) • tcImg wt P 2 ∧
      tcImg wt P 1 = piO (MvPolynomial.C k1) • tcImg wt P 2 :=
  Osserman.Proofs.S8TC.s8_tc_unit_const_proved R μ P wt h u0 u1 u3 v h0 h1 h2 hu

/-- **Three-column step** (lines 160-165 of sec_small_roots.tex), (eq:linearcombination): "and a constant combination
of the original fields satisfies $c_1P_1(x)+c_2P_2(x)=qJx$, $c_1^2+c_2^2=1$, with $J$ orthogonal and skew (by norm and
tangency)". -/
theorem s8_tc_lincomb (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (k0 k1 : ℝ)
    (h0 : tcImg wt P 0 = piO (MvPolynomial.C k0) • tcImg wt P 2)
    (h1 : tcImg wt P 1 = piO (MvPolynomial.C k1) • tcImg wt P 2) (h2 : tcImg wt P 2 ≠ 0) :
    ∃ (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ), c1 ^ 2 + c2 ^ 2 = 1 ∧ Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x) :=
  Osserman.Proofs.S8TC.s8_tc_lincomb_proved R μ P wt h k0 k1 h0 h1 h2

/-- **Three-column step** (lines 165-166 of sec_small_roots.tex): "If $P_1,P_2$ have the same eigenvalue, this is a
linear eigenfield". -/
theorem s8_tc_same_eigen (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hμ : μ 0 = μ 1) (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ)
    (hc : c1 ^ 2 + c2 ^ 2 = 1)
    (hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x)) :
    IsEigenfield R (μ 0) (linP J) :=
  Osserman.Proofs.S8TC.s8_tc_same_eigen_proved R μ P wt h hμ c1 c2 J hc hJ

/-- **Three-column step** (lines 166-169 of sec_small_roots.tex): "Otherwise $Jx$ has constant coordinates in their
moving orthonormal frame on the unit sphere, so subtracting $CR_J$, for any constant $C$, leaves an Osserman tensor"
(`R` Osserman, as everywhere in Section 8). -/
theorem s8_tc_frame_osserman (R : CurvTensor 16) (hO : R.IsOsserman) (μ : Fin 3 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hμ : μ 0 ≠ μ 1)
    (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ) (hc : c1 ^ 2 + c2 ^ 2 = 1)
    (hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x)) :
    (∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x = c1 • evalField (P 0) x + c2 • evalField (P 1) x) ∧
      ∀ Cc : ℝ, ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - Cc • RJfun J u v z) ∧ R'.IsOsserman :=
  Osserman.Proofs.S8TC.s8_tc_frame_osserman_proved R hO μ P wt h hμ c1 c2 J hc hJ

/-- **Three-column step, outcome** (lines 151-166 of sec_small_roots.tex, as used at lines 234-237 and 260-268): when
the negative column `P 2` comes from a simple eigenvalue, either some column is `q` times a linear (skew, orthogonal)
eigenfield ("If some $p_i=0$", the nonunit case), or (eq:linearcombination) holds (the unit case). -/
theorem s8_tc_outcome (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hP2 : CubicIdentities (P 2)) :
    (∃ (i : Fin 3) (J : Matrix (Fin 16) (Fin 16) ℝ), Jᵀ = -J ∧ Jᵀ * J = 1 ∧
        (∀ x : Vec 16, evalField (P i) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ i) (linP J)) ∨
      ∃ (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ), c1 ^ 2 + c2 ^ 2 = 1 ∧ Jᵀ = -J ∧ Jᵀ * J = 1 ∧
        ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x) :=
  Osserman.Proofs.S8TC.s8_tc_outcome_of_lem_8_2 lem_8_2 R μ P wt h hP2

/-! ## General steps used in §8.3-8.6 (hidden in the paper) -/

/-- **§8.3-8.5, spectral projectors** (lines 177-180, 227-229, 257-258 of sec_small_roots.tex), (hidden; S8.109): for
the shifted tensor (`ev i₀ = 0`) and orthogonal cubic eigenfields of squared norm `q³` that fill every eigenspace other
than those of `0` and `λ = ev i₁`, `∑_j μ_j(μ_j - λ)P_jP_jᵀ = qA(A - λqI)` with `A(x) = J_x`. One lemma for (eq:twocolumn)
and the identities of §8.4 and §8.5. -/
theorem s8_spectral_identity {k r : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ)
    (hR : PatternEv R m ev) (hsum : ∑ i, m i = 15) (i0 i1 : Fin k) (h01 : i0 ≠ i1) (h0 : ev i0 = 0)
    (P : Fin r → Fin 16 → MvPolynomial (Fin 16) ℝ) (μ : Fin r → ℝ) (hP3 : ∀ j a, (P j a).IsHomogeneous 3)
    (hPe : ∀ j, IsEigenfield R (μ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ 3 else 0)
    (hμ : ∀ j, ∃ i, i ≠ i0 ∧ i ≠ i1 ∧ μ j = ev i)
    (hcount : ∀ i, i ≠ i0 → i ≠ i1 → (Finset.univ.filter fun j => μ j = ev i).card = m i) :
    ∀ x : Vec 16, ∑ j, (μ j * (μ j - ev i1)) • vecMulVec (evalField (P j) x) (evalField (P j) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev i1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) :=
  Osserman.Proofs.S8Gen.s8_spectral_identity_proved R m ev hR hsum i0 i1 h01 h0 P μ hP3 hPe hPo hμ hcount

/-- **§8.3-8.5, moving a linear eigenfield** (lines 182-183, 237-238, 264-265 of sec_small_roots.tex), (hidden;
S8.110): if `Jx` (`J` skew and orthogonal) is an eigenfield of `ev i₁`, then `R' = R - (ev i₁ - ev i₂)R_J` moves that
one direction from `ev i₁` to `ev i₂`: the multiplicities become `m i₁ - 1` and `m i₂ + 1`, the others are unchanged,
and `R'` is Osserman. -/
theorem s8_move_eigenfield {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (ev : Fin k → ℝ) (hR : PatternEv R m ev)
    (hsum : ∑ i, m i = 15) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) (i1 i2 : Fin k)
    (h12 : i1 ≠ i2) (hJ : IsEigenfield R (ev i1) (linP J)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - (ev i1 - ev i2) • RJfun J u v z) ∧
      (∀ x, R'.jacobi x = R.jacobi x - (ev i1 - ev i2) • jfam J x) ∧ R'.IsOsserman ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x (ev i1) = m i1 - 1 ∧ R'.redMult x (ev i2) = m i2 + 1 ∧
        ∀ i, i ≠ i1 → i ≠ i2 → R'.redMult x (ev i) = m i :=
  Osserman.Proofs.S8Gen.s8_move_eigenfield_proved R m ev hR hsum J hJs hJo i1 i2 h12 hJ

/-- **§8.3-8.5, moving along a constant combination** (lines 166-169, 212-215, 269-274, 291-292 of
sec_small_roots.tex), (hidden; S8.110): if at every unit `x`, `Jx = ∑ c_iF_i(x)` with constant `c_i`, for orthonormal
reduced eigenvectors `F_i(x)` of constant eigenvalues `μ_i`, then `R - CR_J` is Osserman for every constant `C`. -/
theorem s8_move_frame {k : ℕ} (R : CurvTensor 16) (hO : R.IsOsserman) (F : Fin k → Vec 16 → Vec 16) (μ : Fin k → ℝ)
    (hF : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, F i x ∈ Module.End.eigenspace (R.jacobiMap x) (μ i) ⊓ perp x)
    (hFo : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i l, F i x ⬝ᵥ F l x = if i = l then 1 else 0)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (cJ : Fin k → ℝ) (hJ : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x = ∑ i, cJ i • F i x)
    (Cc : ℝ) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - Cc • RJfun J u v z) ∧ R'.IsOsserman :=
  Osserman.Proofs.S8TC.s8_move_frame_proved R hO F μ hF hFo J cJ hJ Cc

/-- **§8.3, opposite signs** (lines 213-217 of sec_small_roots.tex), (hidden): "Lemma~\ref{lem:constantprojection}
excludes a Cayley endpoint" — after conjugating by the `T` of the Cayley form, `K = TJT⁻¹` meets Lemma 8.1. Stated for a
two-eigenvalue tensor of multiplicities `(8, 7)` and an orthogonal skew `J` whose projection onto the multiplicity-8
eigenspace has constant squared length on the unit sphere (by `lem_8_1_pythagoras` this is the same as constant
lengths onto both eigenspaces). -/
theorem s8_cayley_excluded (R' : CurvTensor 16) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R'.redMult x μ₁ = 8 ∧ R'.redMult x μ₂ = 7)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hproj : ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) μ₁ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c) :
    ¬ IsCayleyType R' :=
  Osserman.Proofs.S83.s8_cayley_excluded_proved R' μ₁ μ₂ hne hpat J hJs hJo hproj

/-- **§8.3** (lines 188-191 of sec_small_roots.tex): "A Clifford structure with $\nu=8$ (the $J_i$ of $\eta_i=0$ dropped)
gives its base eigenvalue multiplicity exactly $15-\nu=7$, the dimension of $x^\perp\cap(\sum_i\R J_ix)^\perp$"; stated
for every `ν` (all `η_i ≠ 0`). -/
theorem s8_clifford_base_mult {ν : ℕ} (R' : CurvTensor 16) (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ) (hη : ∀ α, η α ≠ 0)
    (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      Module.End.eigenspace (R'.jacobiMap x) l0 ⊓ perp x = perp x ⊓ ⨅ α, perp (Jα α *ᵥ x) ∧
        R'.redMult x l0 = 15 - ν :=
  Osserman.Proofs.S8TC.s8_clifford_base_mult_proved R' Jα hJ l0 η hη hjac

/-- **Uses of [Nik2006, Proposition 2.1]** (lines 185-186, 216-217, 246-247, 265-266, 289 of sec_small_roots.tex):
the patterns with an eigenvalue of multiplicity nine that occur, `(9,6)`, `(9,5,1)`, `(9,4,2)`, `(9,4,1,1)`, are
Clifford (from `Osserman.Cited.nik2006_prop_2_1` and `hasPattern_osserman`). -/
theorem s8_prop21_uses (R : CurvTensor 16)
    (h : HasPattern R ![9, 6] ∨ HasPattern R ![9, 5, 1] ∨ HasPattern R ![9, 4, 2] ∨ HasPattern R ![9, 4, 1, 1]) :
    R.IsClifford :=
  Osserman.Proofs.S83.s8_prop21_uses_proved R h

/-! ## §8.3: two simple eigenvalues, `(M,N,1,1)`, `(M,N) = (7,6)` or `(8,5)` (lines 171-219) -/

/-- **§8.3** (lines 175-176 of sec_small_roots.tex): "By [Nik2006, Lemma~3.1] there are cubic normalized eigenfields
$P_1,P_2$ (linear ones homogenized by $q$)" for the simple eigenvalues `μ = ev 2`, `σ = ev 3` of the shifted tensor
(a use of `Osserman.Cited.nik2006_lemma_3_1`, `k = 4`, degree `≤ 3`, with `s8_cubic_identities`). -/
theorem s8_3_fields (R : CurvTensor 16) (M N : ℕ) (hMN : (M = 7 ∧ N = 6) ∨ (M = 8 ∧ N = 5)) (ev : Fin 4 → ℝ)
    (hR : PatternEv R ![M, N, 1, 1] ev) (h0 : ev 0 = 0) :
    ∃ P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ, Sec83Data R M N ev P :=
  Osserman.Proofs.S83.s8_3_fields_proved s8_cubic_identities R M N hMN ev hR h0

/-- **§8.3** (lines 177-180 of sec_small_roots.tex), (eq:twocolumn): "the spectral projectors give
$\mu(\mu-\lambda)P_1P_1^T+\sigma(\sigma-\lambda)P_2P_2^T=qA(A-\lambda qI)$" (`λ = ev 1`, `μ = ev 2`, `σ = ev 3`,
`A(x) = J_x`; at every `x`). -/
theorem s8_3_twocolumn (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) :
    ∀ x : Vec 16, (ev 2 * (ev 2 - ev 1)) • vecMulVec (evalField (P 0) x) (evalField (P 0) x) +
        (ev 3 * (ev 3 - ev 1)) • vecMulVec (evalField (P 1) x) (evalField (P 1) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) :=
  Osserman.Proofs.S83.s8_3_twocolumn_proved s8_spectral_identity R M N ev P h

/-- **§8.3** (lines 181-182 of sec_small_roots.tex): "If the two coefficients have the same sign, the sum-of-squares
lemma on the diagonal makes both fields $q$ times linear ones" (first: every component divisible by `q`). -/
theorem s8_3_same_sign (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (hs : 0 < (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1))) :
    ∀ i j, sqP 16 ∣ P i j :=
  Osserman.Proofs.S83.s8_3_same_sign_proved s8_spectral_identity R M N ev P h hs

/-- **§8.3** (line 182 of sec_small_roots.tex): "... both fields $q$ times linear ones" (skew and orthogonal linear
eigenfields, as in `lem_8_2_div_q`). -/
theorem s8_3_linear_fields (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (hq : ∀ i j, sqP 16 ∣ P i j) :
    ∃ J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ, (∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1) ∧
      (∀ i (x : Vec 16), evalField (P i) x = (x ⬝ᵥ x) • (J i *ᵥ x)) ∧
      IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1)) :=
  Osserman.Proofs.S83.s8_3_linear_fields_proved lem_8_2_div_q R M N ev P h hq

/-- **§8.3** (lines 182-184 of sec_small_roots.tex): "Moving one simple eigenvalue into each large eigenvalue gives the
pattern $(M+1,N+1)$, that is $(8,7)$ or $(9,6)$" (here `μ` into `0`, `σ` into `λ`; the other assignment is the same
row after exchanging `(ev 2, P 0)` and `(ev 3, P 1)`). -/
theorem s8_3_move_both (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ) (hJ : ∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1)
    (hJe : IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1))) :
    ∃ Rt : CurvTensor 16,
      (∀ u v z, Rt.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z - (ev 3 - ev 1) • RJfun (J 1) u v z) ∧
      PatternEv Rt ![M + 1, N + 1] ![0, ev 1] ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → J 0 *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) 0 ∧
        J 1 *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) (ev 1) :=
  Osserman.Proofs.S83.s8_3_move_both_proved s8_move_eigenfield R M N ev P h J hJ hJe

/-- **§8.3** (lines 184-185 of sec_small_roots.tex): "the first [$(8,7)$] is classified by Theorem~\ref{thm:A}, with
Cayley excluded by Lemma~\ref{lem:nofield}" (the moved field `J_0x` lies in one eigen-distribution; `thm_C` and
`thm_E_no_cayley`). -/
theorem s8_3_endpoint_87 (Rt : CurvTensor 16) (lam : ℝ) (hpat : PatternEv Rt ![8, 7] ![0, lam])
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hfield : ∀ x : Vec 16, x ⬝ᵥ x = 1 → J *ᵥ x ∈ Module.End.eigenspace (Rt.jacobiMap x) 0) :
    Rt.IsClifford :=
  Osserman.Proofs.S83.s8_3_endpoint_87_proved Rt lam hpat J hJs hJo hfield

/-- **§8.3** (lines 186-188 of sec_small_roots.tex): "Restore the two rank-one terms with [Nik2006, Lemma~3.2(1)],
first the one moved into $\lambda$ and then the one moved into $0$" (`lem_nik_3_2_1` twice; the intermediate tensor
`R - μR_{J_0}` is Osserman of pattern `(M+1, N, 1)`). -/
theorem s8_3_restore_two (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P)
    (J : Fin 2 → Matrix (Fin 16) (Fin 16) ℝ) (hJ : ∀ i, (J i)ᵀ = -J i ∧ (J i)ᵀ * J i = 1)
    (hJe : IsEigenfield R (ev 2) (linP (J 0)) ∧ IsEigenfield R (ev 3) (linP (J 1))) (Rt : CurvTensor 16)
    (hRt : ∀ u v z, Rt.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z - (ev 3 - ev 1) • RJfun (J 1) u v z)
    (hC : Rt.IsClifford) :
    ∃ R1 : CurvTensor 16, (∀ u v z, R1.op u v z = R.op u v z - ev 2 • RJfun (J 0) u v z) ∧
      PatternEv R1 ![M + 1, N, 1] ![0, ev 1, ev 3] ∧ R1.IsClifford ∧ R.IsClifford :=
  Osserman.Proofs.S83.s8_3_restore_two_proved s8_move_eigenfield R M N ev P h J hJ hJe Rt hRt hC

/-- **§8.3** (lines 191-195 of sec_small_roots.tex): "The intermediate pattern $(M+1,N,1)$, that is $(8,6,1)$ or
$(9,5,1)$, has no eigenvalue of multiplicity seven, so its Clifford structures have $\nu\le7$" (structures with every
`η_i ≠ 0`). -/
theorem s8_3_intermediate_nu (R' : CurvTensor 16) (hpat : HasPattern R' ![8, 6, 1] ∨ HasPattern R' ![9, 5, 1])
    {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hη : ∀ α, η α ≠ 0) (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν ≤ 7 :=
  Osserman.Proofs.S83.s8_3_intermediate_nu_proved R' hpat Jα hJ l0 η hη hjac

/-- **§8.3** (line 195 of sec_small_roots.tex): "This proves the claim" for linear fields (same signs, lines 181-195),
and line 201-202: "If both vanish, the linear-field argument above applies". -/
theorem s8_3_linear_case (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (hq : ∀ i j, sqP 16 ∣ P i j) :
    R.IsClifford :=
  Osserman.Proofs.S83.s8_3_linear_case_proved lem_8_2_div_q s8_move_eigenfield R M N ev P h hq

/-- **§8.3, opposite signs** (lines 197-201 of sec_small_roots.tex): "put $a^2=\mu(\mu-\lambda)>0$ and
$b^2=-\sigma(\sigma-\lambda)>0$ ... Modulo $q$, (eq:twocolumn) gives $(ap_1)(ap_1)^T=(bp_2)(bp_2)^T$" (entrywise in
`𝒪`; it holds for any signs). -/
theorem s8_3_mod_q (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) :
    ∀ j k : Fin 16, piO (MvPolynomial.C (ev 2 * (ev 2 - ev 1)) * P 0 j * P 0 k) =
      piO (MvPolynomial.C (-(ev 3 * (ev 3 - ev 1))) * P 1 j * P 1 k) :=
  Osserman.Proofs.S83.s8_3_mod_q_proved s8_spectral_identity R M N ev P h

/-- **§8.3, opposite signs** (lines 200-201 of sec_small_roots.tex): "so $ap_1=\pm bp_2$ (compare a nonzero component,
then every cross entry)" (one sign for all components). -/
theorem s8_3_pm (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1))
    (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ j, piO (MvPolynomial.C a * P 0 j) = piO (MvPolynomial.C (ε * b) * P 1 j) :=
  Osserman.Proofs.S83.s8_3_pm_proved s8_q_prime s8_spectral_identity R M N ev P h a b ha hb ha2 hb2

/-- **§8.3, opposite signs** (lines 201-202 of sec_small_roots.tex): "If both vanish, the linear-field argument above
applies" ((hidden) one vanishes iff the other does, since `ap₁ = ±bp₂`). -/
theorem s8_3_both_vanish (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (ha : 0 < ev 2 * (ev 2 - ev 1))
    (hb : ev 3 * (ev 3 - ev 1) < 0) (h0 : ∀ j, piO (P 0 j) = 0) :
    (∀ j, piO (P 1 j) = 0) ∧ R.IsClifford :=
  Osserman.Proofs.S83.s8_3_both_vanish_proved s8_q_prime lem_8_2_div_q s8_spectral_identity
    s8_move_eigenfield R M N ev P h ha hb h0

/-- **§8.3, opposite signs** (lines 202-206 of sec_small_roots.tex): "Otherwise, after changing the sign of $P_2$,
$aP_1-bP_2=\sqrt{a^2+b^2}\,qJx$ with $J$ orthogonal and skew" (here `ε` is the sign; the row also holds when both
vanish). -/
theorem s8_3_combination (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1)) (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hpm : ∀ j, piO (MvPolynomial.C a * P 0 j) = piO (MvPolynomial.C (ε * b) * P 1 j)) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧ ∀ x : Vec 16,
      a • evalField (P 0) x - (ε * b) • evalField (P 1) x = (Real.sqrt (a ^ 2 + b ^ 2) * (x ⬝ᵥ x)) • (J *ᵥ x) :=
  Osserman.Proofs.S83.s8_3_combination_proved R M N ev P h a b ha hb ha2 hb2 ε hε hpm

/-- **§8.3, opposite signs** (lines 207-208 of sec_small_roots.tex): "Put $C=\mu+\sigma-\lambda$; it is nonzero since
$a^2+b^2=(\mu-\sigma)C$." -/
theorem s8_3_C_ne_zero (lam mu sig a b : ℝ) (hms : mu ≠ sig) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = mu * (mu - lam)) (hb2 : b ^ 2 = -(sig * (sig - lam))) :
    a ^ 2 + b ^ 2 = (mu - sig) * (mu + sig - lam) ∧ mu + sig - lam ≠ 0 :=
  Osserman.Proofs.S83.s8_3_C_ne_zero_proved lam mu sig a b hms ha hb ha2 hb2

/-- **§8.3, opposite signs** (lines 208-212 of sec_small_roots.tex): "subtracting $C(Jx)(Jx)^T$ turns the
two-dimensional block into a fixed symmetric matrix of trace $\lambda$ and determinant
$\mu\sigma-C(\sigma a^2+\mu b^2)/(a^2+b^2)=0$, since $\sigma a^2+\mu b^2=\mu\sigma(\mu-\sigma)$" — the algebra (the
block is `diag(μ, σ) - C/(a²+b²)·(a,-b)(a,-b)ᵀ`, the frame is row `s8_3_block_frame`). -/
theorem s8_3_block_algebra (lam mu sig a b : ℝ) (hms : mu ≠ sig) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = mu * (mu - lam)) (hb2 : b ^ 2 = -(sig * (sig - lam))) :
    let Cc := mu + sig - lam
    let B2 : Matrix (Fin 2) (Fin 2) ℝ := !![mu, 0; 0, sig] - (Cc / (a ^ 2 + b ^ 2)) • vecMulVec ![a, -b] ![a, -b]
    B2ᵀ = B2 ∧ B2.trace = lam ∧ B2.det = mu * sig - Cc * (sig * a ^ 2 + mu * b ^ 2) / (a ^ 2 + b ^ 2) ∧
      sig * a ^ 2 + mu * b ^ 2 = mu * sig * (mu - sig) ∧ B2.det = 0 :=
  Osserman.Proofs.S83.s8_3_block_algebra_proved lam mu sig a b hms ha hb ha2 hb2

/-- **§8.3, opposite signs** (lines 208-210 and 213-215 of sec_small_roots.tex): "On the unit sphere, subtracting
$C(Jx)(Jx)^T$ turns the two-dimensional block into a fixed symmetric matrix ... the changed block is a constant matrix in
the frame $(P_1,P_2)$" (frame `(P 0, εP 1)`; the matrix of row `s8_3_block_algebra`). -/
theorem s8_3_block_frame (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1)) (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : ∀ x : Vec 16, a • evalField (P 0) x - (ε * b) • evalField (P 1) x =
      (Real.sqrt (a ^ 2 + b ^ 2) * (x ⬝ᵥ x)) • (J *ᵥ x))
    (R' : CurvTensor 16) (hR' : ∀ u v z, R'.op u v z = R.op u v z - (ev 2 + ev 3 - ev 1) • RJfun J u v z) :
    let B2 : Matrix (Fin 2) (Fin 2) ℝ :=
      !![ev 2, 0; 0, ev 3] - ((ev 2 + ev 3 - ev 1) / (a ^ 2 + b ^ 2)) • vecMulVec ![a, -b] ![a, -b]
    ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      R'.jacobi x *ᵥ evalField (P 0) x = B2 0 0 • evalField (P 0) x + B2 1 0 • (ε • evalField (P 1) x) ∧
      R'.jacobi x *ᵥ (ε • evalField (P 1) x) = B2 0 1 • evalField (P 0) x + B2 1 1 • (ε • evalField (P 1) x) :=
  Osserman.Proofs.S83.s8_3_block_frame_proved R M N ev P h a b ha hb ha2 hb2 ε hε J hJs hJo hJ R' hR'

/-- **§8.3, opposite signs** (lines 212-215 of sec_small_roots.tex): "The new eigenvalues are $0,\lambda$, so the pattern
is $(M+1,N+1)$, and the projection lengths of $Jx$ onto the new eigenspaces are constant". -/
theorem s8_3_endpoint (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1))
    (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (J : Matrix (Fin 16) (Fin 16) ℝ)
    (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : ∀ x : Vec 16, a • evalField (P 0) x - (ε * b) • evalField (P 1) x =
      (Real.sqrt (a ^ 2 + b ^ 2) * (x ⬝ᵥ x)) • (J *ᵥ x)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - (ev 2 + ev 3 - ev 1) • RJfun J u v z) ∧
      PatternEv R' ![M + 1, N + 1] ![0, ev 1] ∧
      ∀ ℓ ∈ ({0, ev 1} : Set ℝ), ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) ℓ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c :=
  Osserman.Proofs.S83.s8_3_endpoint_proved R M N ev P h a b ha hb ha2 hb2 ε hε J hJs hJo hJ

/-- **§8.3, opposite signs** (lines 215-217 of sec_small_roots.tex): "Lemma~\ref{lem:constantprojection} excludes a
Cayley endpoint (for $(M,N)=(8,5)$ the endpoint $(9,6)$ is Clifford by [Nik2006, Proposition~2.1]). So the endpoint is
Clifford" (`(8,7)`: `thm_C` and `s8_cayley_excluded`; `(9,6)`: `s8_prop21_uses`). -/
theorem s8_3_endpoint_opp (M N : ℕ) (hMN : (M = 7 ∧ N = 6) ∨ (M = 8 ∧ N = 5)) (R' : CurvTensor 16) (lam : ℝ)
    (hpat : PatternEv R' ![M + 1, N + 1] ![0, lam]) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J)
    (hJo : Jᵀ * J = 1)
    (hproj : ∀ ℓ ∈ ({0, lam} : Set ℝ), ∃ c : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      ∃ w, IsOrthProj (Module.End.eigenspace (R'.jacobiMap x) ℓ ⊓ perp x) (J *ᵥ x) w ∧ w ⬝ᵥ w = c) :
    R'.IsClifford :=
  Osserman.Proofs.S83.s8_3_endpoint_opp_proved M N hMN R' lam hpat J hJs hJo hproj

/-- **§8.3, opposite signs** (lines 217-219 of sec_small_roots.tex): "and [Nik2006, Lemma~3.2(1)], with
Remark~\ref{rem:lemma32-cl8} at an endpoint of type (eq:Cl8), restores the original tensor" (`lem_nik_3_2_1`). -/
theorem s8_3_opposite (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (ha : 0 < ev 2 * (ev 2 - ev 1)) (hb : ev 3 * (ev 3 - ev 1) < 0) :
    R.IsClifford :=
  Osserman.Proofs.S83.s8_3_opposite_proved s8_q_prime s8_spectral_identity R M N ev P h ha hb

/-- **§8.3, opposite signs, non-vacuity** (Lean-only row, review a3 SHOULD-1): the hypotheses of `s8_3_opposite` can
hold (e.g. a Clifford tensor of pattern `(7,6,1,1)` with eigenvalues `0, λ = 2, μ = 3, σ = 1`: `μ(μ - λ) = 3 > 0`,
`σ(σ - λ) = -1 < 0`, and fields `P_i(x) = qJ_ix`). -/
theorem s8_3_opposite_nonvacuous :
    ∃ (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ),
      Sec83Data R M N ev P ∧ 0 < ev 2 * (ev 2 - ev 1) ∧ ev 3 * (ev 3 - ev 1) < 0 :=
  Osserman.Proofs.S8Opp.s8_3_opposite_nonvacuous_proved

/-- **§8.3, conclusion** (lines 171-219 of sec_small_roots.tex): the shifted tensor with the data of §8.3 is Clifford
(same signs: `s8_3_linear_case`; opposite signs: `s8_3_opposite`, after interchanging `μ, σ` if needed). -/
theorem s8_3_clifford (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) : R.IsClifford :=
  Osserman.Proofs.S83.s8_3_clifford_proved s8_q_prime lem_8_2_div_q s8_spectral_identity
    s8_move_eigenfield R M N ev P h

/-- **§8.3 = Theorem F for `(7,6,1,1)` and `(8,5,1,1)`** (lines 6-11 and 171-219 of sec_small_roots.tex). -/
theorem s8_3_pattern_clifford (R : CurvTensor 16) (h : HasPattern R ![7, 6, 1, 1] ∨ HasPattern R ![8, 5, 1, 1]) :
    R.IsClifford :=
  Osserman.Proofs.S83.s8_3_pattern_clifford_proved s8_q_prime s8_cubic_identities lem_8_2_div_q s8_spectral_identity s8_move_eigenfield R h

/-! ## §8.4: a double and a simple eigenvalue, `(M,N,2,1)`, `(M,N) = (7,5)` or `(8,4)` (lines 221-250) -/

/-- **§8.4** (lines 225-227 of sec_small_roots.tex): "There are cubic normalized fields $P_1,P_2$ for $\mu$ and $P_3$ for
$\sigma$" (a use of `Osserman.Cited.nik2006_lemma_3_1` (2) and (1), `k = 4`, homogenized by `q` if linear). -/
theorem s8_4_fields (R : CurvTensor 16) (M N : ℕ) (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) (ev : Fin 4 → ℝ)
    (hR : PatternEv R ![M, N, 2, 1] ev) (h0 : ev 0 = 0) :
    ∃ P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ, Sec84Data R M N ev P :=
  Osserman.Proofs.S84.s8_4_fields_proved s8_cubic_identities R M N hMN ev hR h0

/-- **§8.4** (lines 227-230 of sec_small_roots.tex): "$\mu(\mu-\lambda)(P_1P_1^T+P_2P_2^T)+\sigma(\sigma-\lambda)P_3P_3^T
=qA(A-\lambda qI)$" (at every `x`). -/
theorem s8_4_identity (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) :
    ∀ x : Vec 16, (ev 2 * (ev 2 - ev 1)) • (vecMulVec (evalField (P 0) x) (evalField (P 0) x) +
          vecMulVec (evalField (P 1) x) (evalField (P 1) x)) +
        (ev 3 * (ev 3 - ev 1)) • vecMulVec (evalField (P 2) x) (evalField (P 2) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) :=
  Osserman.Proofs.S84.s8_4_identity_proved s8_spectral_identity R M N ev P h

/-- **§8.4** (lines 231-232 of sec_small_roots.tex): "For equal coefficient signs all fields are linear after division
by $q$" (every component divisible by `q`). -/
theorem s8_4_same_sign (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) (hs : 0 < (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1))) :
    ∀ i j, sqP 16 ∣ P i j :=
  Osserman.Proofs.S84.s8_4_same_sign_proved s8_spectral_identity R M N ev P h hs

/-- **§8.4** (lines 232-234 of sec_small_roots.tex): "For opposite signs, after multiplying by $-1$ if necessary, the two
double-eigenvalue columns have positive coefficients and the simple column the negative one, and the three-column
reduction applies". -/
theorem s8_4_three_col (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) (hs : (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1)) < 0) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ThreeColHyp R ![ev 2, ev 2, ev 3] P
      (ε • ![ev 2 * (ev 2 - ev 1), ev 2 * (ev 2 - ev 1), ev 3 * (ev 3 - ev 1)]) :=
  Osserman.Proofs.S84.s8_4_three_col_proved s8_spectral_identity R M N ev P h hs

/-- **§8.4, opposite signs, non-vacuity** (Lean-only row, review a3 SHOULD-1): the hypotheses of `s8_4_three_col` can
hold (e.g. a Clifford tensor of pattern `(7,5,2,1)` with `λ = 2`, double `μ = 3`, simple `σ = 1`, and fields
`P_i(x) = qJ_ix`). -/
theorem s8_4_opposite_nonvacuous :
    ∃ (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ),
      Sec84Data R M N ev P ∧ (ev 2 * (ev 2 - ev 1)) * (ev 3 * (ev 3 - ev 1)) < 0 :=
  Osserman.Proofs.S8Opp.s8_4_opposite_nonvacuous_proved

/-- **§8.4** (lines 231-237 of sec_small_roots.tex): "its nonunit case gives a linear simple-eigenvalue field, its unit
case a linear double-eigenvalue field (eq:linearcombination), and a column vanishing modulo $q$ is already a linear
field" (with the equal-sign case: in all cases a skew orthogonal linear eigenfield of `σ` or of `μ`). -/
theorem s8_4_linear_field (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec84Data R M N ev P) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      (IsEigenfield R (ev 3) (linP J) ∨ IsEigenfield R (ev 2) (linP J)) :=
  Osserman.Proofs.S84.s8_4_linear_field_proved lem_8_2_div_q s8_tc_same_eigen s8_tc_outcome
    s8_spectral_identity R M N ev P h

/-- **§8.4** (lines 237-245 of sec_small_roots.tex): "Moving that field into the zero eigenvalue gives the endpoints"
`(M+1, N, 2)` (field from the simple eigenvalue) and `(M+1, N, 1, 1)` (field from the double one): the table
`(7,5,2,1) → (8,5,2), (8,5,1,1)` and `(8,4,2,1) → (9,4,2), (9,4,1,1)`. -/
theorem s8_4_move (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1) :
    (IsEigenfield R (ev 3) (linP J) → ∃ R' : CurvTensor 16,
        (∀ u v z, R'.op u v z = R.op u v z - ev 3 • RJfun J u v z) ∧ PatternEv R' ![M + 1, N, 2] ![0, ev 1, ev 2]) ∧
      (IsEigenfield R (ev 2) (linP J) → ∃ R' : CurvTensor 16,
        (∀ u v z, R'.op u v z = R.op u v z - ev 2 • RJfun J u v z) ∧
          PatternEv R' ![M + 1, N, 1, 1] ![0, ev 1, ev 2, ev 3]) :=
  Osserman.Proofs.S84.s8_4_move_proved s8_move_eigenfield R M N ev P h J hJs hJo

/-- **§8.4** (lines 246-247 of sec_small_roots.tex): the endpoints "are Clifford by Theorem~\ref{thm:D} [`(8,5,2)`],
Subsection~\ref{subsec:twosimple} [`(8,5,1,1)`] or [Nik2006, Proposition~2.1, p.~382] [`(9,4,2)`, `(9,4,1,1)`]". -/
theorem s8_4_endpoints_clifford (R' : CurvTensor 16)
    (hpat : HasPattern R' ![8, 5, 2] ∨ HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 2] ∨
      HasPattern R' ![9, 4, 1, 1]) :
    R'.IsClifford :=
  Osserman.Proofs.S84.s8_4_endpoints_clifford_proved s8_q_prime s8_cubic_identities lem_8_2_div_q s8_spectral_identity s8_move_eigenfield R' hpat

/-- **§8.4** (lines 247-250 of sec_small_roots.tex): "Restore the rank-one term by [Nik2006, Lemma~3.2(1)]; no endpoint in
the table has an eigenvalue of multiplicity seven, so their Clifford structures have $\nu\le7$ and
Remark~\ref{rem:lemma32-cl8} is not needed" (the bookkeeping claim, for structures with every `η_i ≠ 0`; the restore
step itself is `lem_nik_3_2_1`). -/
theorem s8_4_endpoints_nu (R' : CurvTensor 16)
    (hpat : HasPattern R' ![8, 5, 2] ∨ HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 2] ∨
      HasPattern R' ![9, 4, 1, 1])
    {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hη : ∀ α, η α ≠ 0) (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν ≤ 7 :=
  Osserman.Proofs.S84.s8_4_endpoints_nu_proved R' hpat Jα hJ l0 η hη hjac

/-- **§8.4, conclusion** (lines 221-250 of sec_small_roots.tex): the shifted tensor with the data of §8.4 is
Clifford. -/
theorem s8_4_clifford (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec84Data R M N ev P) : R.IsClifford :=
  Osserman.Proofs.S84.s8_4_clifford_proved s8_q_prime s8_cubic_identities lem_8_2_div_q s8_tc_same_eigen s8_tc_outcome s8_spectral_identity
    s8_move_eigenfield R M N ev P h

/-- **§8.4 = Theorem F for `(7,5,2,1)` and `(8,4,2,1)`** (lines 6-11 and 221-250 of sec_small_roots.tex). -/
theorem s8_4_pattern_clifford (R : CurvTensor 16) (h : HasPattern R ![7, 5, 2, 1] ∨ HasPattern R ![8, 4, 2, 1]) :
    R.IsClifford :=
  Osserman.Proofs.S84.s8_4_pattern_clifford_proved s8_q_prime s8_cubic_identities lem_8_2_div_q s8_tc_same_eigen s8_tc_outcome s8_spectral_identity
    s8_move_eigenfield R h

/-! ## §8.5: three simple eigenvalues, `(M,N,1,1,1)`, `(M,N) = (7,5)` or `(8,4)` (lines 252-294) -/

/-- **§8.5** (lines 254-256 of sec_small_roots.tex): "After shifting $M$ to zero there are five reduced eigenvalues, so
[Nik2006, Lemma~3.1] gives fields of odd degree at most three" (`k = 5`; homogenized to cubic fields satisfying (8.1),
`s8_cubic_identities`). -/
theorem s8_5_fields (R : CurvTensor 16) (M N : ℕ) (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4)) (ev : Fin 5 → ℝ)
    (hR : PatternEv R ![M, N, 1, 1, 1] ev) (h0 : ev 0 = 0) :
    ∃ P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ, Sec85Data R M N ev P :=
  Osserman.Proofs.S85.s8_5_fields_proved s8_cubic_identities R M N hMN ev hR h0

/-- **§8.5** (lines 256-258 of sec_small_roots.tex): "the cubic spectral identity has weights $w_i=\mu_i(\mu_i-\lambda)$"
(`μ_i = ev 2, ev 3, ev 4`, `λ = ev 1`; at every `x`). -/
theorem s8_5_identity (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec85Data R M N ev P) :
    let mus : Fin 3 → ℝ := ![ev 2, ev 3, ev 4]
    ∀ x : Vec 16, ∑ i, (mus i * (mus i - ev 1)) • vecMulVec (evalField (P i) x) (evalField (P i) x) =
      (x ⬝ᵥ x) • (R.jacobi x * (R.jacobi x - (ev 1 * (x ⬝ᵥ x)) • (1 : Matrix (Fin 16) (Fin 16) ℝ))) :=
  Osserman.Proofs.S85.s8_5_identity_proved s8_spectral_identity R M N ev P h

/-- **§8.5** (lines 258-260 of sec_small_roots.tex): "If all signs agree, every field is linear after division by
$q$". -/
theorem s8_5_same_sign (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec85Data R M N ev P) :
    let mus : Fin 3 → ℝ := ![ev 2, ev 3, ev 4]
    ((∀ i, 0 < mus i * (mus i - ev 1)) ∨ ∀ i, mus i * (mus i - ev 1) < 0) → ∀ i j, sqP 16 ∣ P i j :=
  Osserman.Proofs.S85.s8_5_same_sign_proved s8_spectral_identity R M N ev P h

/-- **§8.5** (lines 260-262 of sec_small_roots.tex): "Otherwise choose the sign and order so that two weights are
positive and the third, a simple column, is negative; the three-column reduction applies". -/
theorem s8_5_three_col (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec85Data R M N ev P) :
    let mus : Fin 3 → ℝ := ![ev 2, ev 3, ev 4]
    ¬ ((∀ i, 0 < mus i * (mus i - ev 1)) ∨ ∀ i, mus i * (mus i - ev 1) < 0) →
      ∃ (sg : Equiv.Perm (Fin 3)) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
        ThreeColHyp R (fun i => mus (sg i)) (fun i => P (sg i)) (fun i => ε * (mus (sg i) * (mus (sg i) - ev 1))) :=
  Osserman.Proofs.S85.s8_5_three_col_proved s8_spectral_identity R M N ev P h

/-- **§8.5, mixed signs, non-vacuity** (Lean-only row, review a3 SHOULD-1): the hypotheses of `s8_5_three_col` can
hold (e.g. a Clifford tensor of pattern `(7,5,1,1,1)` with `λ = 2` and simple eigenvalues `3, 4, 1`, and fields
`P_i(x) = qJ_ix`). -/
theorem s8_5_mixed_nonvacuous :
    ∃ (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ),
      Sec85Data R M N ev P ∧
        ¬ ((∀ i, 0 < (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1)) ∨
          ∀ i, (![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i * ((![ev 2, ev 3, ev 4] : Fin 3 → ℝ) i - ev 1) < 0) :=
  Osserman.Proofs.S8Example.s8_5_mixed_nonvacuous_proved

/-- **§8.5** (lines 264-265 of sec_small_roots.tex): "If we have a linear eigenfield, moving it into the zero eigenvalue
gives $(8,5,1,1)$ or $(9,4,1,1)$, Clifford by Subsection~\ref{subsec:twosimple} and [Nik2006, Proposition~2.1]". -/
theorem s8_5_linear_endpoint (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) (i : Fin 3)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : IsEigenfield R (![ev 2, ev 3, ev 4] i) (linP J)) :
    ∃ R' : CurvTensor 16, (∀ u v z, R'.op u v z = R.op u v z - ![ev 2, ev 3, ev 4] i • RJfun J u v z) ∧
      HasPattern R' ![M + 1, N, 1, 1] ∧ (HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![9, 4, 1, 1]) ∧
      R'.IsClifford :=
  Osserman.Proofs.S85.s8_5_linear_endpoint_proved s8_move_eigenfield s8_3_pattern_clifford
    R M N ev P h i J hJs hJo hJ

/-- **§8.5** (lines 264-267 of sec_small_roots.tex): "...; restore by [Nik2006, Lemma~3.2(1)]" (`lem_nik_3_2_1`): a
linear skew orthogonal eigenfield of one of the simple eigenvalues makes `R` Clifford. -/
theorem s8_5_linear_case (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ)
    (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec85Data R M N ev P) (i : Fin 3)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : IsEigenfield R (![ev 2, ev 3, ev 4] i) (linP J)) : R.IsClifford :=
  Osserman.Proofs.S85.s8_5_linear_case_proved s8_move_eigenfield s8_3_pattern_clifford
    R M N ev P h i J hJs hJo hJ

/-- **§8.5** (lines 268-271 of sec_small_roots.tex): "Put $d=\mu_1c_2^2+\mu_2c_1^2$. After subtracting $C(Jx)(Jx)^T$
the characteristic equation of the block is $(\mu_1-z)(\mu_2-z)-C(d-z)=0$" (the block in the frame `(P_1, P_2)` is
`diag(μ_1, μ_2) - C(c_1,c_2)(c_1,c_2)ᵀ`, since `Jx = c_1P_1 + c_2P_2` at unit `x`). -/
theorem s8_5_char_eq (mu1 mu2 c1 c2 Cc z : ℝ) (hc : c1 ^ 2 + c2 ^ 2 = 1) :
    (!![mu1, 0; 0, mu2] - Cc • vecMulVec ![c1, c2] ![c1, c2] - z • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (mu1 - z) * (mu2 - z) - Cc * ((mu1 * c2 ^ 2 + mu2 * c1 ^ 2) - z) :=
  Osserman.Proofs.S85.s8_5_char_eq_proved mu1 mu2 c1 c2 Cc z hc

/-- **§8.5** (lines 271-273 of sec_small_roots.tex): "Choose $z\in\{0,\lambda\}$ with $d\ne z$ (possible since
$\lambda\ne0$) and $C=(\mu_1-z)(\mu_2-z)/(d-z)$, which is nonzero" (`μ_1, μ_2 ∉ {0, λ}`). -/
theorem s8_5_choose_z (lam mu1 mu2 d : ℝ) (hlam : lam ≠ 0) (h1 : mu1 ≠ 0 ∧ mu1 ≠ lam) (h2 : mu2 ≠ 0 ∧ mu2 ≠ lam) :
    ∃ z : ℝ, (z = 0 ∨ z = lam) ∧ d ≠ z ∧ (mu1 - z) * (mu2 - z) / (d - z) ≠ 0 :=
  Osserman.Proofs.S85.s8_5_choose_z_proved lam mu1 mu2 d hlam h1 h2

/-- **§8.5** (line 273 of sec_small_roots.tex): "The other eigenvalue is $\theta=\mu_1+\mu_2-C-z$" (the characteristic
polynomial is `(t - z)(t - θ)`). -/
theorem s8_5_theta (mu1 mu2 d z : ℝ) (hdz : d ≠ z) :
    let Cc := (mu1 - z) * (mu2 - z) / (d - z)
    let θ := mu1 + mu2 - Cc - z
    ∀ t : ℝ, (mu1 - t) * (mu2 - t) - Cc * (d - t) = (t - z) * (t - θ) :=
  Osserman.Proofs.S85.s8_5_theta_proved mu1 mu2 d z hdz

/-- **§8.5** (lines 267-275 of sec_small_roots.tex): "Otherwise (eq:linearcombination) mixes $\mu_1,\mu_2$ ... and
$0,\lambda,\mu_3$ survive unchanged and distinct, so there is no two-eigenvalue endpoint": the endpoint `R - CR_J` is
Osserman with multiplicity `M` at `0`, `N` at `λ`, `1` at `μ_3`, plus one at `z` and one at `θ` (coincidences
included). Mixed pair `(ev 2, ev 3)` with fields `P 0, P 1`, survivor `μ_3 = ev 4` (any other choice is a relabelling of
the simple eigenvalues). -/
theorem s8_5_endpoint_mult (R : CurvTensor 16) (M N : ℕ) (hMN : (M = 7 ∧ N = 5) ∨ (M = 8 ∧ N = 4))
    (ev : Fin 5 → ℝ) (hR : PatternEv R ![M, N, 1, 1, 1] ev) (h0 : ev 0 = 0)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hP : ∀ (i : Fin 2) (x : Vec 16), evalField (P i) x ⬝ᵥ evalField (P i) x = (x ⬝ᵥ x) ^ 3)
    (hPe : IsEigenfield R (ev 2) (P 0) ∧ IsEigenfield R (ev 3) (P 1)) (c1 c2 : ℝ) (hc : c1 ^ 2 + c2 ^ 2 = 1)
    (J : Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x))
    (z : ℝ) (hz : z = 0 ∨ z = ev 1) (hdz : ev 2 * c2 ^ 2 + ev 3 * c1 ^ 2 ≠ z) :
    let d := ev 2 * c2 ^ 2 + ev 3 * c1 ^ 2
    let Cc := (ev 2 - z) * (ev 3 - z) / (d - z)
    let θ := ev 2 + ev 3 - Cc - z
    ∃ R' : CurvTensor 16, (∀ u v w, R'.op u v w = R.op u v w - Cc • RJfun J u v w) ∧ R'.IsOsserman ∧
      (0 ≠ ev 1 ∧ 0 ≠ ev 4 ∧ ev 1 ≠ ev 4) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ ν : ℝ, R'.redMult x ν =
        (if ν = 0 then M else 0) + (if ν = ev 1 then N else 0) + (if ν = ev 4 then 1 else 0) +
          (if ν = z then 1 else 0) + (if ν = θ then 1 else 0) :=
  Osserman.Proofs.S85.s8_5_endpoint_mult_proved s8_move_frame R M N hMN ev hR h0 P hP hPe c1 c2 hc
    J hJ z hz hdz

/-- **§8.5** (lines 275-287 of sec_small_roots.tex): "The complete list of endpoints, including coincidences, is as
follows, where \emph{other large} means $\theta=\lambda$ if $z=0$ and $\theta=0$ if $z=\lambda$" — the table, row by
row, in the order "θ new, θ = μ_3, θ other large, θ = z". Stated CELL BY CELL (review a3 MUST-3): each cell is
the implication "this value of θ gives this pattern" ("θ new" = `θ ∉ {0, λ, μ_3}`; `z ∈ {0, λ}`). -/
theorem s8_5_endpoint_table (R' : CurvTensor 16) (M N : ℕ) (lam mu3 z θ : ℝ)
    (hdist : 0 ≠ lam ∧ 0 ≠ mu3 ∧ lam ≠ mu3) (hz : z = 0 ∨ z = lam)
    (hmult : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ ν : ℝ, R'.redMult x ν =
      (if ν = 0 then M else 0) + (if ν = lam then N else 0) + (if ν = mu3 then 1 else 0) +
        (if ν = z then 1 else 0) + (if ν = θ then 1 else 0)) :
    (M = 7 ∧ N = 5 ∧ z = 0 →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![8, 5, 1, 1]) ∧ (θ = mu3 → HasPattern R' ![8, 5, 2]) ∧
          (θ = lam → HasPattern R' ![8, 6, 1]) ∧ (θ = 0 → HasPattern R' ![9, 5, 1])) ∧
      (M = 7 ∧ N = 5 ∧ z = lam →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![7, 6, 1, 1]) ∧ (θ = mu3 → HasPattern R' ![7, 6, 2]) ∧
          (θ = 0 → HasPattern R' ![8, 6, 1]) ∧ (θ = lam → HasPattern R' ![7, 7, 1])) ∧
      (M = 8 ∧ N = 4 ∧ z = 0 →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![9, 4, 1, 1]) ∧ (θ = mu3 → HasPattern R' ![9, 4, 2]) ∧
          (θ = lam → HasPattern R' ![9, 5, 1]) ∧ (θ = 0 → HasPattern R' ![10, 4, 1])) ∧
      (M = 8 ∧ N = 4 ∧ z = lam →
        (θ ≠ 0 → θ ≠ lam → θ ≠ mu3 → HasPattern R' ![8, 5, 1, 1]) ∧ (θ = mu3 → HasPattern R' ![8, 5, 2]) ∧
          (θ = 0 → HasPattern R' ![9, 5, 1]) ∧ (θ = lam → HasPattern R' ![8, 6, 1])) :=
  Osserman.Proofs.S85.s8_5_endpoint_table_proved R' M N lam mu3 z θ hdist hz hmult

/-- **§8.5** (lines 288-291 of sec_small_roots.tex): "Each is Clifford by the preceding subsections,
Theorem~\ref{thm:D}, [Nik2006, Proposition~2.1] (an eigenvalue of multiplicity $9$), or [Nik2005, Proposition~1] for
$(10,4,1)$" — the ten distinct endpoints of the table. -/
theorem s8_5_endpoint_clifford (R' : CurvTensor 16)
    (hpat : HasPattern R' ![8, 5, 1, 1] ∨ HasPattern R' ![7, 6, 1, 1] ∨ HasPattern R' ![9, 4, 1, 1] ∨
      HasPattern R' ![8, 5, 2] ∨ HasPattern R' ![7, 6, 2] ∨ HasPattern R' ![9, 4, 2] ∨ HasPattern R' ![8, 6, 1] ∨
      HasPattern R' ![9, 5, 1] ∨ HasPattern R' ![7, 7, 1] ∨ HasPattern R' ![10, 4, 1]) :
    R'.IsClifford :=
  Osserman.Proofs.S85.s8_5_endpoint_clifford_proved s8_3_pattern_clifford R' hpat

/-- **§8.5** (lines 290-291 of sec_small_roots.tex): "in the notation of [Nik2005, Proposition~1], $m=10$ and $\nu=5$
satisfy $16\ge3\nu$ and $16>(\nu+1)^2/4$" (`ν = 16 - 1 - m`). -/
theorem s8_5_nik2005_arith :
    (16 - 1 - 10 : ℕ) = 5 ∧ (16 : ℝ) ≥ 3 * ((5 : ℕ) : ℝ) ∧ (16 : ℝ) > (((5 : ℕ) : ℝ) + 1) ^ 2 / 4 :=
  Osserman.Proofs.S85.s8_5_nik2005_arith_proved

/-- **§8.5** (lines 289-291 of sec_small_roots.tex): "or [Nik2005, Proposition~1] for $(10,4,1)$" (from
`Osserman.Cited.nik2005_prop_1` with `m = 10`, `ν = 5`). -/
theorem s8_5_10_4_1 (R' : CurvTensor 16) (hpat : HasPattern R' ![10, 4, 1]) : R'.IsClifford :=
  Osserman.Proofs.S85.s8_5_10_4_1_proved R' hpat

/-- **§8.5** (lines 291-294 of sec_small_roots.tex): "Each update has constant eigenvalues, so [Nik2006, Lemma~3.2(1)],
in the form of Remark~\ref{rem:lemma32-cl8} at the endpoint $(7,7,1)$, restores the original tensor" — the bookkeeping
claim behind the sentence: at `(7,7,1)` every Clifford structure (all `η_i ≠ 0`) has `ν = 8`. The row also states
`ν = 8` at `(7,6,1,1)` and `(7,6,2)` (true). There the paper rightly needs no Remark 7.2: the base eigenvalue
(multiplicity 7) is the unique largest, so [Nik2006, Lemma 3.2(1)] applies as stated; Remark 7.2 is needed only
where `ν = 8` and a second eigenvalue also has multiplicity at least 7, i.e. at `(7,7,1)` (review a3 NIT-2). -/
theorem s8_5_cl8_endpoints (R' : CurvTensor 16)
    (hpat : HasPattern R' ![7, 7, 1] ∨ HasPattern R' ![7, 6, 1, 1] ∨ HasPattern R' ![7, 6, 2])
    {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) (l0 : ℝ) (η : Fin ν → ℝ)
    (hη : ∀ α, η α ≠ 0) (hjac : ∀ x, R'.jacobi x = l0 • Pi x + ∑ α, η α • jfam (Jα α) x) : ν = 8 :=
  Osserman.Proofs.S85.s8_5_cl8_endpoints_proved R' hpat Jα hJ l0 η hη hjac

/-- **§8.5, conclusion** (lines 252-294 of sec_small_roots.tex): the shifted tensor with the data of §8.5 is Clifford
(restoring with `lem_nik_3_2_1`). -/
theorem s8_5_clifford (R : CurvTensor 16) (M N : ℕ) (ev : Fin 5 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec85Data R M N ev P) : R.IsClifford :=
  Osserman.Proofs.S85.s8_5_clifford_proved s8_spectral_identity lem_8_2_div_q s8_tc_outcome
    s8_move_eigenfield s8_3_pattern_clifford s8_move_frame R M N ev P h

/-- **§8.5 = Theorem F for `(7,5,1,1,1)` and `(8,4,1,1,1)`** (lines 6-11 and 252-294 of sec_small_roots.tex). -/
theorem s8_5_pattern_clifford (R : CurvTensor 16)
    (h : HasPattern R ![7, 5, 1, 1, 1] ∨ HasPattern R ![8, 4, 1, 1, 1]) : R.IsClifford :=
  Osserman.Proofs.S85.s8_5_pattern_clifford_proved s8_cubic_identities s8_spectral_identity
    lem_8_2_div_q s8_tc_outcome s8_move_eigenfield s8_3_pattern_clifford s8_move_frame R h

/-! ## §8.6: the remaining patterns, multiplicities at most two (lines 296-315): Nik2006 Lemma 3.3 with up to eight
columns (ADAPTED, flag F4) -/

/-- **§8.6** (lines 298-299 of sec_small_roots.tex): "Shift the eigenvalue of multiplicity $M\in\{7,8\}$ to zero". -/
theorem s8_6_shift (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ) (h : SmallMultHyp R μ0 M) :
    ∃ R0 : CurvTensor 16, (∀ u v z, R0.op u v z = R.op u v z - μ0 • R1fun u v z) ∧ SmallMultHyp R0 0 M ∧
      (R0.IsClifford ↔ R.IsClifford) :=
  Osserman.Proofs.S86.s8_6_shift_proved R μ0 M h

/-- **§8.6** (lines 298-301 of sec_small_roots.tex): "let $r=15-M\le8$. By [Nik2006, Lemma~3.1, p.~383], which applies
because every nonzero eigenvalue has multiplicity one or two, there are $r$ orthogonal normalized fields for the nonzero
eigenvalues" (eigenvalues `Λ_j ≠ 0` counted with multiplicity; odd degrees `dg j`; orthonormal on the unit sphere). -/
theorem s8_6_fields (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) :
    15 - M ≤ 8 ∧ ∃ (Λ : Fin (15 - M) → ℝ) (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ)
      (dg : Fin (15 - M) → ℕ), (∀ j, Odd (dg j)) ∧ (∀ j a, (P j a).IsHomogeneous (dg j)) ∧ (∀ j, Λ j ≠ 0) ∧
      (∀ j, IsEigenfield R (Λ j) (P j)) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then 1 else 0 :=
  Osserman.Proofs.S86.s8_6_fields_proved R M h

/-- **§8.6** (lines 301-304 of sec_small_roots.tex): "Divide each by the largest possible power of $q$ and homogenize all
to the largest remaining odd degree $d$; then a component of a field of maximal degree is not divisible by $q$". -/
theorem s8_6_normalize (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (dg : Fin (15 - M) → ℕ) (hodd : ∀ j, Odd (dg j))
    (hhom : ∀ j a, (P j a).IsHomogeneous (dg j)) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then 1 else 0) :
    ∃ (d : ℕ) (P' : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ), Odd d ∧
      (∀ j a, (P' j a).IsHomogeneous d) ∧ (∀ j, IsEigenfield R (Λ j) (P' j)) ∧
      (∀ (x : Vec 16) j l, evalField (P' j) x ⬝ᵥ evalField (P' l) x = if j = l then (x ⬝ᵥ x) ^ d else 0) ∧
      ∃ j a, ¬ sqP 16 ∣ P' j a :=
  Osserman.Proofs.S86.s8_6_normalize_proved R M h Λ P dg hodd hhom hΛ hPe hPo

/-- **§8.6** (lines 304-308 of sec_small_roots.tex): "With $P$ the $16\times r$ matrix of fields and $\Lambda$ the
diagonal matrix of their eigenvalues, $P^TP=q^dI$, $P\Lambda P^T=q^{d-1}A$, $P\Lambda^2P^T=q^{d-2}A^2$" (at every `x`;
`A(x) = J_x`; the third multiplied by `q`, since `d - 2 < 0` when `d = 1`). -/
theorem s8_6_identities (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hd : Odd d)
    (hhom : ∀ j a, (P j a).IsHomogeneous d) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0) :
    ∀ x : Vec 16, (fieldMat P x)ᵀ * fieldMat P x = (x ⬝ᵥ x) ^ d • (1 : Matrix (Fin (15 - M)) (Fin (15 - M)) ℝ) ∧
      fieldMat P x * diagonal Λ * (fieldMat P x)ᵀ = (x ⬝ᵥ x) ^ (d - 1) • R.jacobi x ∧
      (x ⬝ᵥ x) • (fieldMat P x * diagonal (fun j => Λ j ^ 2) * (fieldMat P x)ᵀ) =
        (x ⬝ᵥ x) ^ (d - 1) • (R.jacobi x * R.jacobi x) :=
  Osserman.Proofs.S86.s8_6_identities_proved R M h Λ P d hd hhom hΛ hPe hPo

/-- **§8.6** (lines 309-310 of sec_small_roots.tex): "If $d\ge3$, each diagonal entry of $P\Lambda^2P^T$ is a sum of
$r\le8$ squares divisible by $q$" (as polynomials). -/
theorem s8_6_diag (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hd : Odd d) (hd3 : 3 ≤ d)
    (hhom : ∀ j a, (P j a).IsHomogeneous d) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0) :
    15 - M ≤ 8 ∧ ∀ a : Fin 16, sqP 16 ∣ ∑ j, (MvPolynomial.C (Λ j) * P j a) ^ 2 :=
  Osserman.Proofs.S86.s8_6_diag_proved R M h Λ P d hd hd3 hhom hΛ hPe hPo

/-- **§8.6** (lines 310-311 of sec_small_roots.tex): "and [Nik2006, Lemma~3.11] makes every field component divisible by
$q$, a contradiction. So $d=1$" (`Osserman.Cited.nik2006_lemma_3_11`). -/
theorem s8_6_d_one (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ) (hd : Odd d)
    (hhom : ∀ j a, (P j a).IsHomogeneous d) (hΛ : ∀ j, Λ j ≠ 0) (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then (x ⬝ᵥ x) ^ d else 0)
    (hnd : ∃ j a, ¬ sqP 16 ∣ P j a) : d = 1 :=
  Osserman.Proofs.S86.s8_6_d_one_proved R M h Λ P d hd hhom hΛ hPe hPo hnd

/-- **§8.6** (lines 311-313 of sec_small_roots.tex): "the fields are $J_ix$ with orthogonal skew, pairwise anticommuting
$J_i$, and the Jacobi formula is Clifford". -/
theorem s8_6_clifford_form (R : CurvTensor 16) (M : ℕ) (h : SmallMultHyp R 0 M) (Λ : Fin (15 - M) → ℝ)
    (P : Fin (15 - M) → Fin 16 → MvPolynomial (Fin 16) ℝ) (hhom : ∀ j a, (P j a).IsHomogeneous 1) (hΛ : ∀ j, Λ j ≠ 0)
    (hPe : ∀ j, IsEigenfield R (Λ j) (P j))
    (hPo : ∀ (x : Vec 16) j l, evalField (P j) x ⬝ᵥ evalField (P l) x = if j = l then x ⬝ᵥ x else 0) :
    ∃ J : Fin (15 - M) → Matrix (Fin 16) (Fin 16) ℝ, IsCliffordStr J ∧ (∀ j, (J j)ᵀ * J j = 1) ∧
      (∀ j (x : Vec 16), evalField (P j) x = J j *ᵥ x) ∧ (∀ x, R.jacobi x = ∑ j, Λ j • jfam (J j) x) ∧
      R.IsClifford :=
  Osserman.Proofs.S86.s8_6_clifford_form_proved R M h Λ P hhom hΛ hPe hPo

/-- **§8.6 = Theorem F, second part** (lines 12-14 and 296-315 of sec_small_roots.tex): "or if one eigenvalue has
multiplicity seven or eight and every other eigenvalue has multiplicity at most two" — Clifford ((hidden) the shift is
added back, S8.112). "(This is the proof of [Nik2006, Lemma~3.3] with at most eight columns instead of six.)" -/
theorem s8_6_clifford (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ) (h : SmallMultHyp R μ0 M) : R.IsClifford :=
  Osserman.Proofs.S86.s8_6_clifford_proved R μ0 M h

/-! ## Theorem F, the assembly (line 315: "This proves Theorem~\ref{thm:E}") -/

/-- **Theorem F** (thm:E, lines 6-14 of sec_small_roots.tex): "An Osserman algebraic curvature tensor on $\R^{16}$ is
Clifford if its reduced multiplicity pattern is one of $(7,6,1,1),\ (8,5,1,1),\ (7,5,2,1),\ (8,4,2,1),\ (7,5,1,1,1),\
(8,4,1,1,1)$, or if one eigenvalue has multiplicity seven or eight and every other eigenvalue has multiplicity at most
two". The six patterns are `HasPattern` (as in `thm_E`); the last case is `SmallMultHyp`. Also row S8.113, "This proves
Theorem~\ref{thm:E}" (line 315): the assembly of `s8_3_pattern_clifford`, `s8_4_pattern_clifford`,
`s8_5_pattern_clifford`, `s8_6_clifford`. (Placed after §8.6 so that these four rows, its leading premises, are
declared first; its type is unchanged.) -/
theorem thm_F (R : CurvTensor 16) (hO : R.IsOsserman)
    (h : HasPattern R ![7, 6, 1, 1] ∨ HasPattern R ![8, 5, 1, 1] ∨ HasPattern R ![7, 5, 2, 1] ∨
      HasPattern R ![8, 4, 2, 1] ∨ HasPattern R ![7, 5, 1, 1, 1] ∨ HasPattern R ![8, 4, 1, 1, 1] ∨
      ∃ μ0 : ℝ, ∃ M : ℕ, SmallMultHyp R μ0 M) :
    R.IsClifford :=
  Osserman.Proofs.ThmF.thm_F_proved s8_3_pattern_clifford s8_4_pattern_clifford s8_5_pattern_clifford
    s8_6_clifford R hO h

end Osserman.Paper
