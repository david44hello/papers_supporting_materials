/-
Matsaev/Paper/Statements.lean — one theorem per claim of the paper.
Paper: "Matsaev's (1971) conjecture is false for every p != 2", Dave Goel, short version v2.00 (md5 a9b3c6be). Scope:
Theorem A, every lemma and theorem of Sections 2-4 (with Lemma 3.5 (iv)), Theorem B, Corollary 5.1, Remark 5.2.

Numbers in the docstrings are those of the final v2.00 (the same as v0.90), with the paper's `\label` names. The Lean NAMES carry the
v2.00 numbers (`lemma_3_5_angle_form` is Lemma 3.5 (i)-(iii) in the angle form of Matsaev/Angle/Defs.lean); the
internal `Matsaev.*_proved` names keep the first draft's (v0.60) numbers.

How to read the exponent: `p : ℝ≥0∞` with `[Fact (1 ≤ p)]` is the space index (Mathlib's convention for `ℓ^p`);
`p.toReal` is the same number as a real, used in the scalar formulas. `p ≠ ⊤` means `p < ∞`.
Real and complex: the paper's matrices and polynomials are real, and Lemma 2.1 says real and complex norms agree.
Each operator claim is stated over `ℝ`; Lemma 2.1 and Theorem A are also stated over `ℂ`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Matsaev.Defs.Scalar
import Matsaev.Defs.Spaces
import Matsaev.Defs.Conjecture
import Matsaev.Angle.Defs
import Matsaev.Bridge.Basic
import Matsaev.Scalar.N1
import Matsaev.Scalar.B0
import Matsaev.Ops.Bellman
import Matsaev.TK.Teps
import Matsaev.Ops.RC
import Matsaev.Ops.LpBridge
import Matsaev.Assembly.Basic
import Matsaev.Ops.Dual
import Matsaev.Ops.JLower
import Matsaev.TK.Gain
import Matsaev.Angle.Basic
import Matsaev.SJ.Sigma
import Matsaev.SJ.Bellman
import Matsaev.Assembly.LpNat
import Matsaev.Assembly.Rem52
import Matsaev.ThmB.Basic
import Matsaev.Assembly.Lem35iv
import Matsaev.Assembly.P1Inf
import Matsaev.Assembly.Qexp
import Matsaev.Assembly.Values
import Matsaev.Assembly.Gamma
import Matsaev.Assembly.Cov130

namespace Matsaev.Paper

open Matsaev
open scoped ENNReal Matrix
open Polynomial

/-! ## Section 2: three basic facts -/

/-- **Section 2, notation** (before Lemma 2.1): for real `ξ, ψ ∈ ℝ²` and `p > 1`,
`d/dh ‖ξ + hψ‖_p^p |_{h=0} = p⟨φ(ξ), ψ⟩`, with `⟨ξ, ψ⟩ = ξ₁ψ₁ + ξ₂ψ₂` and `φ` acting coordinatewise. -/
theorem notation_dir_deriv (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (ξ ψ : Fin 2 → ℝ) :
    HasDerivAt (fun h : ℝ => ‖WithLp.toLp p (ξ + h • ψ)‖ ^ p.toReal) (p.toReal * ∑ i, phi p.toReal (ξ i) * ψ i) 0 :=
  Matsaev.Gamma.hasDerivAt_norm_dir p (Matsaev.Assembly.one_lt_toReal hp hptop) hptop ξ ψ

/-- **Lemma 2.1** (`lem:RC`), matrices: a real `n × n` matrix has the same norm on the real and on the complex `ℓ^p_n`,
`1 ≤ p < ∞` (Marcinkiewicz–Zygmund; the paper gives the proof). The paper states it for `2 × 2` matrices, the case
`n = Fin 2` of this statement. -/
theorem lemma_2_1_matrix (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : matNorm p (A.map (algebraMap ℝ ℂ)) = matNorm p A :=
  Matsaev.lemma_2_1_matrix_proved p hptop A

/-- **Lemma 2.1** (`lem:RC`), shift operators: for a real polynomial `P`, the operator `P(S)` has the same norm on the
real and on the complex `ℓ^p(ℕ)`, `1 ≤ p < ∞`. -/
theorem lemma_2_1_shift (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (P : ℝ[X]) :
    shiftNorm p ℂ (P.map (algebraMap ℝ ℂ)) = shiftNorm p ℝ P :=
  Matsaev.lemma_2_1_shift_proved p hptop P

/-- **Proof of Lemma 2.1** (`lem:RC`), the scalar identity (added in v1.50): for `z = y₁ + iy₂`,
`∫_0^{2π} |y₁ cos θ + y₂ sin θ|^p dθ = β_p |z|^p` with `β_p = ∫_0^{2π} |cos θ|^p dθ` (every real exponent `q`). It is
step 1 of Lean's proof of Lemma 2.1 (`Matsaev.RC.integral_abs_rpow_eq`). -/
theorem lemma_2_1_scalar_identity (q : ℝ) (z : ℂ) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, |Real.cos θ * z.re + Real.sin θ * z.im| ^ q =
      (∫ θ in (0 : ℝ)..2 * Real.pi, |Real.cos θ| ^ q) * ‖z‖ ^ q :=
  Matsaev.RC.integral_abs_rpow_eq z

/-- **Proof of Lemma 2.2** (`lem:J`), the consistency of `(x_n, x_{n-1}) = J^{-n}ξ` (added in v1.50): with `J^{-1} = -J`, the
second coordinate of `J^{-(n+1)}ξ` is the first coordinate of `J^{-n}ξ`; and `J^{-2} = -I`, so `x_{n+2} = -x_n`. -/
theorem lemma_2_2_consistency {𝕜 : Type} [RCLike 𝕜] (ξ : Fin 2 → 𝕜) (n : ℕ) :
    (((-Jmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ (n + 1)) *ᵥ ξ) 1 = (((-Jmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ n) *ᵥ ξ) 0 ∧
      (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) * -Jmat = 1 ∧ (-Jmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ 2 = -1 := by
  refine ⟨?_, by rw [mul_neg, Jmat_mul_Jmat, neg_neg], by rw [neg_sq, sq, Jmat_mul_Jmat]⟩
  rw [pow_succ', ← Matrix.mulVec_mulVec]
  simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Proof of Lemma 2.2** (`lem:J`), the consistency for every `n ∈ ℤ` (v1.90): "if `J^{-n-1}ξ = (b₁, b₂)` then
`J^{-n}ξ = J(b₁, b₂) = (b₂, -b₁)`": the step `J(b₁, b₂) = (b₂, -b₁)` for every vector, and the second coordinate of
`J^{-(n+1)}ξ` is the first coordinate of `J^{-n}ξ` for every integer `n` (`lemma_2_2_consistency` is the form `n ∈ ℕ` with
`J^{-1} = -J`). Review r6, S1. -/
theorem lemma_2_2_consistency_int {𝕜 : Type} [RCLike 𝕜] :
    (∀ b : Fin 2 → 𝕜, (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ b = ![b 1, -b 0]) ∧
    ∀ (ξ : Fin 2 → 𝕜) (n : ℤ), (((Jmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ (-(n + 1))) *ᵥ ξ) 1 =
      (((Jmat : Matrix (Fin 2) (Fin 2) 𝕜) ^ (-n)) *ᵥ ξ) 0 := by
  have hvec : ∀ b : Fin 2 → 𝕜, (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ b = ![b 1, -b 0] := by
    intro b
    ext i
    fin_cases i <;> simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨hvec, fun ξ n => ?_⟩
  have hdet : IsUnit (Jmat : Matrix (Fin 2) (Fin 2) 𝕜).det := by
    simp [Jmat, Matrix.det_fin_two]
  rw [show -n = 1 + -(n + 1) by ring, Matrix.zpow_add hdet, zpow_one, ← Matrix.mulVec_mulVec, hvec]
  simp

/-- **Lemma 2.2** (`lem:J`), the rotation `J` is a lower bound: `‖P(J)‖_{ℓ^p_2} ≤ ‖P(S)‖_{ℓ^p}` for every polynomial `P`
and `1 ≤ p ≤ ∞` (over `𝕜 = ℝ` or `ℂ`). Used only for the equality in Theorem 3.6, not for Theorem A. -/
theorem lemma_2_2 {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : 𝕜[X]) :
    matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) P) ≤ shiftNorm p 𝕜 P :=
  Matsaev.lemma_2_2_proved p P

/-- **Lemma 2.2** (`lem:J`), the last sentence of its proof: "For `p = ∞` the inequality is trivial:
`‖P(J)‖_∞ ≤ Σ|c_k| = ‖P(S)‖_∞`" (complex `ℓ^∞`; `Σ|c_k| = ∑_{k ≤ deg P} |c_k|`). (Lean's proof of `lemma_2_2` at `p = ∞`
takes another route, periodic truncation; see AUDIT.md.) -/
theorem lemma_2_2_infty (P : ℂ[X]) :
    matNorm ⊤ (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) P) ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ ∧
      ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ = shiftNorm ⊤ ℂ P := by
  rw [Matsaev.P1Inf.shiftNorm_top]
  exact ⟨(lemma_2_2 ⊤ P).trans_eq (Matsaev.P1Inf.shiftNorm_top P), rfl⟩

/-- **Section 1, Background**: "For `p = 1` and `p = ∞`, inequality (1) holds trivially, since then
`‖P(T)‖_p ≤ Σ|c_k| = ‖P(S)‖_p`": for every contraction `T` of every `L^p` space (Mathlib's `MeasureTheory.Lp ℂ p μ`, any
measure space) and every complex polynomial `P` (`Σ|c_k| = ∑_{k ≤ deg P} |c_k|`). -/
theorem background_p_one_infty (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p = 1 ∨ p = ⊤) (P : ℂ[X]) (Ω : Type*)
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (T : MeasureTheory.Lp ℂ p μ →L[ℂ] MeasureTheory.Lp ℂ p μ)
    (hT : ‖T‖ ≤ 1) :
    ‖aeval T P‖ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ ∧
      ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ = shiftNorm p ℂ P := by
  refine ⟨Matsaev.P1Inf.norm_aeval_le_sum T hT P, ?_⟩
  rcases hp with rfl | rfl
  · exact (Matsaev.P1Inf.shiftNorm_one P).symm
  · exact (Matsaev.P1Inf.shiftNorm_top P).symm

/-- **Section 1, Idea of the proof of Theorem A**: for `P_0(z) = 1 - Bz²` (`= Pa 0 B`), `B > 0`,
`‖P_0(J)‖_p = ‖P_0(S)‖_p = 1 + B`, for every `1 ≤ p ≤ ∞` (real spaces). -/
theorem idea_p0_norms (p : ℝ≥0∞) [Fact (1 ≤ p)] (B : ℝ) (hB : 0 < B) :
    matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B)) = 1 + B ∧ shiftNorm p ℝ (Pa 0 B) = 1 + B :=
  Matsaev.Qexp.p0_norms p B hB

/-- **Section 1, the table** (Theorem B row): (1) is known to hold for all contractions "only in the trivial case
`‖P(S)‖_p = Σ|c_k|` (then `‖P(T)‖_p ≤ Σ|c_k|` gives (1))": for every `1 ≤ p ≤ ∞`, every contraction `T` of every `L^p`
space (Mathlib's `MeasureTheory.Lp ℂ p μ`) and every complex polynomial `P`, `‖P(T)‖ ≤ Σ|c_k|`; so when
`‖P(S)‖_p = Σ|c_k|`, (1) holds: `‖P(T)‖ ≤ ‖P(S)‖_p`. -/
theorem table_trivial_case (p : ℝ≥0∞) [Fact (1 ≤ p)] (P : ℂ[X]) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (T : MeasureTheory.Lp ℂ p μ →L[ℂ] MeasureTheory.Lp ℂ p μ) (hT : ‖T‖ ≤ 1) :
    ‖aeval T P‖ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ ∧
      (shiftNorm p ℂ P = ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ → ‖aeval T P‖ ≤ shiftNorm p ℂ P) := by
  have h := Matsaev.P1Inf.norm_aeval_le_sum T hT P
  refine ⟨h, fun hP => ?_⟩
  rw [hP]
  exact h

/-- **Section 1, the table** (Theorem B row): the trivial case `‖P(S)‖_p = Σ|c_k|` holds "for example [for]
`deg P ≤ 1`": `‖c₀ + c₁S‖_p = |c₀| + |c₁|` for all complex `c₀, c₁` and every `1 ≤ p ≤ ∞`. -/
theorem table_deg_one (p : ℝ≥0∞) [Fact (1 ≤ p)] (c₀ c₁ : ℂ) :
    shiftNorm p ℂ (C c₀ + C c₁ * X) = ‖c₀‖ + ‖c₁‖ :=
  Matsaev.Cov130.shiftNorm_deg_one p c₀ c₁

/-- **Section 1, Idea of the proof of Theorem A**: "long truncations `x` of every sequence with `x_{n+2} = -x_n` give
`‖P_0(S)x‖_p/‖x‖_p` close to `1+B`": for `1 ≤ p < ∞`, `B ≥ 0`, every nonzero `x : ℕ → 𝕜` with `x_{n+2} = -x_n` and every
`ε > 0` there is `L₀` such that every truncation `y = (x_0, …, x_{L-1}, 0, 0, …)` with `L ≥ L₀` has
`1 + B - ε < ‖P_0(S)y‖_p/‖y‖_p ≤ 1 + B` (Matsaev/Assembly/Cov130.lean). -/
theorem idea_truncations {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 ≤ B)
    (x : ℕ → 𝕜) (hx : ∀ n, x (n + 2) = -x n) (hx0 : x ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ y : lp (fun _ : ℕ => 𝕜) p, (∀ n, y n = if n < L then x n else 0) →
      1 + B - ε < ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ / ‖y‖ ∧
        ‖aeval (shiftOp p 𝕜) (Pa (0 : 𝕜) (B : 𝕜)) y‖ / ‖y‖ ≤ 1 + B :=
  Matsaev.Cov130.truncations_almost_maximise p hptop hB hx hx0 hε

/-- **Section 1, Idea of the proof of Theorem A**: "If `x_{n+2} = -x_n` for all `n ∈ ℤ` and `(Sx)_n = x_{n-1}`, then
`((Sx)_n, (Sx)_{n-1}) = (x_{n-1}, x_{n-2}) = (x_{n-1}, -x_n) = J(x_n, x_{n-1})`: on such sequences `S` acts as `J`"
(here `(Sx)_m = x_{m-1}` is written `(fun m => x (m - 1))`). -/
theorem idea_S_acts_as_J {𝕜 : Type} [RCLike 𝕜] (x : ℤ → 𝕜) (hx : ∀ n, x (n + 2) = -x n) (n : ℤ) :
    (![(fun m => x (m - 1)) n, (fun m => x (m - 1)) (n - 1)] : Fin 2 → 𝕜) = ![x (n - 1), x (n - 2)] ∧
      (![x (n - 1), x (n - 2)] : Fin 2 → 𝕜) = ![x (n - 1), -x n] ∧
      (![x (n - 1), -x n] : Fin 2 → 𝕜) = (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) *ᵥ ![x n, x (n - 1)] := by
  have h2 : x (n - 2) = -x n := by
    have h := hx (n - 2)
    rw [show n - 2 + 2 = n by ring] at h
    rw [h, neg_neg]
  refine ⟨?_, by rw [h2], ?_⟩
  · simp only [show n - 1 - 1 = n - 2 by ring]
  · ext i
    fin_cases i <;> simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Section 1, Idea of the proof of Theorem A** (v1.90 wording): "dividing by `p‖ξ‖_p^{p-1}`,
`d/dε ‖R_{ε/2}ξ‖_p |_{ε=0} = ½ Q(ξ)‖ξ‖_p`"; "the derivative above is at most `(D_*/2)‖ξ‖_p`" for every real `ξ`, with
equality for some `ξ ≠ 0` (`p > 2`; `Q(ξ)` is `Qf p ξ₁ ξ₂`, and `Qf p 0 0 = 0`); "with equality at `ξ = (1, t_*)`" is
`idea_rotation_growth_eq`. Route: Matsaev/Assembly/Cov130.lean. -/
theorem idea_rotation_growth (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) :
    (∀ ξ : Fin 2 → ℝ, HasDerivAt (fun ε => ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖)
        (1 / 2 * Qf p.toReal (ξ 0) (ξ 1) * ‖WithLp.toLp p ξ‖) 0 ∧
      1 / 2 * Qf p.toReal (ξ 0) (ξ 1) * ‖WithLp.toLp p ξ‖ ≤ Dstar p.toReal / 2 * ‖WithLp.toLp p ξ‖) ∧
    ∃ ξ : Fin 2 → ℝ, ξ ≠ 0 ∧
      1 / 2 * Qf p.toReal (ξ 0) (ξ 1) * ‖WithLp.toLp p ξ‖ = Dstar p.toReal / 2 * ‖WithLp.toLp p ξ‖ := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  obtain ⟨t, ht, -, -, -, hle, hD, -, -⟩ := Matsaev.lemma_3_3_proved p.toReal hq2
  refine ⟨fun ξ => ⟨Matsaev.Cov130.hasDerivAt_rot_norm p (by linarith) hptop ξ, ?_⟩, ![1, t], ?_, ?_⟩
  · by_cases h : (ξ 0, ξ 1) = (0, 0)
    · have hξ : ξ = 0 := by
        ext i
        fin_cases i
        exacts [congrArg Prod.fst h, congrArg Prod.snd h]
      subst hξ
      simp
    · have hQ := hle (ξ 0) (ξ 1) h
      rw [← hD] at hQ
      have hn := norm_nonneg (WithLp.toLp p ξ)
      nlinarith
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Matsaev.Gamma.Qf_one_pos ht.1, ← hD]
    ring

/-- **Section 1, Idea of the proof of Theorem A** (v1.90): "the derivative above is at most `(D_*/2)‖ξ‖_p`, with equality at
`ξ = (1, t_*)`" (`2 < p < ∞`; `t_*` the critical point of `f` in `(0, 1)`, as in `lemma_3_4`; the inequality is
`idea_rotation_growth`). Review r6, M2. -/
theorem idea_rotation_growth_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hcrit : deriv (dfun p.toReal) t = 0) :
    1 / 2 * Qf p.toReal 1 t * ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ =
      Dstar p.toReal / 2 * ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  rw [Matsaev.Gamma.Qf_one_pos ht.1, ← (Matsaev.Gamma.tstar_facts hq2 ht hcrit).1]
  ring

/-- **Section 1, Background**, in the definition's form: Matsaev's inequality (1) holds for `p = 1` and `p = ∞`. -/
theorem matsaev_conjecture_one_infty : MatsaevConjecture 1 ∧ MatsaevConjecture ⊤ := by
  refine ⟨fun Ω _ μ T hT P => ?_, fun Ω _ μ T hT P => ?_⟩
  · obtain ⟨h1, h2⟩ := background_p_one_infty 1 (Or.inl rfl) P Ω μ T hT
    exact h1.trans_eq h2
  · obtain ⟨h1, h2⟩ := background_p_one_infty ⊤ (Or.inr rfl) P Ω μ T hT
    exact h1.trans_eq h2

/-- **Lemma 2.3** (`lem:dual`), duality, `1 < p < ∞`, `p' = p/(p-1)`: `‖P(S)‖_p = ‖P(S)‖_{p'}`, and for a `2 × 2` matrix
`T`, `‖P(Tᵀ)‖_p = ‖P(T)‖_{p'}` and `‖Tᵀ‖_p = ‖T‖_{p'}`. Stated over `𝕜 = ℝ` or `ℂ` (the paper: real `T`, polynomial `P`;
over `ℂ` the transpose is the adjoint for the bilinear pairing, so this includes the paper's case). -/
theorem lemma_2_3 {𝕜 : Type} [RCLike 𝕜] (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p.toReal.HolderConjugate q.toReal) (P : 𝕜[X]) :
    shiftNorm p 𝕜 P = shiftNorm q 𝕜 P ∧
      ∀ T : Matrix (Fin 2) (Fin 2) 𝕜, matNorm p (aeval Tᵀ P) = matNorm q (aeval T P) ∧ matNorm p Tᵀ = matNorm q T :=
  Matsaev.lemma_2_3_proved p q hpq P

/-! ## Section 3: the shift has the norm of the rotation, for small `a` -/

/-- `P_a(J) = (1 + B) I + a J` (Section 3, before Lemma 3.4: "Since `P_a(J) = (1+B)I + aJ`"), since `J² = -I`. -/
theorem aeval_Jmat_Pa {𝕜 : Type} [RCLike 𝕜] (a B : 𝕜) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) 𝕜) (Pa a B) = (1 + B) • (1 : Matrix (Fin 2) (Fin 2) 𝕜) + a • Jmat :=
  Matsaev.aeval_Jmat_Pa_proved a B

/-- **Section 3** (before Lemma 3.1): "`C_a := ‖P_a(J)‖_p` (by Lemma 2.1, a maximum over real vectors)": for
`1 < p < ∞` and `1 + B > 0` (the paper fixes `p > 2`, `B > 0`), the norm of `P_a(J)` on the complex `ℓ^p_2` equals its norm
on the real `ℓ^p_2`, and the latter is attained at a real vector `ξ ≠ 0`. -/
theorem sec3_Ca_max (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (a B : ℝ) (hB : 0 < 1 + B) :
    matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa (a : ℂ) (B : ℂ))) =
        matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ∧
      ∃ ξ : Fin 2 → ℝ, ξ ≠ 0 ∧
        ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ)‖ =
          matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) * ‖WithLp.toLp p ξ‖ := by
  refine ⟨?_, ?_⟩
  · have hJ : (Jmat : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ) = Jmat := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Jmat]
    rw [← Matsaev.Assembly.Pa_map, ← hJ, Matsaev.Assembly.aeval_map_complex, lemma_2_1_matrix p hptop]
  · obtain ⟨φw, -, hmax⟩ :=
      Matsaev.TK.exists_max_angle p hptop (Matsaev.Assembly.one_lt_toReal hp hptop) a B hB
    refine ⟨![Real.cos φw, Real.sin φw], fun h => ?_, ?_⟩
    · have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
      have := Real.sin_sq_add_cos_sq φw
      rw [h0, h1] at this
      norm_num at this
    · rw [aeval_Jmat_Pa_proved]
      exact hmax

/-- **Lemma 3.1** (`lem:bellman`), the Bellman-function bound, real `ℓ^p`: if `G : ℝ² → ℝ` is continuous with
`G(0,0) = 0` and the window function `F` of eq. (`eq:bellman`) is `≥ 0` on `ℝ³`, then `‖P_a(S)‖_{ℓ^p} ≤ C`.
(Hypothesis `C ≥ 0`, weaker than the paper's `C > 0`. The lemma holds for every `1 ≤ p < ∞`, `a`, `B`.) -/
theorem lemma_3_1 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (a B C : ℝ) (hC : 0 ≤ C) (G : ℝ → ℝ → ℝ)
    (hG : Continuous (Function.uncurry G)) (hG0 : G 0 0 = 0)
    (hF : ∀ u v w : ℝ, 0 ≤ bellmanF p.toReal a B C G u v w) :
    shiftNorm p ℝ (Pa a B) ≤ C :=
  Matsaev.lemma_3_1_proved p hptop a B C hC G hG hG0 hF

/-- **Lemma 3.1** (`lem:bellman`), complex `ℓ^p` (the paper's last step: "by Lemma 2.1 also for complex `x`"). -/
theorem lemma_3_1_complex (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (a B C : ℝ) (hC : 0 ≤ C) (G : ℝ → ℝ → ℝ)
    (hG : Continuous (Function.uncurry G)) (hG0 : G 0 0 = 0)
    (hF : ∀ u v w : ℝ, 0 ≤ bellmanF p.toReal a B C G u v w) :
    shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) ≤ C := by
  have h := lemma_3_1 p hptop a B C hC G hG hG0 hF
  rwa [← lemma_2_1_shift p hptop (Pa a B), Matsaev.Assembly.Pa_map] at h

/-- **Section 3** (added in v1.50; before Lemma 3.4): with `h = a/(1+B)`, `‖P_a(J)ξ‖_p^p = (1+B)^p ‖ξ + hJξ‖_p^p` for real `ξ`
(`P_a(J) = (1+B)I + aJ = (1+B)(I + hJ)`). -/
theorem sec3_PaJ_scaling (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B : ℝ) (hB : 0 < 1 + B) (ξ : Fin 2 → ℝ) :
    ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ)‖ ^ p.toReal =
      (1 + B) ^ p.toReal * ‖WithLp.toLp p (ξ + (a / (1 + B)) • (Jmat *ᵥ ξ))‖ ^ p.toReal := by
  have h : aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ = (1 + B) • (ξ + (a / (1 + B)) • (Jmat *ᵥ ξ)) := by
    rw [aeval_Jmat_Pa, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, smul_add,
      smul_smul, show (1 + B) * (a / (1 + B)) = a by field_simp]
  rw [h, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hB, Real.mul_rpow hB.le (norm_nonneg _)]

/-- **Section 1, Idea of the proof of Theorem A** and **Lemma 3.1** (`lem:bellman`) (added in v1.50): a Bellman function is "a
function `G` of two real variables with `|(P_a(S)x)_n|^p ≤ C^p|x_n|^p + G(x_{n-1},x_{n-2}) - G(x_n,x_{n-1})` for every
real `x ∈ ℓ^p(ℕ)` (with `x_{-1} = x_{-2} = 0`) and every `n`". Here `(P_a(S)x)_n = x_n + a x_{n-1} - B x_{n-2}`, so this
inequality at `x, n` is `F(x_n, x_{n-1}, x_{n-2}) ≥ 0` for the window function `F` of eq. (`eq:bellman`); Lemma 3.1's
hypothesis `F ≥ 0` on `ℝ³` gives it for every `x` and every `n`. -/
theorem idea_bellman_window (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B C : ℝ) (G : ℝ → ℝ → ℝ) (x : lp (fun _ : ℕ => ℝ) p)
    (n : ℕ) :
    aeval (shiftOp p ℝ) (Pa a B) x n =
        x n + a * (if 1 ≤ n then x (n - 1) else 0) - B * (if 2 ≤ n then x (n - 2) else 0) ∧
      ((∀ u v w : ℝ, 0 ≤ bellmanF p.toReal a B C G u v w) →
        |aeval (shiftOp p ℝ) (Pa a B) x n| ^ p.toReal ≤ C ^ p.toReal * |x n| ^ p.toReal +
          G (if 1 ≤ n then x (n - 1) else 0) (if 2 ≤ n then x (n - 2) else 0) -
          G (x n) (if 1 ≤ n then x (n - 1) else 0)) := by
  have h1 : (shiftOp p ℝ x) n = if 1 ≤ n then x (n - 1) else 0 := by
    have := Matsaev.JLower.shiftOp_pow_apply p 1 x n
    rwa [pow_one] at this
  have h2 : (shiftOp p ℝ (shiftOp p ℝ x)) n = if 2 ≤ n then x (n - 2) else 0 := by
    simpa [sq] using Matsaev.JLower.shiftOp_pow_apply p 2 x n
  have hop : aeval (shiftOp p ℝ) (Pa a B) x = x + a • shiftOp p ℝ x - B • (shiftOp p ℝ (shiftOp p ℝ x)) := by
    simp [Pa, Algebra.algebraMap_eq_smul_one, sq]
  have h : aeval (shiftOp p ℝ) (Pa a B) x n =
      x n + a * (if 1 ≤ n then x (n - 1) else 0) - B * (if 2 ≤ n then x (n - 2) else 0) := by
    rw [hop, ← h1, ← h2]
    simp only [lp.coeFn_add, lp.coeFn_sub, lp.coeFn_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨h, fun hF => ?_⟩
  have hw := hF (x n) (if 1 ≤ n then x (n - 1) else 0) (if 2 ≤ n then x (n - 2) else 0)
  unfold bellmanF at hw
  rw [h]
  linarith

/-- **Lemma 3.2** (`lem:B0`), the case `a = 0`: with `G₀` and `C = 1 + B` the window function is
`F₀(u, v, w) = (1+B)^(p-1)(|u|^p + B|w|^p) - |u - Bw|^p ≥ 0`, with equality exactly on the plane `w = -u`.
(Stated for `p > 1`; the paper's section fixes `p > 2`.) -/
theorem lemma_3_2 (p : ℝ) (hp : 1 < p) (B : ℝ) (hB : 0 < B) (u v w : ℝ) :
    bellmanF p 0 B (1 + B) (G0 p B) u v w = F0 p B u w ∧ 0 ≤ F0 p B u w ∧ (F0 p B u w = 0 ↔ w = -u) :=
  Matsaev.lemma_3_2_proved p hp B hB u v w

/-- **Eq. `eq:Qexp`** (Section 3, "The function Q"): for `2 < p < ∞`, `B > 0`,
`‖P_a(J)ξ‖_p^p = (1+B)^p‖ξ‖_p^p(1 + pa/(1+B) Q(ξ)) + O(a²)‖ξ‖_p^p` uniformly in `ξ ∈ ℝ²`, with the `O(a²)` explicit:
`|error| ≤ K a² ‖ξ‖_p^p` for `|a| ≤ 1`. `Q(ξ) = ⟨φ(ξ), Jξ⟩/‖ξ‖_p^p` is `Qf p (ξ 0) (ξ 1)` (`Qf p 0 0 = 0`, so `ξ = 0` is
included). Route: a global Taylor bound for `|y|^p` (Matsaev/Assembly/Qexp.lean). -/
theorem eq_Qexp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, ∀ a : ℝ, |a| ≤ 1 → ∀ ξ : Fin 2 → ℝ,
      |‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ)‖ ^ p.toReal -
          (1 + B) ^ p.toReal * ‖WithLp.toLp p ξ‖ ^ p.toReal *
            (1 + p.toReal * a / (1 + B) * Qf p.toReal (ξ 0) (ξ 1))| ≤
        K * a ^ 2 * ‖WithLp.toLp p ξ‖ ^ p.toReal := by
  have hq2 : 2 < p.toReal := Matsaev.Assembly.two_lt_toReal hp hptop
  refine ⟨2 * p.toReal * (p.toReal - 1) * (2 + B) ^ (p.toReal - 2), fun a ha ξ => ?_⟩
  have hξ : ξ = ![ξ 0, ξ 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hξ, Matsaev.SJ.PaJ_mulVec, norm_toLp_fin2_rpow p hptop, norm_toLp_fin2_rpow p hptop]
  exact Matsaev.Qexp.qexp hq2 B hB a ha (ξ 0) (ξ 1)

/-- **Section 3** (before Lemma 3.4): "For real `σ` put `f(σ) = Q(1, σ) = σ(1 - |σ|^(p-2))/(1 + |σ|^p)`": the identity
holds for every real `σ` (and every real `p`); for `σ > 0` it is the function `dfun p` of the rest of the paper. -/
theorem eq_f_def (p σ : ℝ) :
    Qf p 1 σ = σ * (1 - |σ| ^ (p - 2)) / (1 + |σ| ^ p) ∧ (0 < σ → Qf p 1 σ = dfun p σ) :=
  ⟨Matsaev.Gamma.Qf_one_left p σ, fun h => Matsaev.Gamma.Qf_one_pos h⟩

/-- **Lemma 3.4** (`lem:N1`), the maximum of `Q`: for `p > 2`, `f = dfun` has exactly
one critical point `t_* ∈ (0, 1)`; it is a nondegenerate maximum; `D_* = max_{w≠0} Q(w) = f(t_*) > 0` is attained exactly on
the nonzero multiples of `(1, t_*)` and `J(1, t_*) = (t_*, -1)`; and (`eq:ST`): `1 + t_*^(2p-2) = (p-1) t_*^(p-2) (1 + t_*²)`. -/
theorem lemma_3_4 (p : ℝ) (hp : 2 < p) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1,
      (∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun p) s = 0 ↔ s = t) ∧
      deriv (deriv (dfun p)) t < 0 ∧
      0 < dfun p t ∧
      (∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf p u v ≤ dfun p t) ∧
      Dstar p = dfun p t ∧
      (∀ u v : ℝ, (u, v) ≠ (0, 0) →
        (Qf p u v = dfun p t ↔ ∃ r : ℝ, r ≠ 0 ∧ ((u, v) = (r, r * t) ∨ (u, v) = (r * t, -r)))) ∧
      1 + t ^ (2 * p - 2) = (p - 1) * t ^ (p - 2) * (1 + t ^ 2) :=
  Matsaev.lemma_3_3_proved p hp

/-- **Lemma 3.4** (`lem:N1`), the worked values after its proof: `t_* = 2 sin(π/12)`, `D_* = 2^(-3/2)` for `p = 4`, and
`t_* = (√5 - 1)/2`, `D_* = 1/2` for `p = 6`. Here `t_*` is pinned as the unique critical point of `f` in `(0, 1)`, as in
`lemma_3_4`. Route: Matsaev/Assembly/Values.lean. -/
theorem lemma_3_4_examples :
    ((∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun 4) s = 0 ↔ s = 2 * Real.sin (Real.pi / 12)) ∧
        Dstar 4 = (2 : ℝ) ^ (-(3 / 2 : ℝ))) ∧
      ((∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun 6) s = 0 ↔ s = (Real.sqrt 5 - 1) / 2) ∧ Dstar 6 = 1 / 2) :=
  ⟨Matsaev.Values.values_four, Matsaev.Values.values_six⟩

/-- **Lemma 3.5 (i)-(iii)** (`lem:SJmax`), in the angle form that the proof of Theorem 3.6 consumes (the paper's own form is `lemma_3_5_i_iii` below, proved from this). There is a maximum angle `θ_* = arctan t_*`
(`Angle.IsThetaStar`: Lemma 3.4 on the unit circle), and for small `a > 0` an angle `θ_a` with `|θ_a - θ_*| ≤ a` where
`Σ_a(e(θ_a)) = 0`, and `Σ_a(e(θ)) ≥ a η · min(ρ, dist(θ, θ_a + (π/2)ℤ))²` for every `ρ ∈ (0, ρ₀]` (with `a₁, η` depending
on `ρ`; review r2, finding 5: this is the form Steps 4-6 consume). Lemma 3.5 (iv), that `a ↦ s_a` and
`a ↦ C_a^p` are real-analytic, is `lemma_3_5_full` (the formal proof does not use it). The paper uses it in Step 4 of the proof of Theorem 3.6 (`|λ(a)| ≤ Λa`), in Step 6
(`∂_s N_a = O(a)`) and in Lemma 4.1 (the expansion `ξ_a = ξ_0 + a ξ' + o(a)`). Our route replaces these by `|θ_a - θ_*| ≤ a`
with explicit Lipschitz and Taylor bounds (Matsaev/SJ/BellmanLam.lean, BellmanLip.lean, BellmanEst.lean), and by
`TK.key_localization` (Matsaev/TK/Moving.lean), used in Matsaev/TK/Gain.lean, for Lemma 4.1. Analyticity of `C_a^p` is
never used. -/
theorem lemma_3_5_angle_form (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ θs : ℝ, Angle.IsThetaStar p.toReal θs ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ a₁ η : ℝ, 0 < a₁ ∧ 0 < η ∧ ∀ a : ℝ, 0 < a → a < a₁ →
      ∃ θa : ℝ, |θa - θs| ≤ a ∧
        Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θa = 0 ∧
        ∀ θ : ℝ, a * η * (min ρ (Angle.angDist θ θa)) ^ 2 ≤
          Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ := by
  obtain ⟨θs, hθs⟩ := Matsaev.Angle.exists_isThetaStar p.toReal (Matsaev.Assembly.two_lt_toReal hp hptop)
  exact ⟨θs, hθs, Matsaev.SJ.sigma_interface p hp hptop B hB θs hθs⟩

/-- **Lemma 3.5 (i)-(iii)** (`lem:SJmax`), in the paper's form, on the unit circle `s = e(θ) = (cos θ, sin θ)` with the
angular distance (`O_a = {±s_a, ±J s_a}` is the coset `θ_a + (π/2)ℤ`, and `e_* = e(arctan t_*)`, `t_*` the critical point
of Lemma 3.4 = `lemma_3_4`): for `p > 2`, `B > 0` there are `ρ ∈ (0, ½ arctan t_*)` and `a₁, δ, η > 0` such that for
`0 < a < a₁` there is `θ_a` with
(i) `Σ_a(e(θ)) = 0` exactly for `θ ∈ θ_a + (π/2)ℤ`; these are exactly the `θ` with `‖P_a(J) e(θ)‖_p = C_a ‖e(θ)‖_p`, the
maximisers of `‖P_a(J)s‖_p/‖s‖_p` (whose maximum is `C_a = ‖P_a(J)‖_p`); and `|θ_a - arctan t_*| ≤ ρ/2`, so `s_a = e(θ_a)`
is the point of `O_a` nearest to `e_*` and `O_a` lies within angular distance `ρ/2` of `O_0`;
(ii) `Σ_a(e(θ)) ≥ a δ` if `e(θ)` is at angular distance at least `ρ` from `O_a`;
(iii) `Σ_a(e(θ)) ≥ a η r²` if `e(θ)` is at angular distance `r ≤ ρ` from `O_a`.
Proved from `lemma_3_5_angle_form` and `lemma_3_4`. Part (iv) (analyticity) is `lemma_3_5_full` below; the formal proof of
Theorem 3.6 does not use it. -/
theorem lemma_3_5_i_iii (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, (∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun p.toReal) s = 0 ↔ s = t) ∧
    ∃ ρ a₁ δ η : ℝ, 0 < ρ ∧ ρ < Real.arctan t / 2 ∧ 0 < a₁ ∧ 0 < δ ∧ 0 < η ∧ ∀ a : ℝ, 0 < a → a < a₁ →
      ∃ θa : ℝ,
        (∀ θ : ℝ, Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ = 0 ↔
          ∃ k : ℤ, θ = θa + k * (Real.pi / 2)) ∧
        (∀ θ : ℝ, Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ = 0 ↔
          ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ![Real.cos θ, Real.sin θ])‖ =
            matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) *
              ‖WithLp.toLp p (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ)‖) ∧
        |θa - Real.arctan t| ≤ ρ / 2 ∧
        (∀ θ : ℝ, ρ ≤ Angle.angDist θ θa →
          a * δ ≤ Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ) ∧
        (∀ θ : ℝ, Angle.angDist θ θa ≤ ρ →
          a * η * Angle.angDist θ θa ^ 2 ≤
            Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ) := by
  have hq2 : 2 < p.toReal := Matsaev.Assembly.two_lt_toReal hp hptop
  have hq0 : 0 < p.toReal := by linarith
  obtain ⟨t, ht, hcrit, -, -, -, hD, hatt, -⟩ := lemma_3_4 p.toReal hq2
  obtain ⟨θs, hθs, ρ₀, hρ₀, hstep⟩ := lemma_3_5_angle_form p hp hptop B hB
  -- `θ_*` (the maximum angle of `lemma_3_5_angle_form`) is `arctan t_*`.
  have hθt : θs = Real.arctan t := by
    obtain ⟨hθ0, hθ4⟩ := hθs.mem
    have hc : 0 < Real.cos θs := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hs : 0 < Real.sin θs := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
    have hne : (Real.cos θs, Real.sin θs) ≠ ((0 : ℝ), (0 : ℝ)) := fun h => by
      simp only [Prod.mk.injEq] at h; linarith [h.1]
    have hQ : Qf p.toReal (Real.cos θs) (Real.sin θs) = dfun p.toReal t := by
      rw [← hD]; exact hθs.eq_at
    obtain ⟨r, -, hr⟩ := (hatt _ _ hne).1 hQ
    rcases hr with hr | hr
    · simp only [Prod.mk.injEq] at hr
      have htan : Real.tan θs = t := by
        rw [Real.tan_eq_sin_div_cos, hr.1, hr.2]; field_simp [hr.1 ▸ hc.ne']
      rw [← htan, Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    · simp only [Prod.mk.injEq] at hr
      nlinarith [ht.1, hr.1, hr.2]
  have hθs0 : 0 < θs := hθs.mem.1
  set ρ := min ρ₀ (θs / 4) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (by linarith)
  have hρθ : ρ < Real.arctan t / 2 := by
    rw [← hθt]; linarith [min_le_right ρ₀ (θs / 4)]
  obtain ⟨a₁, η, ha₁, hη, hmain⟩ := hstep ρ hρ (min_le_left _ _)
  refine ⟨t, ht, hcrit, ρ, min a₁ (ρ / 2), η * ρ ^ 2, η, hρ, hρθ, lt_min ha₁ (by linarith), by positivity, hη,
    fun a ha ha' => ?_⟩
  obtain ⟨θa, hθa, hzero, hlow⟩ := hmain a ha (lt_of_lt_of_le ha' (min_le_left _ _))
  set A := aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) with hAdef
  set C := matNorm p A with hCdef
  have hper : Function.Periodic (Angle.SigmaAng p.toReal a B C) (Real.pi / 2) := by
    intro θ
    simp only [Angle.SigmaAng]
    rw [Angle.Nang_periodic p.toReal θ, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two,
      show (1 + B) * -Real.sin θ + a * Real.cos θ = -((1 + B) * Real.sin θ - a * Real.cos θ) by ring, abs_neg,
      show (1 + B) * Real.cos θ - a * -Real.sin θ = (1 + B) * Real.cos θ + a * Real.sin θ by ring]
    ring
  refine ⟨θa, fun θ => ⟨fun h0 => ?_, ?_⟩, fun θ => ?_, ?_, fun θ hθ => ?_, fun θ hθ => ?_⟩
  · -- (i) a zero of `Σ_a` is at angular distance `0` from `θ_a`
    have hd : Angle.angDist θ θa = 0 := by
      by_contra hne
      have hpos : 0 < Angle.angDist θ θa := lt_of_le_of_ne (Matsaev.SJ.angDist_nonneg _ _) (Ne.symm hne)
      have hm : 0 < min ρ (Angle.angDist θ θa) := lt_min hρ hpos
      have h1 : 0 < a * η * (min ρ (Angle.angDist θ θa)) ^ 2 := by positivity
      linarith [hlow θ]
    obtain ⟨k, hk⟩ := Matsaev.SJ.exists_int_angDist θ θa
    rw [hd, abs_eq_zero] at hk
    exact ⟨k, by linarith⟩
  · rintro ⟨k, rfl⟩
    rw [hper.int_mul k θa]
    exact hzero
  · -- (i) the zeros are the maximisers of `‖P_a(J)s‖_p / ‖s‖_p`
    have hmv : A *ᵥ ![Real.cos θ, Real.sin θ] =
        ![(1 + B) * Real.cos θ + a * Real.sin θ, (1 + B) * Real.sin θ - a * Real.cos θ] := by
      rw [hAdef, aeval_Jmat_Pa_proved, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Jmat_mulVec]
      ext i
      fin_cases i <;> simp [sub_eq_add_neg]
    have hN : Angle.Nang p.toReal θ = ‖WithLp.toLp p (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ)‖ ^ p.toReal := by
      rw [norm_toLp_fin2_rpow p hptop]; rfl
    have hAx : ‖WithLp.toLp p (A *ᵥ ![Real.cos θ, Real.sin θ])‖ ^ p.toReal =
        |(1 + B) * Real.cos θ + a * Real.sin θ| ^ p.toReal + |(1 + B) * Real.sin θ - a * Real.cos θ| ^ p.toReal := by
      rw [hmv, norm_toLp_fin2_rpow p hptop]
    have hC0 : 0 ≤ C := matNorm_nonneg _ _
    unfold Angle.SigmaAng
    rw [hN, ← hAx, ← Real.mul_rpow hC0 (norm_nonneg _)]
    constructor
    · intro h
      have h' : ‖WithLp.toLp p (A *ᵥ ![Real.cos θ, Real.sin θ])‖ ^ p.toReal =
          (C * ‖WithLp.toLp p (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ)‖) ^ p.toReal := by linarith
      exact (Real.rpow_left_inj (norm_nonneg _) (mul_nonneg hC0 (norm_nonneg _)) hq0.ne').mp h'
    · intro h
      rw [h]; ring
  · -- (i) `θ_a` is within `ρ/2` of `θ_* = arctan t_*`
    rw [← hθt]
    linarith [min_le_right a₁ (ρ / 2)]
  · -- (ii)
    calc a * (η * ρ ^ 2) = a * η * (min ρ (Angle.angDist θ θa)) ^ 2 := by rw [min_eq_left hθ]; ring
      _ ≤ _ := hlow θ
  · -- (iii)
    have h := hlow θ
    rwa [min_eq_right hθ] at h

/-- **Lemma 3.5** (`lem:SJmax`), parts (i)-(iv) together, in the paper's form, with the same `ρ, a₁, δ, η`. `θf a` is the
angle of `s_a = e(θf a) = (cos θf a, sin θf a)`: for `0 < a < a₁`, (i)-(iii) hold as in `lemma_3_5_i_iii` with `θ_a = θf a`;
and (iv) `s_0 = e_* = (1, t_*)/‖(1, t_*)‖₂`, and `a ↦ s_a` and `a ↦ C_a^p = ‖P_a(J)‖_p^p` are real-analytic on `[0, a₁)`.
"Real-analytic on `[0, a₁)`" is Mathlib's `AnalyticOn ℝ f (Set.Ico 0 a₁)`: at each point of `[0, a₁)` a power series
converges to `f` on a neighbourhood of the point within `[0, a₁)` (one-sided at `0`). The one-sided form is the true one:
`C_a` is even in `a`, so `a ↦ C_a^p` has a corner at `0` as a function on `ℝ`. Route: Matsaev/Assembly/Lem35iv.lean (a Morse
factor of `D_* - Q` at `θ_*` and Mathlib's analytic implicit function theorem). -/
theorem lemma_3_5_full (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, (∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun p.toReal) s = 0 ↔ s = t) ∧
    ∃ ρ a₁ δ η : ℝ, 0 < ρ ∧ ρ < Real.arctan t / 2 ∧ 0 < a₁ ∧ 0 < δ ∧ 0 < η ∧ ∃ θf : ℝ → ℝ,
      (∀ a : ℝ, 0 < a → a < a₁ →
        (∀ θ : ℝ, Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ = 0 ↔
          ∃ k : ℤ, θ = θf a + k * (Real.pi / 2)) ∧
        (∀ θ : ℝ, Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ = 0 ↔
          ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ![Real.cos θ, Real.sin θ])‖ =
            matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) *
              ‖WithLp.toLp p (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ)‖) ∧
        |θf a - Real.arctan t| ≤ ρ / 2 ∧
        (∀ θ : ℝ, ρ ≤ Angle.angDist θ (θf a) →
          a * δ ≤ Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ) ∧
        (∀ θ : ℝ, Angle.angDist θ (θf a) ≤ ρ →
          a * η * Angle.angDist θ (θf a) ^ 2 ≤
            Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ)) ∧
      (![Real.cos (θf 0), Real.sin (θf 0)] : Fin 2 → ℝ) = (Real.sqrt (1 + t ^ 2))⁻¹ • ![1, t] ∧
      AnalyticOn ℝ (fun a => (![Real.cos (θf a), Real.sin (θf a)] : Fin 2 → ℝ)) (Set.Ico 0 a₁) ∧
      AnalyticOn ℝ (fun a => matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ p.toReal)
        (Set.Ico 0 a₁) := by
  have hq2 : 2 < p.toReal := Matsaev.Assembly.two_lt_toReal hp hptop
  obtain ⟨t, ht, hcrit, ρ, a₁, δ, η, hρ, hρt, ha₁, hδ, hη, H⟩ := lemma_3_5_i_iii p hp hptop B hB
  obtain ⟨θs, hθs, -⟩ := lemma_3_5_angle_form p hp hptop B hB
  have hθt : θs = Real.arctan t := Matsaev.Lem35iv.thetaStar_eq_arctan hq2 hθs ht hcrit
  obtain ⟨θf, hθf0, a₂, ha₂, hzero, hθfA, hCA⟩ := Matsaev.Lem35iv.core p hp hptop B hB θs hθs
  have harc : Real.arctan t < Real.pi / 4 := by rw [← Real.arctan_one]; exact Real.arctan_strictMono ht.2
  have ha₃ : 0 < min a₁ (min a₂ ρ) := lt_min ha₁ (lt_min ha₂ hρ)
  have hsub : Set.Ico 0 (min a₁ (min a₂ ρ)) ⊆ Set.Ioo (-a₂) a₂ := fun x hx =>
    ⟨by linarith [hx.1], lt_of_lt_of_le hx.2 ((min_le_right _ _).trans (min_le_left _ _))⟩
  refine ⟨t, ht, hcrit, ρ, min a₁ (min a₂ ρ), δ, η, hρ, hρt, ha₃, hδ, hη, θf, fun a ha ha' => ?_, ?_, ?_, ?_⟩
  · have haa₁ : a < a₁ := lt_of_lt_of_le ha' (min_le_left _ _)
    have haa₂ : a < a₂ := lt_of_lt_of_le ha' ((min_le_right _ _).trans (min_le_left _ _))
    have haρ : a < ρ := lt_of_lt_of_le ha' ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨θa, h1, h2, h3, h4, h5⟩ := H a ha haa₁
    obtain ⟨hθfa, hz⟩ := hzero a ha haa₂
    -- `θf a` is a zero of `Σ_a`, so `θf a = θ_a + k π/2`; both are near `θ_*`, so `k = 0`
    obtain ⟨k, hk⟩ := (h1 (θf a)).mp hz
    rw [hθt] at hθfa
    have hb1 := abs_le.mp hθfa
    have hb2 := abs_le.mp h3
    have hpi := Real.pi_pos
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hkn | hkz | hkp
      · have hk1 : (k : ℝ) ≤ -1 := by
          have : k ≤ -1 := by omega
          exact_mod_cast this
        have : (k : ℝ) * (Real.pi / 2) ≤ -(Real.pi / 2) := by nlinarith
        linarith
      · exact hkz
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hkp
        have : Real.pi / 2 ≤ (k : ℝ) * (Real.pi / 2) := by nlinarith
        linarith
    have heq : θf a = θa := by rw [hk, hk0]; simp
    rw [heq]
    exact ⟨h1, h2, h3, h4, h5⟩
  · rw [hθf0, hθt, Real.cos_arctan, Real.sin_arctan]
    ext i
    fin_cases i <;> simp [div_eq_inv_mul]
  · rw [analyticOn_pi_iff]
    intro i x hx
    have hA := hθfA x (hsub hx)
    fin_cases i
    · exact (Real.analyticAt_cos.comp hA).analyticWithinAt
    · exact (Real.analyticAt_sin.comp hA).analyticWithinAt
  · exact hCA.mono (Set.Ico_subset_Ico_right ((min_le_right _ _).trans (min_le_left _ _)))

/-- **Lemma 3.5** (`lem:SJmax`), proof (added in v1.90): "As `Σ_0 = 0`, `Σ'(s)` is the right derivative of `Σ_a(s)` at
`a = 0`", with the display before it, "`Σ_a(s)/a → Σ'(s) := 2p(1+B)^(p-1)‖s‖_p^p(D_* - Q(s))` (`a → 0⁺`), uniformly on the
unit circle" (here with the rate `K a`), for `2 < p < ∞`, `B > 0`, on the unit circle `s = e(θ)` (`‖s‖_p^p = Nang`,
`Q(s) = qang`). Route: eq. (`eq:Qexp`) for `‖P_a(J)s‖_p^p` and for `C_a^p` (upper bound at a norming vector, lower bound at
`(1, t_*)`). Lean's proof of Lemma 3.5 itself does not use this (route note 11). -/
theorem lemma_3_5_sigma_right_deriv (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    (∀ θ : ℝ, Angle.SigmaAng p.toReal 0 B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B))) θ = 0) ∧
    (∃ K : ℝ, ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ θ : ℝ,
      |Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ / a -
          2 * p.toReal * (1 + B) ^ (p.toReal - 1) * Angle.Nang p.toReal θ *
            (Dstar p.toReal - Angle.qang p.toReal θ)| ≤ K * a) ∧
    ∀ θ : ℝ, HasDerivWithinAt
      (fun a => Angle.SigmaAng p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ)
      (2 * p.toReal * (1 + B) ^ (p.toReal - 1) * Angle.Nang p.toReal θ * (Dstar p.toReal - Angle.qang p.toReal θ))
      (Set.Ici 0) 0 := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  have hp1 : 1 < p := lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp
  have hB1 : 0 < 1 + B := by linarith
  obtain ⟨t, -, -, -, htpos, hle, hD, hmaxset, -⟩ := lemma_3_4 p.toReal hq2
  obtain ⟨K1, hK1⟩ := eq_Qexp p hp hptop B hB
  set q := p.toReal with hqdef
  have hq0 : 0 < q := by linarith
  set D := Dstar q with hDdef
  have hQ : ∀ u v : ℝ, Qf q u v ≤ D := by
    intro u v
    by_cases h : (u, v) = (0, 0)
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2, hD]
      simp [Qf, htpos.le]
    · rw [hD]
      exact hle _ _ h
  have hQt : Qf q 1 t = D := by
    rw [hD]
    exact (hmaxset 1 t (by simp)).2 ⟨1, one_ne_zero, Or.inl (by simp)⟩
  -- `Σ_0 = 0`
  have hzero : ∀ θ : ℝ,
      Angle.SigmaAng q 0 B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B))) θ = 0 := by
    intro θ
    rw [(Matsaev.Qexp.p0_norms p B hB).1]
    simp only [Angle.SigmaAng, Angle.Nang, zero_mul, add_zero, sub_zero]
    rw [abs_mul, abs_mul, abs_of_pos hB1, Real.mul_rpow hB1.le (abs_nonneg _),
      Real.mul_rpow hB1.le (abs_nonneg _)]
    ring
  -- `C_a^p = (1+B)^p (1 + p a D_*/(1+B)) + O(a²)` for `0 ≤ a ≤ 1`
  have hnpos : ∀ ξ : Fin 2 → ℝ, ξ ≠ 0 → 0 < ‖WithLp.toLp p ξ‖ ^ q := by
    intro ξ hξ
    apply Real.rpow_pos_of_pos
    rw [norm_pos_iff]
    intro h
    apply hξ
    simpa using congrArg WithLp.ofLp h
  have hCup : ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ q ≤
        (1 + B) ^ q * (1 + q * a / (1 + B) * D) + |K1| * a ^ 2 := by
    intro a ha0 ha1
    obtain ⟨-, ξ, hξ0, hξ⟩ := sec3_Ca_max p hp1 hptop a B hB1
    have hn := hnpos ξ hξ0
    have h := (abs_le.mp (hK1 a (abs_le.mpr ⟨by linarith, ha1⟩) ξ)).2
    rw [hξ, Real.mul_rpow (matNorm_nonneg _ _) (norm_nonneg _)] at h
    have hc : 0 ≤ (1 + B) ^ q * ‖WithLp.toLp p ξ‖ ^ q * (q * a / (1 + B)) := by positivity
    have hcQ := mul_le_mul_of_nonneg_left (hQ (ξ 0) (ξ 1)) hc
    have hK : K1 * a ^ 2 * ‖WithLp.toLp p ξ‖ ^ q ≤ |K1| * a ^ 2 * ‖WithLp.toLp p ξ‖ ^ q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K1) (sq_nonneg a)) hn.le
    refine le_of_mul_le_mul_right ?_ hn
    linarith
  have hClo : ∀ a : ℝ, |a| ≤ 1 →
      (1 + B) ^ q * (1 + q * a / (1 + B) * D) - |K1| * a ^ 2 ≤
        matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ q := by
    intro a ha
    have hξ0 : (![1, t] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp at this
    have hn := hnpos _ hξ0
    have h := (abs_le.mp (hK1 a ha ![1, t])).1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hQt] at h
    have hv := Real.rpow_le_rpow (norm_nonneg _)
      (norm_mulVec_le_matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ![1, t]) hq0.le
    rw [Real.mul_rpow (matNorm_nonneg _ _) (norm_nonneg _)] at hv
    have hK : K1 * a ^ 2 * ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ ^ q ≤
        |K1| * a ^ 2 * ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ ^ q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K1) (sq_nonneg a)) hn.le
    refine le_of_mul_le_mul_right ?_ hn
    linarith
  -- the bound `|Σ_a - aΣ'| ≤ K a²`
  set K0 := 2 * q * (q - 1) * (2 + B) ^ (q - 2) with hK0
  have hK0nn : 0 ≤ K0 := by
    have : 0 ≤ q - 1 := by linarith
    positivity
  have hbound : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ θ : ℝ,
      |Angle.SigmaAng q a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ -
          a * (2 * q * (1 + B) ^ (q - 1) * Angle.Nang q θ * (D - Angle.qang q θ))| ≤
        4 * (|K1| + K0) * a ^ 2 := by
    intro a ha0 ha1 θ
    have hN0 : 0 ≤ Angle.Nang q θ := by unfold Angle.Nang; positivity
    have hN2 : Angle.Nang q θ ≤ 2 := by
      unfold Angle.Nang
      have h1 := Real.rpow_le_one (abs_nonneg (Real.cos θ)) (Real.abs_cos_le_one θ) hq0.le
      have h2 := Real.rpow_le_one (abs_nonneg (Real.sin θ)) (Real.abs_sin_le_one θ) hq0.le
      linarith
    have hM := abs_le.mp (Matsaev.Qexp.qexp hq2 B hB a (abs_le.mpr ⟨by linarith, ha1⟩) (Real.cos θ) (Real.sin θ))
    have hup := hCup a ha0.le ha1
    have hlo := hClo a (abs_le.mpr ⟨by linarith, ha1⟩)
    set C := matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) with hCdef
    set N := Angle.Nang q θ with hNdef
    have hNdef' : N = |Real.cos θ| ^ q + |Real.sin θ| ^ q := rfl
    have hE : |C ^ q - (1 + B) ^ q * (1 + q * a / (1 + B) * D)| ≤ |K1| * a ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hNE : |N * (C ^ q - (1 + B) ^ q * (1 + q * a / (1 + B) * D))| ≤ 2 * (|K1| * a ^ 2) := by
      rw [abs_mul, abs_of_nonneg hN0]
      exact mul_le_mul hN2 hE (abs_nonneg _) (by norm_num)
    have hKN : K0 * a ^ 2 * N ≤ K0 * a ^ 2 * 2 :=
      mul_le_mul_of_nonneg_left hN2 (by positivity)
    rw [← hNdef'] at hM
    have hrp : (1 + B) ^ (q - 1) = (1 + B) ^ q / (1 + B) := Real.rpow_sub_one hB1.ne' q
    have hident : Angle.SigmaAng q a B C θ - a * (2 * q * (1 + B) ^ (q - 1) * N * (D - Angle.qang q θ)) =
        2 * (N * (C ^ q - (1 + B) ^ q * (1 + q * a / (1 + B) * D))) -
          2 * ((|(1 + B) * Real.cos θ + a * Real.sin θ| ^ q + |(1 + B) * Real.sin θ - a * Real.cos θ| ^ q) -
            (1 + B) ^ q * N * (1 + q * a / (1 + B) * Qf q (Real.cos θ) (Real.sin θ))) := by
      rw [hrp, Angle.SigmaAng, Angle.qang]
      field_simp
      ring
    rw [hident]
    have h1 := abs_le.mp hNE
    rw [abs_le]
    constructor <;> nlinarith [hM.1, hM.2, h1.1, h1.2, hKN]
  refine ⟨hzero, ⟨4 * (|K1| + K0), fun a ha0 ha1 θ => ?_⟩, fun θ => ?_⟩
  · have h := hbound a ha0 ha1 θ
    rw [show Angle.SigmaAng q a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ / a -
        2 * q * (1 + B) ^ (q - 1) * Angle.Nang q θ * (D - Angle.qang q θ) =
        (Angle.SigmaAng q a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ -
          a * (2 * q * (1 + B) ^ (q - 1) * Angle.Nang q θ * (D - Angle.qang q θ))) / a by
        field_simp, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
    calc _ ≤ 4 * (|K1| + K0) * a ^ 2 := h
      _ = 4 * (|K1| + K0) * a * a := by ring
  · have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
      exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, h.ne'⟩⟩
    rw [hasDerivWithinAt_iff_tendsto_slope, hset, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    set K := 4 * (|K1| + K0) with hKdef
    have hKnn : 0 ≤ K := by positivity
    refine ⟨min 1 (ε / (K + 1)), lt_min one_pos (div_pos hε (by linarith)), fun a ha hdist => ?_⟩
    have ha0 : 0 < a := ha
    rw [Real.dist_eq, sub_zero, abs_of_pos ha0] at hdist
    have ha1 : a ≤ 1 := (hdist.trans_le (min_le_left _ _)).le
    have haε : a < ε / (K + 1) := hdist.trans_le (min_le_right _ _)
    rw [slope_def_field, hzero θ, sub_zero, sub_zero, Real.dist_eq]
    have h := hbound a ha0 ha1 θ
    have h2 : |Angle.SigmaAng q a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ / a -
        2 * q * (1 + B) ^ (q - 1) * Angle.Nang q θ * (D - Angle.qang q θ)| ≤ K * a := by
      rw [show Angle.SigmaAng q a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ / a -
          2 * q * (1 + B) ^ (q - 1) * Angle.Nang q θ * (D - Angle.qang q θ) =
          (Angle.SigmaAng q a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) θ -
            a * (2 * q * (1 + B) ^ (q - 1) * Angle.Nang q θ * (D - Angle.qang q θ))) / a by
          field_simp, abs_div, abs_of_pos ha0, div_le_iff₀ ha0]
      calc _ ≤ 4 * (|K1| + K0) * a ^ 2 := h
        _ = K * a * a := by rw [hKdef]; ring
    have h3 : K * a < ε := by
      have : K * a ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left haε.le hKnn
      have h4 : K * (ε / (K + 1)) < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
      linarith
    exact lt_of_le_of_lt h2 h3

/-- **Milestone: the proof of Theorem 3.6** (`thm:SJ`), Steps 1-6 (review r1, finding 3): for `p > 2`, `B > 0` and all
small `a ≥ 0` there is a Bellman function `G` (continuous, `G(0,0) = 0`) whose window function `F` with `C = C_a = ‖P_a(J)‖_p`
is `≥ 0` on `ℝ³`. With Lemma 3.1 this gives `theorem_3_6_le` for `p > 2`. Proved from `lemma_3_5_angle_form` as stated. -/
theorem theorem_3_6_bellman (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a < a₀ → ∃ G : ℝ → ℝ → ℝ, Continuous (Function.uncurry G) ∧ G 0 0 = 0 ∧
      ∀ u v w : ℝ, 0 ≤ bellmanF p.toReal a B (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) G u v w := by
  obtain ⟨θs, hθs, hSig⟩ := lemma_3_5_angle_form p hp hptop B hB
  exact Matsaev.SJ.bellman_of_sigma p hp hptop B hB θs hθs hSig

/-- **Abstract** (and Section 1, Idea): for `p > 2`, `B > 0` and small `a ≥ 0`, "a Bellman function: a function `G` of two
real variables such that, for every real sequence `x ∈ ℓ^p(ℕ)` (with `x_{-1} = x_{-2} = 0`) and every `n ≥ 0`,
`|(P_a(S)x)_n|^p ≤ ‖P_a(J)‖^p|x_n|^p + G(x_{n-1}, x_{n-2}) - G(x_n, x_{n-1})`" (`G` continuous, `G(0,0) = 0`). From
`theorem_3_6_bellman` and `idea_bellman_window`. Review r6, S4. -/
theorem abstract_bellman (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a < a₀ → ∃ G : ℝ → ℝ → ℝ, Continuous (Function.uncurry G) ∧ G 0 0 = 0 ∧
      ∀ (x : lp (fun _ : ℕ => ℝ) p) (n : ℕ),
        |aeval (shiftOp p ℝ) (Pa a B) x n| ^ p.toReal ≤
          matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) ^ p.toReal * |x n| ^ p.toReal +
          G (if 1 ≤ n then x (n - 1) else 0) (if 2 ≤ n then x (n - 2) else 0) -
          G (x n) (if 1 ≤ n then x (n - 1) else 0) := by
  obtain ⟨a₀, ha₀, h⟩ := theorem_3_6_bellman p hp hptop B hB
  refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
  obtain ⟨G, hGc, hG0, hF⟩ := h a ha ha'
  exact ⟨G, hGc, hG0, fun x n => (idea_bellman_window p a B _ G x n).2 hF⟩

open scoped ContDiff in
/-- **Proof of Theorem 3.6, Step 3** (v2.00 wording, review r6 M4): "The function `|y|^p` is real-analytic in `y` for
`y ≠ 0`" (every real `p`): near `y ≠ 0` it is `(±y)^p` with a positive base. -/
theorem theorem_3_6_abs_rpow_analytic (p y : ℝ) (hy : y ≠ 0) : AnalyticAt ℝ (fun x : ℝ => |x| ^ p) y := by
  have hc : ContDiffAt ℝ ω (fun x : ℝ => |x| ^ p) y := by
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have h1 : ContDiffAt ℝ ω ((fun x : ℝ => x ^ p) ∘ fun x : ℝ => -x) y :=
        ContDiffAt.comp y (Real.contDiffAt_rpow_const_of_ne (neg_ne_zero.mpr hy)) contDiff_neg.contDiffAt
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hneg] with x hx
      simp [abs_of_neg (show x < 0 from hx)]
    · have h1 : ContDiffAt ℝ ω (fun x : ℝ => x ^ p) y := Real.contDiffAt_rpow_const_of_ne hy
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hpos] with x hx
      simp [abs_of_pos (show 0 < x from hx)]
  exact hc.analyticAt

/-- **Theorem 3.6** (`thm:SJ`), the inequality `‖P_a(S)‖ ≤ ‖P_a(J)‖` alone — the only part Theorem A uses (the proof of
Theorem 3.6 says so); it does not need Lemma 2.2. -/
theorem theorem_3_6_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) (B : ℝ) (hB : 0 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a < a₀ → shiftNorm p ℝ (Pa a B) ≤ matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) := by
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · obtain ⟨q, hq1, hqtop, hpq⟩ := Matsaev.Assembly.exists_conj p hp hptop
    have : Fact (1 ≤ q) := ⟨hq1⟩
    obtain ⟨hq2, -⟩ := Matsaev.Assembly.conj_gt_two hpq hlt
    obtain ⟨a₀, ha₀, hG⟩ := theorem_3_6_bellman q hq2 hqtop B hB
    refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
    obtain ⟨G, hGc, hG0, hF⟩ := hG a ha ha'
    have h := lemma_3_1 q hqtop a B _ (matNorm_nonneg _ _) G hGc hG0 hF
    obtain ⟨hS, hT⟩ := lemma_2_3 p q hpq (Pa a B)
    rw [hS]
    calc shiftNorm q ℝ (Pa a B) ≤ matNorm q (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) := h
      _ = matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ)ᵀ (Pa a B)) := ((hT Jmat).1).symm
      _ = matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) :=
        Matsaev.Assembly.matNorm_aeval_Jmat_transpose_Pa p hptop a B
  · obtain ⟨a₀, ha₀, hG⟩ := theorem_3_6_bellman p hgt hptop B hB
    refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
    obtain ⟨G, hGc, hG0, hF⟩ := hG a ha ha'
    exact lemma_3_1 p hptop a B _ (matNorm_nonneg _ _) G hGc hG0 hF

/-- **Theorem 3.6** (`thm:SJ`), shift = rotation, real spaces: for `p ∈ (1, ∞) \ {2}` and `B > 0` there is `a₀ > 0` with
`‖P_a(S)‖_{ℓ^p} = ‖P_a(J)‖_{ℓ^p_2}` for `0 ≤ a < a₀` (for `p < 2` the proof takes `a₀` from `p'`, as the paper does).
The complex spaces: `theorem_3_6_complex`. -/
theorem theorem_3_6 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) (B : ℝ) (hB : 0 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a < a₀ → shiftNorm p ℝ (Pa a B) = matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) := by
  obtain ⟨a₀, ha₀, h⟩ := theorem_3_6_le p hp hptop hp2 B hB
  exact ⟨a₀, ha₀, fun a ha ha' => le_antisymm (h a ha ha') (lemma_2_2 (𝕜 := ℝ) p (Pa a B))⟩

/-- **Theorem 3.6** (`thm:SJ`), complex spaces (the paper's `ℓ^p_2` is `ℂ²`): for `p ∈ (1, ∞) \ {2}` and `B > 0` there
is `a₀ > 0` with `‖P_a(S)‖_{ℓ^p} = ‖P_a(J)‖_{ℓ^p_2}` on the complex spaces for `0 ≤ a < a₀`. From `theorem_3_6` and
Lemma 2.1 (`lemma_2_1_shift`, `lemma_2_1_matrix`). -/
theorem theorem_3_6_complex (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) (B : ℝ)
    (hB : 0 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 ≤ a → a < a₀ →
      shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) = matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa (a : ℂ) (B : ℂ))) := by
  have hJ : (Jmat : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ) = Jmat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jmat]
  obtain ⟨a₀, ha₀, h⟩ := theorem_3_6 p hp hptop hp2 B hB
  refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
  rw [← Matsaev.Assembly.Pa_map, lemma_2_1_shift p hptop, ← hJ, Matsaev.Assembly.aeval_map_complex,
    lemma_2_1_matrix p hptop]
  exact h a ha ha'

/-- **Lemma 3.3** (`lem:B0q`), growth of `F₀` away from `Π`: with `ν = u + w` there is
`γ₁ > 0` with `F₀(u, w) ≥ γ₁ (|u| + |ν|)^(p-2) ν²` for all real `u, w` (`F₀` does not depend on `v`). -/
theorem lemma_3_3 (p : ℝ) (hp : 2 < p) (B : ℝ) (hB : 0 < B) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ u w : ℝ, c₁ * (|u| + |u + w|) ^ (p - 2) * (u + w) ^ 2 ≤ F0 p B u w :=
  Matsaev.lemma_3_5_proved p hp B hB

/-! ## Section 4: a contraction that beats the rotation -/

/-- `T_ε = exp(ε K_*) J` (Lemma 4.1, `lem:TK`); `Teps` is defined as `e^(-ε D_*/2) R_(ε/2) J`, and its closed form
`e^(-ε D_*/2) R_(π/2 + ε/2)` of Theorem A is `teps_eq_rot`. -/
theorem teps_eq_exp (p ε : ℝ) : Teps p ε = NormedSpace.exp (ε • Kstar p) * Jmat :=
  Matsaev.teps_eq_exp_proved p ε

/-- Theorem A's closed form (`thm:A`, and the end of the first paragraph of the proof of Lemma 4.1):
`T_ε = e^(-ε D_*/2) R_(π/2 + ε/2)`, i.e. `R_(ε/2) J = R_(π/2 + ε/2)`. -/
theorem teps_eq_rot (p ε : ℝ) : Teps p ε = Real.exp (-(ε * Dstar p / 2)) • Rot (Real.pi / 2 + ε / 2) := by
  rw [add_comm (Real.pi / 2)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Teps, Rot, Jmat, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.50): the matrix `T_ε = e^(-εD_*/2) R_(ε/2) J = e^(-εD_*/2) R_(π/2+ε/2)`;
"for real `ξ ≠ 0` put `Q(ξ) = (φ(ξ₁)ξ₂ - φ(ξ₂)ξ₁)/‖ξ‖_p^p`" (the `Q` of Section 3; here for every real `ξ`, `0/0 = 0`);
"`d/dε R_(ε/2)ξ |_{ε=0} = ½Jξ = ½(ξ₂, -ξ₁)`". -/
theorem idea_rotation_facts (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) :
    (∀ ε : ℝ, Teps p.toReal ε = Real.exp (-(ε * Dstar p.toReal / 2)) • (Rot (ε / 2) * Jmat) ∧
      Teps p.toReal ε = Real.exp (-(ε * Dstar p.toReal / 2)) • Rot (Real.pi / 2 + ε / 2)) ∧
    (∀ ξ : Fin 2 → ℝ, Qf p.toReal (ξ 0) (ξ 1) =
      (phi p.toReal (ξ 0) * ξ 1 - phi p.toReal (ξ 1) * ξ 0) / ‖WithLp.toLp p ξ‖ ^ p.toReal) ∧
    (∀ ξ : Fin 2 → ℝ, HasDerivAt (fun ε : ℝ => Rot (ε / 2) *ᵥ ξ) ((1 / 2 : ℝ) • (Jmat *ᵥ ξ)) 0 ∧
      Jmat *ᵥ ξ = ![ξ 1, -ξ 0]) := by
  refine ⟨fun ε => ⟨by rw [Teps, smul_mul_assoc], teps_eq_rot _ ε⟩, fun ξ => ?_, fun ξ => ⟨?_, ?_⟩⟩
  · have hξ : ξ = ![ξ 0, ξ 1] := by
      ext i
      fin_cases i <;> rfl
    rw [hξ, norm_toLp_fin2_rpow p hptop]
    rfl
  · have h : (fun ε : ℝ => Rot (ε / 2) *ᵥ ξ) =
        fun ε => Real.cos (ε / 2) • ξ + Real.sin (ε / 2) • (Jmat *ᵥ ξ) := by
      funext ε
      rw [Rot, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h]
    have hc := (((hasDerivAt_id' (0 : ℝ)).div_const 2).cos).smul_const ξ
    have hs := (((hasDerivAt_id' (0 : ℝ)).div_const 2).sin).smul_const (Jmat *ᵥ ξ)
    convert hc.add hs using 1
    simp
  · ext i
    fin_cases i <;> simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Lemma 4.1** (`lem:TK`): for `p > 2`, `B > 1`: `‖T_ε‖_p ≤ 1` for all `ε ≥ 0` (real and complex `ℓ^p_2`), and there
is `a₂ > 0` such that for each `0 < a < a₂`, `‖P_a(T_ε)‖_p > ‖P_a(J)‖_p` for all sufficiently small `ε > 0` (real `ℓ^p_2`;
the complex `ℓ^p_2`: `lemma_4_1_complex`). (The paper's proof also takes `a₂ ≤ a₁`, `a₁` from Lemma 3.5.) -/
theorem lemma_4_1 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 1 < B) :
    (∀ ε : ℝ, 0 ≤ ε →
      matNorm p (Teps p.toReal ε) ≤ 1 ∧ matNorm p ((Teps p.toReal ε).map (algebraMap ℝ ℂ)) ≤ 1) ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ a : ℝ, 0 < a → a < a₂ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) < matNorm p (aeval (Teps p.toReal ε) (Pa a B)) := by
  have hp1 : 1 < p := lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  obtain ⟨t, -, -, -, -, hle, hD, -, -⟩ := lemma_3_4 p.toReal hq2
  have hQ : ∀ u v : ℝ, (u, v) ≠ (0, 0) → Qf p.toReal u v ≤ Dstar p.toReal := fun u v h => by
    rw [hD]; exact hle u v h
  refine ⟨fun ε hε => ?_, ?_⟩
  · have h1 := Matsaev.teps_contraction_of p hp1 hptop hQ ε hε
    exact ⟨h1, (lemma_2_1_matrix p hptop _).trans_le h1⟩
  · exact Matsaev.lemma_4_1_b_proved p hp hptop B hB

/-- **Lemma 4.1** (`lem:TK`), its inequality on the complex `ℓ^p_2` (the contraction bound on both spaces is in
`lemma_4_1`): for `p > 2`, `B > 1` there is `a₂ > 0` such that for each `0 < a < a₂`, `‖P_a(T_ε)‖_p > ‖P_a(J)‖_p` on the
complex `ℓ^p_2` for all sufficiently small `ε > 0`. From `lemma_4_1` and Lemma 2.1 (`lemma_2_1_matrix`). -/
theorem lemma_4_1_complex (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 1 < B) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ a : ℝ, 0 < a → a < a₂ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa (a : ℂ) (B : ℂ))) <
        matNorm p (aeval ((Teps p.toReal ε).map (algebraMap ℝ ℂ)) (Pa (a : ℂ) (B : ℂ))) := by
  have hJ : (Jmat : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ) = Jmat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jmat]
  obtain ⟨-, a₂, ha₂, h⟩ := lemma_4_1 p hp hptop B hB
  refine ⟨a₂, ha₂, fun a ha ha' => ?_⟩
  obtain ⟨ε₀, hε₀, hε⟩ := h a ha ha'
  refine ⟨ε₀, hε₀, fun ε hε1 hε2 => ?_⟩
  rw [← Matsaev.Assembly.Pa_map, ← hJ, Matsaev.Assembly.aeval_map_complex, Matsaev.Assembly.aeval_map_complex,
    lemma_2_1_matrix p hptop, lemma_2_1_matrix p hptop]
  exact hε ε hε1 hε2

/-- **Proof of Lemma 4.1** (`lem:TK`), "`T_ε` is a contraction": `exp(εK_*) = e^(-εD_*/2) R_(ε/2)`; for real `ξ` and
`ξ(ε) = exp(εK_*)ξ`, `d/dε ‖ξ(ε)‖_p^p = p⟨φ(ξ(ε)), K_*ξ(ε)⟩`; `⟨φ(w), K_*w⟩ = ½‖w‖_p^p (Q(w) - D_*)` for `w ≠ 0`
(so `p⟨φ(ξ(ε)), K_*ξ(ε)⟩ = (p/2)‖ξ(ε)‖_p^p (Q(ξ(ε)) - D_*)`), and `⟨φ(w), K_*w⟩ ≤ 0` for every `w` (`p > 2`). -/
theorem lemma_4_1_contraction_deriv (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) :
    (∀ ε : ℝ, NormedSpace.exp (ε • Kstar p.toReal) = Real.exp (-(ε * Dstar p.toReal / 2)) • Rot (ε / 2)) ∧
    (∀ (ξ : Fin 2 → ℝ) (ε : ℝ),
      HasDerivAt (fun ε => ‖WithLp.toLp p (NormedSpace.exp (ε • Kstar p.toReal) *ᵥ ξ)‖ ^ p.toReal)
        (p.toReal * ∑ i, phi p.toReal ((NormedSpace.exp (ε • Kstar p.toReal) *ᵥ ξ) i) *
          (Kstar p.toReal *ᵥ (NormedSpace.exp (ε • Kstar p.toReal) *ᵥ ξ)) i) ε) ∧
    (∀ w : Fin 2 → ℝ, w ≠ 0 → ∑ i, phi p.toReal (w i) * (Kstar p.toReal *ᵥ w) i =
      1 / 2 * ‖WithLp.toLp p w‖ ^ p.toReal * (Qf p.toReal (w 0) (w 1) - Dstar p.toReal)) ∧
    (∀ w : Fin 2 → ℝ, ∑ i, phi p.toReal (w i) * (Kstar p.toReal *ᵥ w) i ≤ 0) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  refine ⟨Matsaev.Gamma.exp_eps_Kstar _, fun ξ ε => Matsaev.Gamma.hasDerivAt_norm_expK p (by linarith) hptop ξ ε,
    fun w hw => ?_, fun w => ?_⟩
  · obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, w = ![u, v] := ⟨w 0, w 1, by ext i; fin_cases i <;> rfl⟩
    have hne : (u, v) ≠ (0, 0) := fun h => hw (by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      ext i
      fin_cases i <;> rfl)
    rw [Matsaev.Gamma.inner_phi_Kstar (by linarith) u v (Matsaev.Gamma.normq_pos hne).ne',
      norm_toLp_fin2_rpow p hptop]
    rfl
  · obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, w = ![u, v] := ⟨w 0, w 1, by ext i; fin_cases i <;> rfl⟩
    have hg := Matsaev.Gamma.gfun_le hq2 ![u, v]
    rw [Matsaev.Gamma.gfun_two] at hg
    rw [Matsaev.Gamma.Kstar_mulVec, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith

/-- **Proof of Lemma 4.1** (`lem:TK`), "Derivative in ε": entrywise, `d/dε T_ε |₀ = K_* J` and
`d/dε T_ε² |₀ = K_* J² + J K_* J = -K_* + J K_* J`; for every real `ξ`, `d/dε ‖P_a(T_ε)ξ‖_p^p |₀ = p Γ(a, ξ)` with
`Γ(a, ξ) = ⟨φ(y), M_a ξ⟩`, `y = P_a(J)ξ`, `M_a = a K_* J + B (K_* - J K_* J)` (`p > 1`); and, with `J² = -I`,
`K_* J = -½(I + D_* J)` and `K_* - J K_* J = J - D_* I`. -/
theorem lemma_4_1_eps_deriv (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (a B : ℝ) :
    (∀ i j : Fin 2,
      HasDerivAt (fun ε => Teps p.toReal ε i j) ((Kstar p.toReal * Jmat : Matrix (Fin 2) (Fin 2) ℝ) i j) 0) ∧
    (∀ i j : Fin 2, HasDerivAt (fun ε => (Teps p.toReal ε ^ 2) i j)
      ((Kstar p.toReal * Jmat * Jmat + Jmat * Kstar p.toReal * Jmat : Matrix (Fin 2) (Fin 2) ℝ) i j) 0) ∧
    Kstar p.toReal * Jmat * Jmat + Jmat * Kstar p.toReal * Jmat = -Kstar p.toReal + Jmat * Kstar p.toReal * Jmat ∧
    (∀ ξ : Fin 2 → ℝ, HasDerivAt (fun ε => ‖WithLp.toLp p (aeval (Teps p.toReal ε) (Pa a B) *ᵥ ξ)‖ ^ p.toReal)
      (p.toReal * ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ) i) *
        ((a • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ξ) i) 0) ∧
    (Jmat : Matrix (Fin 2) (Fin 2) ℝ) * Jmat = -1 ∧
    Kstar p.toReal * Jmat = -(1 / 2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℝ) + Dstar p.toReal • Jmat) ∧
    Kstar p.toReal - Jmat * Kstar p.toReal * Jmat = Jmat - Dstar p.toReal • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
  ⟨Matsaev.Gamma.hasDerivAt_Teps_entry _, Matsaev.Gamma.hasDerivAt_Teps_sq_entry _, Matsaev.Gamma.kstar_JJ _,
    Matsaev.Gamma.hasDerivAt_norm_PaTeps p (Matsaev.Assembly.one_lt_toReal hp hptop) hptop a B,
    Matsaev.Gamma.Jmat_mul_self, Matsaev.Gamma.kstar_mul_J _, Matsaev.Gamma.kstar_sub_JKJ _⟩

/-- **Proof of Lemma 4.1** (`lem:TK`), the values at `ξ_0 = (1, t)`, `t = t_*` (pinned as the unique critical point of
`f` in `(0, 1)`, Lemma 3.4), `D = D_*`: `‖ξ_0‖_p^p = 1 + t^p`, `⟨φ(ξ_0), Jξ_0⟩ = D(1 + t^p)`,
`E_* := ⟨|ξ_0|^(p-2) Jξ_0, (J - D I)ξ_0⟩ = t² + t^(p-2) - D(t - t^(p-1)) = t^(p-2)(1+t²)²/(1+t^p)`, the identity
`(s² + s^(p-2))(1 + s^p) - (s - s^(p-1))² = s^(p-2)(1 + s²)²` (every `s ≥ 0`), and with `eq:ST`
`(1+t^p)²(1+D²) = (1+t^p)² + (t - t^(p-1))² = (1+t²)(1+t^(2p-2)) = (p-1)t^(p-2)(1+t²)²`, i.e. `(1+t^p)(1+D²) = (p-1)E_*`. -/
theorem lemma_4_1_values (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hcrit : deriv (dfun p.toReal) t = 0) :
    ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ ^ p.toReal = 1 + t ^ p.toReal ∧
    ∑ i, phi p.toReal ((![1, t] : Fin 2 → ℝ) i) * ((Jmat : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, t]) i =
      Dstar p.toReal * (1 + t ^ p.toReal) ∧
    ∑ i, |(![1, t] : Fin 2 → ℝ) i| ^ (p.toReal - 2) * ((Jmat : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, t]) i *
        ((Jmat - Dstar p.toReal • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ![1, t]) i =
      t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1)) ∧
    t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1)) =
      t ^ (p.toReal - 2) * (1 + t ^ 2) ^ 2 / (1 + t ^ p.toReal) ∧
    (∀ s : ℝ, 0 ≤ s → (s ^ 2 + s ^ (p.toReal - 2)) * (1 + s ^ p.toReal) - (s - s ^ (p.toReal - 1)) ^ 2 =
      s ^ (p.toReal - 2) * (1 + s ^ 2) ^ 2) ∧
    (1 + t ^ p.toReal) ^ 2 * (1 + Dstar p.toReal ^ 2) = (1 + t ^ p.toReal) ^ 2 + (t - t ^ (p.toReal - 1)) ^ 2 ∧
    (1 + t ^ p.toReal) ^ 2 + (t - t ^ (p.toReal - 1)) ^ 2 = (1 + t ^ 2) * (1 + t ^ (2 * p.toReal - 2)) ∧
    (1 + t ^ 2) * (1 + t ^ (2 * p.toReal - 2)) = (p.toReal - 1) * t ^ (p.toReal - 2) * (1 + t ^ 2) ^ 2 ∧
    (1 + t ^ p.toReal) * (1 + Dstar p.toReal ^ 2) =
      (p.toReal - 1) * (t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1))) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  have hq1 : 1 < p.toReal := by linarith
  obtain ⟨h1, h2, h3⟩ := Matsaev.Gamma.ST_chain hq2 ht hcrit
  have hphi1 : phi p.toReal 1 = 1 := by simp [phi]
  have hphit : phi p.toReal t = t ^ (p.toReal - 1) := Matsaev.B0.phi_of_nonneg hq1 ht.1.le
  obtain ⟨hx1, -, -⟩ := Matsaev.Gamma.rpow_facts (q := p.toReal) ht.1
  refine ⟨?_, ?_, ?_, Matsaev.Gamma.E_eq hq2 ht hcrit, fun s hs => Matsaev.Gamma.E_identity hq2 hs, h1, h2, h3,
    Matsaev.Gamma.NE_identity hq2 ht hcrit⟩
  · rw [norm_toLp_fin2_rpow p hptop, abs_one, Real.one_rpow, abs_of_pos ht.1]
  · rw [Matsaev.Gamma.J_mulVec, Fin.sum_univ_two, Matsaev.Gamma.Dstar_mul hq2 ht hcrit]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hphi1, hphit]
    ring
  · rw [Matsaev.Gamma.J_mulVec, Matsaev.Gamma.JD_mulVec, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_one, Real.one_rpow, abs_of_pos ht.1, hx1]
    ring

/-- **Proof of Lemma 4.1** (`lem:TK`), `Γ(0) = 0` and the maximum of `g`: with `ξ_0 = (1, t)`, `t = t_*`, `D = D_*`,
`p > 2`, `B > 0`: `y_0 = P_0(J)ξ_0 = (1+B)ξ_0` and `Γ(0) = ⟨φ(y_0), M_0 ξ_0⟩ = (1+B)^(p-1) B ‖ξ_0‖_p^p (Q(ξ_0) - D) = 0`;
`g(ξ) := ⟨φ(ξ), (J - D I)ξ⟩ = ‖ξ‖_p^p (Q(ξ) - D)` for `ξ ≠ 0`, `g ≤ 0` everywhere, and the derivative of `g` at its
maximum `ξ_0` vanishes in every direction `ψ`. -/
theorem lemma_4_1_gamma_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hcrit : deriv (dfun p.toReal) t = 0) :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B) *ᵥ ![1, t] = (1 + B) • ![1, t] ∧
    ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B) *ᵥ ![1, t]) i) *
        (((0 : ℝ) • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ![1, t]) i =
      (1 + B) ^ (p.toReal - 1) * B * ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ ^ p.toReal *
        (Qf p.toReal 1 t - Dstar p.toReal) ∧
    ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa 0 B) *ᵥ ![1, t]) i) *
        (((0 : ℝ) • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ![1, t]) i = 0 ∧
    (∀ ξ : Fin 2 → ℝ, ξ ≠ 0 →
      ∑ i, phi p.toReal (ξ i) * ((Jmat - Dstar p.toReal • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ξ) i =
        ‖WithLp.toLp p ξ‖ ^ p.toReal * (Qf p.toReal (ξ 0) (ξ 1) - Dstar p.toReal)) ∧
    (∀ ξ : Fin 2 → ℝ, ∑ i, phi p.toReal (ξ i) * ((Jmat - Dstar p.toReal • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ξ) i ≤ 0) ∧
    (∀ ψ : Fin 2 → ℝ, HasDerivAt (fun h : ℝ => ∑ i, phi p.toReal ((![1, t] + h • ψ) i) *
      ((Jmat - Dstar p.toReal • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ (![1, t] + h • ψ)) i) 0 0) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  have hq1 : 1 < p.toReal := by linarith
  obtain ⟨hy, hg⟩ := Matsaev.Gamma.gam_zero hq1 (by linarith : 0 < 1 + B) ht.1
  have hn : ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ ^ p.toReal = 1 + t ^ p.toReal := by
    rw [norm_toLp_fin2_rpow p hptop, abs_one, Real.one_rpow, abs_of_pos ht.1]
  have hg' : Matsaev.Gamma.gam p.toReal 0 B ![1, t] =
      (1 + B) ^ (p.toReal - 1) * B * ‖WithLp.toLp p (![1, t] : Fin 2 → ℝ)‖ ^ p.toReal *
        (Qf p.toReal 1 t - Dstar p.toReal) := by rw [hn]; exact hg
  refine ⟨hy, hg', ?_, fun ξ hξ => ?_, Matsaev.Gamma.gfun_le hq2, Matsaev.Gamma.gfun_dir_deriv hq2 ht hcrit⟩
  · show Matsaev.Gamma.gam p.toReal 0 B ![1, t] = 0
    rw [hg', Matsaev.Gamma.Qf_one_pos ht.1, ← (Matsaev.Gamma.tstar_facts hq2 ht hcrit).1, sub_self, mul_zero]
  · obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
    have hne : (u, v) ≠ (0, 0) := fun h => hξ (by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      ext i
      fin_cases i <;> rfl)
    show Matsaev.Gamma.gfun p.toReal ![u, v] = _
    rw [Matsaev.Gamma.gfun_eq (by linarith) u v (Matsaev.Gamma.normq_pos hne).ne', norm_toLp_fin2_rpow p hptop]
    rfl

/-- **Proof of Lemma 4.1** (`lem:TK`), `Γ′(0)`: for `p > 2`, `B > 0`, `t = t_*`, `D = D_*`, `E_* = t² + t^(p-2) - D(t - t^(p-1))`
and ANY test vectors `ξ_a` with `(ξ_a)₁ = 1`, `ξ_0 = (1, t)` and `ξ_a = ξ_0 + aξ̇ + o(a)` as `a → 0+` (the paper's
`ξ_a = s_a/(s_a)₁` is such a family by Lemma 3.5 (i), (iv), `lemma_3_5_full`): `d/da y_a |₀ = (1+B)ξ̇ + Jξ_0` for
`y_a = P_a(J)ξ_a`; `Γ(a) = ⟨φ(y_a), M_a ξ_a⟩` has, from the right at `0`, the derivative
`Γ′(0) = (1+B)^(p-2)[-½(1+B)(1+t^p)(1+D²) + (p-1)B E_*] = (1+B)^(p-2)(p-1)E_*(B-1)/2` (the `ξ̇` terms cancel), so
`Γ(a) = a(1+B)^(p-2)(p-1)E_*(B-1)/2 + o(a)` with `E_* > 0`; for `B > 1`, `Γ(a) > 0` for `0 < a < a₂`. (At `B = 1` the
first-order term is `0`.) With `lemma_4_1_eps_deriv` this gives the outline's "a positive multiple of `εa(B-1)`" to
leading order FOR THE TEST VECTOR `ξ_a`: `d/dε ‖P_a(T_ε)ξ_a‖_p^p |₀ = pΓ(a)`. It is not stated for the operator norm
`‖P_a(T_ε)‖_p` itself; `lemma_4_1` proves the strict inequality of norms. -/
theorem lemma_4_1_gamma (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hcrit : deriv (dfun p.toReal) t = 0) (ξ : ℝ → Fin 2 → ℝ) (ξ' : Fin 2 → ℝ)
    (hξ1 : ∀ a, ξ a 0 = 1) (hξ0 : ξ 0 = ![1, t]) (hξ : HasDerivWithinAt ξ ξ' (Set.Ici 0) 0) :
    HasDerivWithinAt (fun a => aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a)
      ((1 + B) • ξ' + (Jmat : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ξ 0) (Set.Ici 0) 0 ∧
    HasDerivWithinAt (fun a => ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a) i) *
        ((a • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ξ a) i)
      ((1 + B) ^ (p.toReal - 2) * (-(1 / 2) * (1 + B) * (1 + t ^ p.toReal) * (1 + Dstar p.toReal ^ 2) +
        (p.toReal - 1) * B * (t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1)))))
      (Set.Ici 0) 0 ∧
    (1 + B) ^ (p.toReal - 2) * (-(1 / 2) * (1 + B) * (1 + t ^ p.toReal) * (1 + Dstar p.toReal ^ 2) +
        (p.toReal - 1) * B * (t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1)))) =
      (1 + B) ^ (p.toReal - 2) * (p.toReal - 1) *
        (t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1))) * (B - 1) / 2 ∧
    0 < t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1)) ∧
    Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ici 0))
      (fun a => ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a) i) *
          ((a • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ξ a) i -
        a * ((1 + B) ^ (p.toReal - 2) * (p.toReal - 1) *
          (t ^ 2 + t ^ (p.toReal - 2) - Dstar p.toReal * (t - t ^ (p.toReal - 1))) * (B - 1) / 2))
      (fun a => a) ∧
    (1 < B → ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ a : ℝ, 0 < a → a < a₂ →
      0 < ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a) i) *
        ((a • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ξ a) i) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  have hq1 : 1 < p.toReal := by linarith
  have hB1 : 0 < 1 + B := by linarith
  have hd := Matsaev.Gamma.gamma_curve hq2 ht hcrit hB1 hξ1 hξ0 hξ
  have heq := Matsaev.Gamma.gamma_deriv_eq hq2 ht hcrit B
  have hE := Matsaev.Gamma.E_pos hq2 ht hcrit
  have h0 : Matsaev.Gamma.gam p.toReal 0 B (ξ 0) = 0 := by
    rw [hξ0, (Matsaev.Gamma.gam_zero hq1 hB1 ht.1).2, Matsaev.Gamma.Qf_one_pos ht.1,
      ← (Matsaev.Gamma.tstar_facts hq2 ht hcrit).1, sub_self, mul_zero]
  have hd' := hd.congr_deriv heq
  refine ⟨Matsaev.Gamma.hasDerivWithinAt_y B hξ, hd, heq, hE,
    Matsaev.Gamma.isLittleO_of_hasDerivWithinAt hd' h0, fun hB' => ?_⟩
  have hc := Real.rpow_pos_of_pos hB1 (p.toReal - 2)
  exact Matsaev.Gamma.exists_pos_of_hasDerivWithinAt hd' h0 (by
    have : 0 < p.toReal - 1 := by linarith
    have : 0 < B - 1 := by linarith
    positivity)

/-- **Lemma 4.1** (`lem:TK`), its inequality by the PAPER'S OWN ROUTE (proof of Lemma 4.1, "Choice of test vector" to
the end): with `s_a = e(θ_a)` from Lemma 3.5 (i), (iv) (`lemma_3_5_full`), `ξ_a = s_a/(s_a)₁` attains `‖P_a(J)‖_p`, and
`Γ(a) > 0` for small `a > 0` (`lemma_4_1_gamma`, `B > 1`), so `d/dε ‖P_a(T_ε)ξ_a‖_p^p |₀ = pΓ(a) > 0`
(`lemma_4_1_eps_deriv`) and, for all small `ε > 0`,
`‖P_a(T_ε)‖_p ≥ ‖P_a(T_ε)ξ_a‖_p/‖ξ_a‖_p > ‖P_a(J)ξ_a‖_p/‖ξ_a‖_p = ‖P_a(J)‖_p`. The same conclusion as the second half of
`lemma_4_1`, whose Lean proof uses another route (`TK.gamma_identity`). -/
theorem lemma_4_1_paper_route (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 1 < B) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ a : ℝ, 0 < a → a < a₂ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) < matNorm p (aeval (Teps p.toReal ε) (Pa a B)) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  obtain ⟨t, ht, hcrit, ρ, a₁, δ, η, -, hρt, ha₁, -, -, θf, H, hθ0, hanal, -⟩ :=
    lemma_3_5_full p hp hptop B (by linarith)
  have htc : deriv (dfun p.toReal) t = 0 := (hcrit t ht).mpr rfl
  have hsq : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hc0 : Real.cos (θf 0) = (Real.sqrt (1 + t ^ 2))⁻¹ := by simpa using congrFun hθ0 0
  have hs0 : Real.sin (θf 0) = (Real.sqrt (1 + t ^ 2))⁻¹ * t := by simpa using congrFun hθ0 1
  have hc0ne : (![Real.cos (θf 0), Real.sin (θf 0)] : Fin 2 → ℝ) 0 ≠ 0 := by
    simp only [Matrix.cons_val_zero, hc0]
    exact (inv_pos.mpr hsq).ne'
  obtain ⟨ξ', hξ'⟩ := Matsaev.Gamma.curve_hasDerivWithinAt ha₁ hanal hc0ne
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hξ'
  -- the paper's test vectors `ξ_a = s_a/(s_a)₁ = (1, sin θ_a / cos θ_a)`
  have hξ0 : (![1, Real.sin (θf 0) / Real.cos (θf 0)] : Fin 2 → ℝ) = ![1, t] := by
    rw [hc0, hs0, mul_div_cancel_left₀ t (inv_pos.mpr hsq).ne']
  obtain ⟨-, -, -, -, -, hpos⟩ := lemma_4_1_gamma p hp hptop B (by linarith) t ht htc
    (fun a => (![1, Real.sin (θf a) / Real.cos (θf a)] : Fin 2 → ℝ)) ξ' (fun a => rfl) hξ0 hξ'
  obtain ⟨a₂, ha₂, hΓ⟩ := hpos hB
  refine ⟨min a₁ a₂, lt_min ha₁ ha₂, fun a ha haa => ?_⟩
  obtain ⟨hzero, hnorm, hclose, -, -⟩ := H a ha (lt_of_lt_of_le haa (min_le_left _ _))
  have hmax := (hnorm (θf a)).mp ((hzero (θf a)).mpr ⟨0, by simp⟩)
  -- `θ_a` is within `ρ/2 < arctan t_*/4` of `arctan t_* ∈ (0, π/4)`, so `cos θ_a > 0`
  have hat0 : 0 < Real.arctan t := Real.arctan_pos.mpr ht.1
  have hat1 : Real.arctan t < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono ht.2
  have hcos : 0 < Real.cos (θf a) := by
    obtain ⟨h1, h2⟩ := abs_le.mp hclose
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hξa : (![1, Real.sin (θf a) / Real.cos (θf a)] : Fin 2 → ℝ) =
      (Real.cos (θf a))⁻¹ • ![Real.cos (θf a), Real.sin (θf a)] := by
    ext i
    fin_cases i
    · simp [inv_mul_cancel₀ hcos.ne']
    · simp [div_eq_inv_mul]
  refine Matsaev.Gamma.gain_of_gam_pos p (by linarith) hptop a B (![1, Real.sin (θf a) / Real.cos (θf a)]) ?_ ?_
    (hΓ a ha (lt_of_lt_of_le haa (min_le_right _ _)))
  · intro h
    have h0 := congrFun h 0
    simp at h0
  · rw [hξa]
    exact Matsaev.Gamma.attain_smul p _ _ _ _ hmax

/-- **Idea of the proof of Theorem A** (v1.90 display) and **proof of Lemma 4.1**: "Let `ξ_a` be a real vector at which
`‖P_a(J)ξ‖_p/‖ξ‖_p` is maximal, normalised by `(ξ_a)₁ = 1` and close to `(1, t_*)` (such a vector exists by Lemma 3.5). The
derivative in `ε` at `ε = 0` of `‖P_a(T_ε)ξ_a‖_p^p` is `½p(p-1)(1+B)^(p-2)E_* a(B-1) + o(a)` (`a → 0`),
`E_* = t_*^(p-2)(1+t_*²)²/(1+t_*^p) > 0`". For `p > 2`, `B > 1`: `t_*` is the unique critical point of `f` in `(0, 1)`;
`ξ_a = s_a/(s_a)₁` (`s_a = e(θ_a)` from Lemma 3.5 (i), (iv), `lemma_3_5_full`) has `(ξ_a)₁ = 1`, `ξ_0 = (1, t_*)`, `ξ_a → ξ_0`
as `a → 0⁺`; for `0 < a < a₂` it attains `‖P_a(J)‖_p` and the `ε`-derivative is the displayed sum; minus the display it is
`o(a)` (`E_* > 0` is `idea_E_closed_form`). Review r6, M1 (the reviewer's statement). -/
theorem lemma_4_1_gain_maximising (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 1 < B) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, (∀ s ∈ Set.Ioo (0 : ℝ) 1, deriv (dfun p.toReal) s = 0 ↔ s = t) ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∃ ξ : ℝ → Fin 2 → ℝ, ξ 0 = ![1, t] ∧ (∀ a, ξ a 0 = 1) ∧
      ContinuousWithinAt ξ (Set.Ici 0) 0 ∧
      (∀ a : ℝ, 0 < a → a < a₂ →
        ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a)‖ =
          matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) * ‖WithLp.toLp p (ξ a)‖ ∧
        HasDerivAt (fun ε => ‖WithLp.toLp p (aeval (Teps p.toReal ε) (Pa a B) *ᵥ ξ a)‖ ^ p.toReal)
          (p.toReal * ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a) i) *
            ((a • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ξ a) i) 0) ∧
      Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ici 0))
        (fun a => p.toReal * ∑ i, phi p.toReal ((aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ a) i) *
            ((a • (Kstar p.toReal * Jmat) + B • (Kstar p.toReal - Jmat * Kstar p.toReal * Jmat)) *ᵥ ξ a) i -
          1 / 2 * p.toReal * (p.toReal - 1) * (1 + B) ^ (p.toReal - 2) *
            (t ^ (p.toReal - 2) * (1 + t ^ 2) ^ 2 / (1 + t ^ p.toReal)) * a * (B - 1))
        (fun a => a) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  obtain ⟨t, ht, hcrit, ρ, a₁, δ, η, -, hρt, ha₁, -, -, θf, H, hθ0, hanal, -⟩ :=
    lemma_3_5_full p hp hptop B (by linarith)
  have htc : deriv (dfun p.toReal) t = 0 := (hcrit t ht).mpr rfl
  have hsq : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hc0 : Real.cos (θf 0) = (Real.sqrt (1 + t ^ 2))⁻¹ := by simpa using congrFun hθ0 0
  have hs0 : Real.sin (θf 0) = (Real.sqrt (1 + t ^ 2))⁻¹ * t := by simpa using congrFun hθ0 1
  have hc0ne : (![Real.cos (θf 0), Real.sin (θf 0)] : Fin 2 → ℝ) 0 ≠ 0 := by
    simp only [Matrix.cons_val_zero, hc0]
    exact (inv_pos.mpr hsq).ne'
  obtain ⟨ξ', hξ'⟩ := Matsaev.Gamma.curve_hasDerivWithinAt ha₁ hanal hc0ne
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hξ'
  have hξ0 : (![1, Real.sin (θf 0) / Real.cos (θf 0)] : Fin 2 → ℝ) = ![1, t] := by
    rw [hc0, hs0, mul_div_cancel_left₀ t (inv_pos.mpr hsq).ne']
  obtain ⟨-, -, -, -, hlo, -⟩ := lemma_4_1_gamma p hp hptop B (by linarith) t ht htc
    (fun a => (![1, Real.sin (θf a) / Real.cos (θf a)] : Fin 2 → ℝ)) ξ' (fun a => rfl) hξ0 hξ'
  have hE' := Matsaev.Gamma.E_eq hq2 ht htc
  refine ⟨t, ht, hcrit, a₁, ha₁, fun a => ![1, Real.sin (θf a) / Real.cos (θf a)], hξ0, fun a => rfl,
    hξ'.continuousWithinAt, fun a ha haa => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨hzero, hnorm, hclose, -, -⟩ := H a ha haa
    have hmax := (hnorm (θf a)).mp ((hzero (θf a)).mpr ⟨0, by simp⟩)
    have hat0 : 0 < Real.arctan t := Real.arctan_pos.mpr ht.1
    have hat1 : Real.arctan t < Real.pi / 4 := by
      rw [← Real.arctan_one]
      exact Real.arctan_strictMono ht.2
    have hcos : 0 < Real.cos (θf a) := by
      obtain ⟨h1, h2⟩ := abs_le.mp hclose
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have hξa : (![1, Real.sin (θf a) / Real.cos (θf a)] : Fin 2 → ℝ) =
        (Real.cos (θf a))⁻¹ • ![Real.cos (θf a), Real.sin (θf a)] := by
      ext i
      fin_cases i
      · simp [inv_mul_cancel₀ hcos.ne']
      · simp [div_eq_inv_mul]
    beta_reduce
    rw [hξa]
    exact Matsaev.Gamma.attain_smul p _ _ _ _ hmax
  · exact (lemma_4_1_eps_deriv p (ENNReal.one_lt_two.trans hp) hptop a B).2.2.2.1 _
  · refine (hlo.const_mul_left p.toReal).congr_left fun a => ?_
    rw [← hE']
    ring

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.80): "`d/dy |y|^p = p φ(y)`" for `p > 1`. -/
theorem idea_abs_rpow_deriv (p : ℝ) (hp : 1 < p) (y : ℝ) :
    HasDerivAt (fun y : ℝ => |y| ^ p) (p * phi p y) y :=
  Matsaev.Angle.hasDerivAt_absRpow hp y

/-- **Section 3, the function `Q`** (added in v1.80; also the Idea): `⟨φ(ξ), Jξ⟩ = φ(ξ₁)ξ₂ - φ(ξ₂)ξ₁ = Q(ξ)‖ξ‖_p^p`
for every real `ξ` (both sides are `0` at `ξ = 0`); this is the term of first order in `h` of `‖ξ + hJξ‖_p^p`, divided by
`hp`. -/
theorem sec3_first_order_term (p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ⊤) (ξ : Fin 2 → ℝ) :
    ∑ i, phi p.toReal (ξ i) * (Jmat *ᵥ ξ) i = phi p.toReal (ξ 0) * ξ 1 - phi p.toReal (ξ 1) * ξ 0 ∧
      phi p.toReal (ξ 0) * ξ 1 - phi p.toReal (ξ 1) * ξ 0 =
        Qf p.toReal (ξ 0) (ξ 1) * ‖WithLp.toLp p ξ‖ ^ p.toReal := by
  have hξ : ξ = ![ξ 0, ξ 1] := by
    ext i
    fin_cases i <;> rfl
  refine ⟨?_, ?_⟩
  · rw [Fin.sum_univ_two]
    simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · rw [hξ, norm_toLp_fin2_rpow p hptop]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    unfold Qf
    by_cases h0 : |ξ 0| ^ p.toReal + |ξ 1| ^ p.toReal = 0
    · have hr : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hptop
      have h1 : |ξ 0| ^ p.toReal = 0 := by
        have := Real.rpow_nonneg (abs_nonneg (ξ 0)) p.toReal
        have := Real.rpow_nonneg (abs_nonneg (ξ 1)) p.toReal
        linarith
      have h2 : |ξ 1| ^ p.toReal = 0 := by
        have := Real.rpow_nonneg (abs_nonneg (ξ 0)) p.toReal
        linarith
      have e0 : ξ 0 = 0 := by
        rcases (Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _)).mp h1 with ⟨h, -⟩
        exact abs_eq_zero.mp h
      have e1 : ξ 1 = 0 := by
        rcases (Real.rpow_eq_zero_iff_of_nonneg (abs_nonneg _)).mp h2 with ⟨h, -⟩
        exact abs_eq_zero.mp h
      simp [e0, e1]
    · rw [div_mul_cancel₀ _ h0]

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.80), for `2 < p < ∞` and real `ξ`:
"`d/dε ‖R_{ε/2}ξ‖_p^p |_{ε=0} = (p/2)(φ(ξ₁)ξ₂ - φ(ξ₂)ξ₁) = (p/2) Q(ξ)‖ξ‖_p^p`"; "`R_{(ε+h)/2} = R_{h/2}R_{ε/2}`"; and
"`‖R_{ε/2}ξ‖_p ≤ e^{εD_*/2}‖ξ‖_p` for `ε ≥ 0`" (here from `‖T_ε‖_p ≤ 1`, Lemma 4.1, as `J` is an isometry; the paper's
route, the bound at every `ε` and integration, is `idea_log_rate`). -/
theorem idea_rotation_pth_power (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) :
    (∀ ξ : Fin 2 → ℝ, HasDerivAt (fun ε : ℝ => ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖ ^ p.toReal)
        (p.toReal / 2 * (phi p.toReal (ξ 0) * ξ 1 - phi p.toReal (ξ 1) * ξ 0)) 0 ∧
      p.toReal / 2 * (phi p.toReal (ξ 0) * ξ 1 - phi p.toReal (ξ 1) * ξ 0) =
        p.toReal / 2 * Qf p.toReal (ξ 0) (ξ 1) * ‖WithLp.toLp p ξ‖ ^ p.toReal) ∧
    (∀ ε h : ℝ, Rot ((ε + h) / 2) = Rot (h / 2) * Rot (ε / 2)) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Fin 2 → ℝ,
      ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖ ≤ Real.exp (ε * Dstar p.toReal / 2) * ‖WithLp.toLp p ξ‖) := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  have hq0 : 0 < p.toReal := by linarith
  refine ⟨fun ξ => ⟨?_, ?_⟩, fun ε h => ?_, fun ε hε ξ => ?_⟩
  · obtain ⟨u, v, rfl⟩ : ∃ u v : ℝ, ξ = ![u, v] := ⟨ξ 0, ξ 1, by ext i; fin_cases i <;> rfl⟩
    have hd := Matsaev.Cov130.hasDerivAt_rot_rpow (q := p.toReal) (by linarith) u v
    have hfun : (fun ε : ℝ => ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ![u, v])‖ ^ p.toReal) =
        fun ε => |Gamma.ex1 0 u v ε| ^ p.toReal + |Gamma.ex2 0 u v ε| ^ p.toReal := by
      funext ε
      rw [Matsaev.Cov130.rot_mulVec, norm_toLp_fin2_rpow p hptop]
    rw [hfun]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact hd.congr_deriv (by ring)
  · rw [(sec3_first_order_term p hptop ξ).2]
    ring
  · rw [show (ε + h) / 2 = h / 2 + ε / 2 by ring]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Rot, Jmat, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring
  · -- `‖T_ε‖ ≤ 1` at `η = -Jξ`, where `Jη = ξ` and `‖η‖ = ‖ξ‖`
    have hT := ((lemma_4_1 p hp hptop 2 (by norm_num)).1 ε hε).1
    set η : Fin 2 → ℝ := -(Jmat *ᵥ ξ) with hη
    have hJη : Jmat *ᵥ η = ξ := by
      rw [hη, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Jmat_mul_Jmat, Matrix.neg_mulVec, neg_neg,
        Matrix.one_mulVec]
    have hnorm : ‖WithLp.toLp p η‖ = ‖WithLp.toLp p ξ‖ := by
      have hpow : ‖WithLp.toLp p η‖ ^ p.toReal = ‖WithLp.toLp p ξ‖ ^ p.toReal := by
        have e1 : η = ![-ξ 1, ξ 0] := by
          ext i
          fin_cases i <;> simp [hη, Jmat, dotProduct, Fin.sum_univ_two]
        have e2 : ξ = ![ξ 0, ξ 1] := by
          ext i
          fin_cases i <;> rfl
        rw [e1, norm_toLp_fin2_rpow p hptop, e2, norm_toLp_fin2_rpow p hptop]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, abs_neg]
        ring
      rw [← Real.rpow_rpow_inv (norm_nonneg (WithLp.toLp p η)) hq0.ne', hpow,
        Real.rpow_rpow_inv (norm_nonneg _) hq0.ne']
    have hv := norm_mulVec_le_matNorm p (Teps p.toReal ε) η
    have hTη : Teps p.toReal ε *ᵥ η = Real.exp (-(ε * Dstar p.toReal / 2)) • (Rot (ε / 2) *ᵥ ξ) := by
      rw [Teps, ← Matrix.mulVec_mulVec, hJη, Matrix.smul_mulVec]
    rw [hTη, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hnorm] at hv
    have hle : Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖ ≤ ‖WithLp.toLp p ξ‖ :=
      hv.trans (mul_le_of_le_one_left (norm_nonneg _) hT)
    have hexp : Real.exp (ε * Dstar p.toReal / 2) * Real.exp (-(ε * Dstar p.toReal / 2)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖
        = Real.exp (ε * Dstar p.toReal / 2) *
            (Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖) := by
          rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp (ε * Dstar p.toReal / 2) * ‖WithLp.toLp p ξ‖ :=
          mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.90), for `2 < p < ∞` and real `ξ ≠ 0`: "As
`R_{(ε+h)/2} = R_{h/2}R_{ε/2}`, the same bound holds at every `ε`, with `ξ` replaced by `R_{ε/2}ξ`. Thus
`d/dε log ‖R_{ε/2}ξ‖_p ≤ D_*/2`" (at every `ε` the derivative is `Q(R_{ε/2}ξ)/2`), "and integration from `0` to `ε` gives
`‖R_{ε/2}ξ‖_p ≤ e^{εD_*/2}‖ξ‖_p` for `ε ≥ 0`" (proved by this route: `log ‖R_{ε/2}ξ‖_p - εD_*/2` has derivative `≤ 0`, so it
is antitone; review r6 M3). -/
theorem idea_log_rate (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (ξ : Fin 2 → ℝ) (hξ : ξ ≠ 0) :
    (∀ ε : ℝ, HasDerivAt (fun e : ℝ => Real.log ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖)
        (Qf p.toReal ((Rot (ε / 2) *ᵥ ξ) 0) ((Rot (ε / 2) *ᵥ ξ) 1) / 2) ε ∧
      Qf p.toReal ((Rot (ε / 2) *ᵥ ξ) 0) ((Rot (ε / 2) *ᵥ ξ) 1) / 2 ≤ Dstar p.toReal / 2) ∧
    ∀ ε : ℝ, 0 ≤ ε →
      ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖ ≤ Real.exp (ε * Dstar p.toReal / 2) * ‖WithLp.toLp p ξ‖ := by
  have hq2 := Matsaev.Assembly.two_lt_toReal hp hptop
  have hq0 : 0 < p.toReal := by linarith
  obtain ⟨hderiv0, hgroup, -⟩ := idea_rotation_pth_power p hp hptop
  obtain ⟨t, -, -, -, htpos, hle, hD, -, -⟩ := lemma_3_4 p.toReal hq2
  have hrot0 : Rot 0 = 1 := by simp [Rot]
  -- rotations are invertible, so `R_{e/2} ξ ≠ 0`
  have hne : ∀ e : ℝ, Rot (e / 2) *ᵥ ξ ≠ 0 := by
    intro e h0
    apply hξ
    have hinv : Rot ((e + -e) / 2) = Rot (-e / 2) * Rot (e / 2) := hgroup e (-e)
    rw [add_neg_cancel, zero_div, hrot0] at hinv
    calc ξ = (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ξ := (Matrix.one_mulVec ξ).symm
      _ = Rot (-e / 2) *ᵥ (Rot (e / 2) *ᵥ ξ) := by rw [hinv, Matrix.mulVec_mulVec]
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  have hpos : ∀ e : ℝ, 0 < ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖ := by
    intro e
    rw [norm_pos_iff]
    intro h
    apply hne e
    simpa using congrArg WithLp.ofLp h
  have hQ : ∀ η : Fin 2 → ℝ, Qf p.toReal (η 0) (η 1) ≤ Dstar p.toReal := by
    intro η
    by_cases h : (η 0, η 1) = (0, 0)
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2, hD]
      simp [Qf, htpos.le]
    · rw [hD]
      exact hle _ _ h
  have hlogderiv : ∀ ε : ℝ, HasDerivAt (fun e : ℝ => Real.log ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖)
      (Qf p.toReal ((Rot (ε / 2) *ᵥ ξ) 0) ((Rot (ε / 2) *ᵥ ξ) 1) / 2) ε := by
    intro ε
    set η := Rot (ε / 2) *ᵥ ξ with hη
    obtain ⟨hd, hdq⟩ := hderiv0 η
    rw [hdq] at hd
    -- move the base point from `0` to `ε`
    have hshift : (fun e : ℝ => ‖WithLp.toLp p (Rot ((e - ε) / 2) *ᵥ η)‖ ^ p.toReal) =
        fun e => ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖ ^ p.toReal := by
      funext e
      rw [hη, Matrix.mulVec_mulVec, ← hgroup ε (e - ε), add_sub_cancel]
    have h1 : HasDerivAt (fun s : ℝ => ‖WithLp.toLp p (Rot (s / 2) *ᵥ η)‖ ^ p.toReal)
        (p.toReal / 2 * Qf p.toReal (η 0) (η 1) * ‖WithLp.toLp p η‖ ^ p.toReal) (ε - ε) := by
      rwa [sub_self]
    have hd' := HasDerivAt.comp_sub_const ε ε h1
    rw [hshift] at hd'
    have hfpos : 0 < ‖WithLp.toLp p η‖ ^ p.toReal := Real.rpow_pos_of_pos (hpos ε) _
    have hlog := (hd'.log hfpos.ne').div_const p.toReal
    have hfun : (fun e : ℝ => Real.log ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖) =
        fun e => Real.log (‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖ ^ p.toReal) / p.toReal := by
      funext e
      rw [Real.log_rpow (hpos e), mul_div_cancel_left₀ _ hq0.ne']
    rw [hfun]
    convert hlog using 1
    rw [← hη]
    field_simp
  refine ⟨fun ε => ⟨hlogderiv ε, by linarith [hQ (Rot (ε / 2) *ᵥ ξ)]⟩, fun ε hε => ?_⟩
  set D := Dstar p.toReal with hDdef
  have hg : ∀ e : ℝ, HasDerivAt (fun e : ℝ => Real.log ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖ - e * (D / 2))
      (Qf p.toReal ((Rot (e / 2) *ᵥ ξ) 0) ((Rot (e / 2) *ᵥ ξ) 1) / 2 - 1 * (D / 2)) e :=
    fun e => (hlogderiv e).sub ((hasDerivAt_id' e).mul_const (D / 2))
  have hanti : Antitone (fun e : ℝ => Real.log ‖WithLp.toLp p (Rot (e / 2) *ᵥ ξ)‖ - e * (D / 2)) :=
    antitone_of_deriv_nonpos (fun e => (hg e).differentiableAt) (fun e => by
      rw [(hg e).deriv]
      linarith [hQ (Rot (e / 2) *ᵥ ξ)])
  have h0 := hanti hε
  simp only [zero_div, hrot0, Matrix.one_mulVec, zero_mul, sub_zero] at h0
  have hξpos : 0 < ‖WithLp.toLp p ξ‖ := by simpa [hrot0] using hpos 0
  calc ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖ = Real.exp (Real.log ‖WithLp.toLp p (Rot (ε / 2) *ᵥ ξ)‖) :=
        (Real.exp_log (hpos ε)).symm
    _ ≤ Real.exp (ε * D / 2 + Real.log ‖WithLp.toLp p ξ‖) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (ε * D / 2) * ‖WithLp.toLp p ξ‖ := by rw [Real.exp_add, Real.exp_log hξpos]

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.90), `2 < p < ∞`, real `ξ`: "As `J` is an isometry of `ℓ^p_2`
(it permutes the coordinates up to sign), `‖T_εξ‖_p = e^{-εD_*/2}‖R_{ε/2}Jξ‖_p ≤ ‖Jξ‖_p = ‖ξ‖_p`" (`ε ≥ 0`); "so `T_ε` is a
contraction on real vectors, and hence, by Lemma 2.1, on `ℓ^p_2`" (real and complex). Proved by this route, from
`idea_log_rate` (not from `lemma_4_1`). -/
theorem idea_J_isometry_contraction (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) :
    (∀ ξ : Fin 2 → ℝ, Jmat *ᵥ ξ = ![ξ 1, -ξ 0] ∧ ‖WithLp.toLp p (Jmat *ᵥ ξ)‖ = ‖WithLp.toLp p ξ‖) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Fin 2 → ℝ,
      ‖WithLp.toLp p (Teps p.toReal ε *ᵥ ξ)‖ =
          Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ (Jmat *ᵥ ξ))‖ ∧
        Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ (Jmat *ᵥ ξ))‖ ≤
          ‖WithLp.toLp p (Jmat *ᵥ ξ)‖) ∧
    ∀ ε : ℝ, 0 ≤ ε →
      matNorm p (Teps p.toReal ε) ≤ 1 ∧ matNorm p ((Teps p.toReal ε).map (algebraMap ℝ ℂ)) ≤ 1 := by
  have hq0 : 0 < p.toReal := by have := Matsaev.Assembly.two_lt_toReal hp hptop; linarith
  have hJ : ∀ ξ : Fin 2 → ℝ, Jmat *ᵥ ξ = ![ξ 1, -ξ 0] := fun ξ => by
    ext i
    fin_cases i <;> simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hiso : ∀ ξ : Fin 2 → ℝ, ‖WithLp.toLp p (Jmat *ᵥ ξ)‖ = ‖WithLp.toLp p ξ‖ := by
    intro ξ
    have e2 := norm_toLp_fin2_rpow p hptop (ξ 0) (ξ 1)
    have e3 : (![ξ 0, ξ 1] : Fin 2 → ℝ) = ξ := by
      ext i
      fin_cases i <;> rfl
    rw [e3] at e2
    have hpow : ‖WithLp.toLp p (Jmat *ᵥ ξ)‖ ^ p.toReal = ‖WithLp.toLp p ξ‖ ^ p.toReal := by
      rw [hJ, norm_toLp_fin2_rpow p hptop, e2, abs_neg]
      ring
    rw [← Real.rpow_rpow_inv (norm_nonneg (WithLp.toLp p (Jmat *ᵥ ξ))) hq0.ne', hpow,
      Real.rpow_rpow_inv (norm_nonneg _) hq0.ne']
  have heq : ∀ ε : ℝ, ∀ ξ : Fin 2 → ℝ, ‖WithLp.toLp p (Teps p.toReal ε *ᵥ ξ)‖ =
      Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ (Jmat *ᵥ ξ))‖ := by
    intro ε ξ
    rw [Teps, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hle : ∀ ε : ℝ, 0 ≤ ε → ∀ ξ : Fin 2 → ℝ,
      Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ (Jmat *ᵥ ξ))‖ ≤
        ‖WithLp.toLp p (Jmat *ᵥ ξ)‖ := by
    intro ε hε ξ
    by_cases h0 : Jmat *ᵥ ξ = 0
    · simp [h0]
    · have hR := (idea_log_rate p hp hptop (Jmat *ᵥ ξ) h0).2 ε hε
      have hexp : Real.exp (-(ε * Dstar p.toReal / 2)) * Real.exp (ε * Dstar p.toReal / 2) = 1 := by
        rw [← Real.exp_add]
        simp
      calc Real.exp (-(ε * Dstar p.toReal / 2)) * ‖WithLp.toLp p (Rot (ε / 2) *ᵥ (Jmat *ᵥ ξ))‖
          ≤ Real.exp (-(ε * Dstar p.toReal / 2)) * (Real.exp (ε * Dstar p.toReal / 2) * ‖WithLp.toLp p (Jmat *ᵥ ξ)‖) :=
            mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
        _ = ‖WithLp.toLp p (Jmat *ᵥ ξ)‖ := by rw [← mul_assoc, hexp, one_mul]
  refine ⟨fun ξ => ⟨hJ ξ, hiso ξ⟩, fun ε hε ξ => ⟨heq ε ξ, hle ε hε ξ⟩, fun ε hε => ?_⟩
  have hreal : matNorm p (Teps p.toReal ε) ≤ 1 := by
    rw [matNorm_le_iff p _ zero_le_one]
    intro ξ
    rw [heq, one_mul, ← hiso ξ]
    exact hle ε hε ξ
  exact ⟨hreal, (lemma_2_1_matrix p hptop _).trans_le hreal⟩

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.80; v2.00 wording): "At `ε = 0` we have `T_0 = J`", and "The
gain `‖P_a(T_ε)‖_p - ‖P_a(J)‖_p` is positive, but it is small: it tends to `0` as `ε → 0`" (every `a`, `B`,
`1 ≤ p ≤ ∞`; "positive", for `B > 1`, small `a` and small `ε > 0`, is the second half of `lemma_4_1` and
`lemma_4_1_paper_route`). -/
theorem idea_gain_vanishes (p : ℝ≥0∞) [Fact (1 ≤ p)] (a B : ℝ) :
    Teps p.toReal 0 = Jmat ∧
      Filter.Tendsto (fun ε => matNorm p (aeval (Teps p.toReal ε) (Pa a B)) -
        matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B))) (nhds 0) (nhds 0) := by
  have hT0 : Teps p.toReal 0 = Jmat := by simp [Teps, Rot]
  refine ⟨hT0, ?_⟩
  have hL : Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => matNorm p A) := by
    let L : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (WithLp p (Fin 2 → ℝ) →L[ℝ] WithLp p (Fin 2 → ℝ)) :=
      LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.toLpLin p p).toLinearMap
    exact continuous_norm.comp L.continuous_of_finiteDimensional
  have hT : Continuous (fun ε : ℝ => Teps p.toReal ε) := by
    unfold Teps Rot
    fun_prop
  have hc := (hL.comp ((Pa a B).continuous_aeval.comp hT)).tendsto 0
  have h := hc.sub_const (matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)))
  simpa [hT0] using h

/-- **Section 1, Idea of the proof of Theorem A** (added in v1.80): "`E_* = t_*^{p-2}(1+t_*²)²/(1+t_*^p) > 0`", the
closed form of the `E_* = t² + t^(p-2) - D_*(t - t^(p-1))` of `lemma_4_1_gamma`, at `t = t_*`. -/
theorem idea_E_closed_form (p : ℝ) (hp : 2 < p) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hcrit : deriv (dfun p) t = 0) :
    t ^ 2 + t ^ (p - 2) - Dstar p * (t - t ^ (p - 1)) = t ^ (p - 2) * (1 + t ^ 2) ^ 2 / (1 + t ^ p) ∧
      0 < t ^ (p - 2) * (1 + t ^ 2) ^ 2 / (1 + t ^ p) := by
  refine ⟨Matsaev.Gamma.E_eq hp ht hcrit, ?_⟩
  have h1 := Real.rpow_pos_of_pos ht.1 (p - 2)
  have h2 := Real.rpow_pos_of_pos ht.1 p
  positivity

/-- **Proof of Theorem A, choice of test vector** (`thm:A`; v1.90 wording): "By Lemma 3.5 (i), (iv), for `0 < a < a₁` the
real maximisers of `‖P_a(J)ξ‖_p/‖ξ‖_p` are exactly the nonzero real multiples of `s_a` and `Js_a`, with `s_a` real-analytic
in `a`" (both directions), for `2 < p < ∞`, `B > 0`; `s_a = e(θf a) = (cos θf a, sin θf a)` as in `lemma_3_5_full`. -/
theorem theorem_A_real_maximisers (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 0 < B) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ ∃ θf : ℝ → ℝ,
      (∀ a : ℝ, 0 < a → a < a₁ → ∀ ξ : Fin 2 → ℝ,
        (ξ ≠ 0 ∧ ‖WithLp.toLp p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) *ᵥ ξ)‖ =
            matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B)) * ‖WithLp.toLp p ξ‖) ↔
          ∃ c : ℝ, c ≠ 0 ∧ (ξ = c • ![Real.cos (θf a), Real.sin (θf a)] ∨
            ξ = c • (Jmat *ᵥ ![Real.cos (θf a), Real.sin (θf a)]))) ∧
      AnalyticOn ℝ (fun a => (![Real.cos (θf a), Real.sin (θf a)] : Fin 2 → ℝ)) (Set.Ico 0 a₁) := by
  obtain ⟨t, -, -, ρ, a₁, δ, η, -, -, ha₁, -, -, θf, H, -, hAn, -⟩ := lemma_3_5_full p hp hptop B hB
  refine ⟨a₁, ha₁, θf, fun a ha ha' => ?_, hAn⟩
  obtain ⟨hzero, hmax, -, -, -⟩ := H a ha ha'
  set P := aeval (Jmat : Matrix (Fin 2) (Fin 2) ℝ) (Pa a B) with hP
  set C := matNorm p P with hC
  set e0 : Fin 2 → ℝ := ![Real.cos (θf a), Real.sin (θf a)] with he0
  have hcirc : ∀ θ : ℝ, ‖WithLp.toLp p (P *ᵥ ![Real.cos θ, Real.sin θ])‖ =
      C * ‖WithLp.toLp p (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ)‖ ↔ ∃ k : ℤ, θ = θf a + k * (Real.pi / 2) :=
    fun θ => (hmax θ).symm.trans (hzero θ)
  have hhom : ∀ c : ℝ, c ≠ 0 → ∀ v : Fin 2 → ℝ,
      (‖WithLp.toLp p (P *ᵥ (c • v))‖ = C * ‖WithLp.toLp p (c • v)‖ ↔
        ‖WithLp.toLp p (P *ᵥ v)‖ = C * ‖WithLp.toLp p v‖) := by
    intro c hc v
    rw [Matrix.mulVec_smul, WithLp.toLp_smul, WithLp.toLp_smul, norm_smul, norm_smul, mul_left_comm C]
    exact ⟨fun h => mul_left_cancel₀ (norm_ne_zero_iff.mpr hc) h, fun h => by rw [h]⟩
  have he_ne : ∀ θ : ℝ, (![Real.cos θ, Real.sin θ] : Fin 2 → ℝ) ≠ 0 := by
    intro θ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
    have := Real.sin_sq_add_cos_sq θ
    rw [h0, h1] at this
    norm_num at this
  have hplus : ∀ φ : ℝ, (![Real.cos (φ + Real.pi / 2), Real.sin (φ + Real.pi / 2)] : Fin 2 → ℝ) =
      -(Jmat *ᵥ ![Real.cos φ, Real.sin φ]) := by
    intro φ
    ext i
    fin_cases i <;> simp [Jmat, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hminus : ∀ φ : ℝ, (![Real.cos (φ - Real.pi / 2), Real.sin (φ - Real.pi / 2)] : Fin 2 → ℝ) =
      Jmat *ᵥ ![Real.cos φ, Real.sin φ] := by
    intro φ
    ext i
    fin_cases i <;> simp [Jmat, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Real.cos_sub_pi_div_two,
      Real.sin_sub_pi_div_two]
  have hJJ : ∀ v : Fin 2 → ℝ, Jmat *ᵥ (Jmat *ᵥ v) = -v := by
    intro v
    rw [Matrix.mulVec_mulVec, Jmat_mul_Jmat, Matrix.neg_mulVec, Matrix.one_mulVec]
  -- the points `θf a + k π/2` of the circle are `±e0` and `±J e0`
  have hstep_plus : ∀ φ : ℝ, (∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ((![Real.cos φ, Real.sin φ] : Fin 2 → ℝ) = c • e0 ∨
        (![Real.cos φ, Real.sin φ] : Fin 2 → ℝ) = c • (Jmat *ᵥ e0))) →
      ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        ((![Real.cos (φ + Real.pi / 2), Real.sin (φ + Real.pi / 2)] : Fin 2 → ℝ) = c • e0 ∨
          (![Real.cos (φ + Real.pi / 2), Real.sin (φ + Real.pi / 2)] : Fin 2 → ℝ) = c • (Jmat *ᵥ e0)) := by
    rintro φ ⟨c, hc, hv | hv⟩
    · refine ⟨-c, by rcases hc with rfl | rfl <;> norm_num, Or.inr ?_⟩
      rw [hplus, hv, Matrix.mulVec_smul, neg_smul]
    · refine ⟨c, hc, Or.inl ?_⟩
      rw [hplus, hv, Matrix.mulVec_smul, hJJ, smul_neg, neg_neg]
  have hstep_minus : ∀ φ : ℝ, (∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ((![Real.cos φ, Real.sin φ] : Fin 2 → ℝ) = c • e0 ∨
        (![Real.cos φ, Real.sin φ] : Fin 2 → ℝ) = c • (Jmat *ᵥ e0))) →
      ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        ((![Real.cos (φ - Real.pi / 2), Real.sin (φ - Real.pi / 2)] : Fin 2 → ℝ) = c • e0 ∨
          (![Real.cos (φ - Real.pi / 2), Real.sin (φ - Real.pi / 2)] : Fin 2 → ℝ) = c • (Jmat *ᵥ e0)) := by
    rintro φ ⟨c, hc, hv | hv⟩
    · refine ⟨c, hc, Or.inr ?_⟩
      rw [hminus, hv, Matrix.mulVec_smul]
    · refine ⟨-c, by rcases hc with rfl | rfl <;> norm_num, Or.inl ?_⟩
      rw [hminus, hv, Matrix.mulVec_smul, hJJ, smul_neg, neg_smul]
  have hk : ∀ k : ℤ, ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
      ((![Real.cos (θf a + k * (Real.pi / 2)), Real.sin (θf a + k * (Real.pi / 2))] : Fin 2 → ℝ) = c • e0 ∨
        (![Real.cos (θf a + k * (Real.pi / 2)), Real.sin (θf a + k * (Real.pi / 2))] : Fin 2 → ℝ) =
          c • (Jmat *ᵥ e0)) := by
    intro k
    induction k using Int.induction_on with
    | zero => exact ⟨1, Or.inl rfl, Or.inl (by simp [he0])⟩
    | succ i ih =>
      have h := hstep_plus _ ih
      rwa [show θf a + ((i : ℤ) : ℝ) * (Real.pi / 2) + Real.pi / 2 =
        θf a + (((i : ℤ) + 1 : ℤ) : ℝ) * (Real.pi / 2) by push_cast; ring] at h
    | pred i ih =>
      have h := hstep_minus _ ih
      rwa [show θf a + ((-(i : ℤ) : ℤ) : ℝ) * (Real.pi / 2) - Real.pi / 2 =
        θf a + ((-(i : ℤ) - 1 : ℤ) : ℝ) * (Real.pi / 2) by push_cast; ring] at h
  -- `e0` and `J e0` are maximisers
  have hmax0 : ‖WithLp.toLp p (P *ᵥ e0)‖ = C * ‖WithLp.toLp p e0‖ := (hcirc (θf a)).mpr ⟨0, by simp⟩
  have hmaxJ : ‖WithLp.toLp p (P *ᵥ (Jmat *ᵥ e0))‖ = C * ‖WithLp.toLp p (Jmat *ᵥ e0)‖ := by
    have h1 := (hcirc (θf a + Real.pi / 2)).mpr ⟨1, by simp⟩
    rw [hplus] at h1
    have hJe : Jmat *ᵥ e0 = (-1 : ℝ) • -(Jmat *ᵥ e0) := by simp
    rw [hJe]
    exact (hhom (-1) (by norm_num) _).mpr h1
  have hJe0 : Jmat *ᵥ e0 ≠ 0 := by
    intro h
    apply he_ne (θf a)
    rw [← he0, ← neg_neg e0, ← hJJ e0, h, Matrix.mulVec_zero, neg_zero]
  intro ξ
  constructor
  · rintro ⟨hξ0, hξ⟩
    obtain ⟨R, θ, hR, hξR⟩ : ∃ R θ : ℝ, 0 ≤ R ∧ ξ = R • ![Real.cos θ, Real.sin θ] := by
      refine ⟨‖(⟨ξ 0, ξ 1⟩ : ℂ)‖, Complex.arg ⟨ξ 0, ξ 1⟩, norm_nonneg _, ?_⟩
      ext i
      fin_cases i
      · simp [Complex.norm_mul_cos_arg]
      · simp [Complex.norm_mul_sin_arg]
    have hR0 : R ≠ 0 := by
      rintro rfl
      exact hξ0 (by rw [hξR, zero_smul])
    rw [hξR] at hξ
    obtain ⟨k, hk'⟩ := (hcirc θ).mp ((hhom R hR0 _).mp hξ)
    obtain ⟨c, hc, hv | hv⟩ := hk k
    · refine ⟨R * c, mul_ne_zero hR0 (by rcases hc with rfl | rfl <;> norm_num), Or.inl ?_⟩
      rw [hξR, hk', hv, smul_smul]
    · refine ⟨R * c, mul_ne_zero hR0 (by rcases hc with rfl | rfl <;> norm_num), Or.inr ?_⟩
      rw [hξR, hk', hv, smul_smul]
  · rintro ⟨c, hc, hv | hv⟩
    · subst hv
      exact ⟨smul_ne_zero hc (he_ne _), (hhom c hc _).mpr hmax0⟩
    · subst hv
      exact ⟨smul_ne_zero hc hJe0, (hhom c hc _).mpr hmaxJ⟩

/-! ## Section 5: Theorem A -/

/-- **Theorem A** (`thm:A`), last sentence: "since the transpose of `R_θ` is `R_(-θ)`, this is again a scaled rotation by
slightly more than a right angle, now counterclockwise": `R_θᵀ = R_(-θ)`, so the matrix for `1 < p < 2` (the transpose of
`T_ε = e^(-εD_*/2) R_(π/2+ε/2)`, built for the dual exponent) is `e^(-εD_*/2) R_(-(π/2+ε/2))`. -/
theorem theorem_A_transpose (q θ ε : ℝ) :
    (Rot θ)ᵀ = Rot (-θ) ∧ (Teps q ε)ᵀ = Real.exp (-(ε * Dstar q / 2)) • Rot (-(Real.pi / 2 + ε / 2)) := by
  refine ⟨Matsaev.Cov130.rot_transpose θ, ?_⟩
  rw [teps_eq_rot, Matrix.transpose_smul, Matsaev.Cov130.rot_transpose]

/-- **Theorem A** (`thm:A`), the constant of its explicit form: for `p > 2`, `D_* > 0` and
`D_* = max_{0 ≤ t ≤ 1} (t - t^(p-1)) / (1 + t^p)` (attained), and this is the number `Dstar p` (`max_{w ≠ 0} Q(w)`,
Lemma 3.4) that `Teps` uses. From `lemma_3_4` and `Q(1, t) = f(t)` for `t > 0`. -/
theorem theorem_A_dstar (p : ℝ) (hp : 2 < p) : 0 < Dstar p ∧ IsGreatest (dfun p '' Set.Icc 0 1) (Dstar p) := by
  obtain ⟨t, ht, -, -, hpos, hle, hD, -, -⟩ := lemma_3_4 p hp
  refine ⟨hD ▸ hpos, ⟨t, ⟨ht.1.le, ht.2.le⟩, hD.symm⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  rw [hD]
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · rw [← h0]
    have h00 : dfun p 0 = 0 := by
      simp [dfun, Real.zero_rpow (by linarith : p - 1 ≠ 0), Real.zero_rpow (by linarith : p ≠ 0)]
    rw [h00]
    exact hpos.le
  · have hQ : Qf p 1 s = dfun p s := by
      unfold Qf dfun phi
      rw [sign_pos h0, sign_pos one_pos, abs_one, abs_of_pos h0, Real.one_rpow, Real.one_rpow]
      simp
    rw [← hQ]
    exact hle 1 s (by simp)

/-- **Theorem A** (`thm:A`), explicit form for `p > 2`: one can take `T = T_ε = e^(-ε D_*/2) R_(π/2 + ε/2) = exp(ε K_*) J`
(`teps_eq_rot`, `teps_eq_exp`) for all sufficiently small `ε > 0` (depending on `a`); real and complex `ℓ^p`. -/
theorem theorem_A_explicit (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hptop : p ≠ ⊤) (B : ℝ) (hB : 1 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (matNorm p (Teps p.toReal ε) ≤ 1 ∧ shiftNorm p ℝ (Pa a B) < matNorm p (aeval (Teps p.toReal ε) (Pa a B))) ∧
      (matNorm p ((Teps p.toReal ε).map (algebraMap ℝ ℂ)) ≤ 1 ∧
        shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) <
          matNorm p (aeval ((Teps p.toReal ε).map (algebraMap ℝ ℂ)) (Pa (a : ℂ) (B : ℂ)))) := by
  obtain ⟨a₀, ha₀, h34⟩ := theorem_3_6_le p (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hp) hptop hp.ne' B (by linarith)
  obtain ⟨hcontr, a₂, ha₂, h41⟩ := lemma_4_1 p hp hptop B hB
  refine ⟨min a₀ a₂, lt_min ha₀ ha₂, fun a ha ha' => ?_⟩
  obtain ⟨ε₀, hε₀, hε₁⟩ := h41 a ha (lt_of_lt_of_le ha' (min_le_right _ _))
  refine ⟨ε₀, hε₀, fun ε hε hε' => ?_⟩
  have hS := h34 a ha.le (lt_of_lt_of_le ha' (min_le_left _ _))
  have hT := hε₁ ε hε hε'
  obtain ⟨hc, hcC⟩ := hcontr ε hε.le
  refine ⟨⟨hc, lt_of_le_of_lt hS hT⟩, ⟨hcC, ?_⟩⟩
  rw [← Matsaev.Assembly.Pa_map, lemma_2_1_shift p hptop, Matsaev.Assembly.aeval_map_complex,
    lemma_2_1_matrix p hptop]
  exact lt_of_le_of_lt hS hT

/-- **Theorem A** (`thm:A`), explicit form for `1 < p < 2`: the transpose of `T_ε` for the dual exponent `p'`
(`theorem_A_transpose`: `T_εᵀ = e^(-εD_*/2) R_(-(π/2+ε/2))`, as `R_θᵀ = R_(-θ)`). -/
theorem theorem_A_explicit_dual (p q : ℝ≥0∞) [Fact (1 ≤ p)] (hpq : p.toReal.HolderConjugate q.toReal)
    (hp : p < 2) (B : ℝ) (hB : 1 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (matNorm p (Teps q.toReal ε)ᵀ ≤ 1 ∧ shiftNorm p ℝ (Pa a B) < matNorm p (aeval (Teps q.toReal ε)ᵀ (Pa a B))) ∧
      (matNorm p ((Teps q.toReal ε)ᵀ.map (algebraMap ℝ ℂ)) ≤ 1 ∧
        shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) <
          matNorm p (aeval ((Teps q.toReal ε)ᵀ.map (algebraMap ℝ ℂ)) (Pa (a : ℂ) (B : ℂ)))) := by
  obtain ⟨hq2, hqtop⟩ := Matsaev.Assembly.conj_gt_two hpq hp
  have : Fact (1 ≤ q) := ⟨le_of_lt (lt_trans (by norm_num : (1 : ℝ≥0∞) < 2) hq2)⟩
  have hptop : p ≠ ⊤ := ne_top_of_lt hp
  obtain ⟨a₀, ha₀, hA⟩ := theorem_A_explicit q hq2 hqtop B hB
  refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
  obtain ⟨ε₀, hε₀, hε₁⟩ := hA a ha ha'
  refine ⟨ε₀, hε₀, fun ε hε hε' => ?_⟩
  obtain ⟨⟨hc, hlt⟩, -⟩ := hε₁ ε hε hε'
  obtain ⟨hS, hT⟩ := lemma_2_3 p q hpq (Pa a B)
  obtain ⟨hTP, hTn⟩ := hT (Teps q.toReal ε)
  have hreal1 : matNorm p (Teps q.toReal ε)ᵀ ≤ 1 := by rw [hTn]; exact hc
  have hreal2 : shiftNorm p ℝ (Pa a B) < matNorm p (aeval (Teps q.toReal ε)ᵀ (Pa a B)) := by
    rw [hS, hTP]; exact hlt
  refine ⟨⟨hreal1, hreal2⟩, ⟨(lemma_2_1_matrix p hptop _).trans_le hreal1, ?_⟩⟩
  rw [← Matsaev.Assembly.Pa_map, lemma_2_1_shift p hptop, Matsaev.Assembly.aeval_map_complex,
    lemma_2_1_matrix p hptop]
  exact hreal2

/-- **Theorem A** (`thm:A`), real `ℓ^p`: for `p ∈ (1, ∞) \ {2}` and `B > 1`, for every sufficiently small
`a > 0` there is a real `2 × 2` matrix `T` with `‖T‖_{ℓ^p_2} ≤ 1` and `‖P_a(T)‖_{ℓ^p_2} > ‖P_a(S)‖_{ℓ^p}`. -/
theorem theorem_A_real (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) (B : ℝ) (hB : 1 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∃ T : Matrix (Fin 2) (Fin 2) ℝ,
      matNorm p T ≤ 1 ∧ shiftNorm p ℝ (Pa a B) < matNorm p (aeval T (Pa a B)) := by
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · obtain ⟨q, -, -, hpq⟩ := Matsaev.Assembly.exists_conj p hp hptop
    obtain ⟨a₀, ha₀, hA⟩ := theorem_A_explicit_dual p q hpq hlt B hB
    refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
    obtain ⟨ε₀, hε₀, hε⟩ := hA a ha ha'
    exact ⟨_, (hε (ε₀ / 2) (by positivity) (by linarith)).1⟩
  · obtain ⟨a₀, ha₀, hA⟩ := theorem_A_explicit p hgt hptop B hB
    refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
    obtain ⟨ε₀, hε₀, hε⟩ := hA a ha ha'
    exact ⟨_, (hε (ε₀ / 2) (by positivity) (by linarith)).1⟩

/-- **Theorem A** (`thm:A`), complex `ℓ^p` (Matsaev's setting): the same real matrix `T`, acting on the
complex `ℓ^p_2`, is a contraction and `‖P_a(T)‖_{ℓ^p_2} > ‖P_a(S)‖_{ℓ^p}`. -/
theorem theorem_A (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) (B : ℝ) (hB : 1 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∃ T : Matrix (Fin 2) (Fin 2) ℝ,
      matNorm p (T.map (algebraMap ℝ ℂ)) ≤ 1 ∧
      shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) < matNorm p (aeval (T.map (algebraMap ℝ ℂ)) (Pa (a : ℂ) (B : ℂ))) := by
  rcases lt_or_gt_of_ne hp2 with hlt | hgt
  · obtain ⟨q, -, -, hpq⟩ := Matsaev.Assembly.exists_conj p hp hptop
    obtain ⟨a₀, ha₀, hA⟩ := theorem_A_explicit_dual p q hpq hlt B hB
    refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
    obtain ⟨ε₀, hε₀, hε⟩ := hA a ha ha'
    exact ⟨_, (hε (ε₀ / 2) (by positivity) (by linarith)).2⟩
  · obtain ⟨a₀, ha₀, hA⟩ := theorem_A_explicit p hgt hptop B hB
    refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
    obtain ⟨ε₀, hε₀, hε⟩ := hA a ha ha'
    exact ⟨_, (hε (ε₀ / 2) (by positivity) (by linarith)).2⟩

/-- **Matsaev's conjecture is false for every `p ∈ (1, ∞) \ {2}`** (the paper's title; Theorem A with `B = 2`): it already
fails on the `L^p` space `ℓ^p_2`. -/
theorem matsaev_conjecture_false (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) :
    ¬ MatsaevOnL2 p := by
  intro h
  obtain ⟨a₀, ha₀, hA⟩ := theorem_A p hp hptop hp2 2 (by norm_num)
  obtain ⟨T, hT1, hlt⟩ := hA (a₀ / 2) (by positivity) (by linarith)
  exact absurd (h (T.map (algebraMap ℝ ℂ)) hT1 _) (not_le.mpr hlt)

/-- **Matsaev's conjecture is false for every `p ∈ (1, ∞) \ {2}`**, in the literature's form, the paper's eq. (1)
(`eq:matsaev`; `MatsaevConjecture`: every contraction of every `L^p(μ)`, Mathlib's `MeasureTheory.Lp`, every complex
polynomial; review r1, finding 1): the counterexample lives on `Fin 2` with the counting measure. -/
theorem matsaev_conjecture_false_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) :
    ¬ MatsaevConjecture p :=
  fun h => matsaev_conjecture_false p hp hptop hp2 (Matsaev.matsaevOnL2_of_conjecture p hptop h)

/-- **The counterexample, on an explicit `L^p` space** (review r2, finding 2): on `L^p(Fin 2, counting measure)`, a finite
measure space, there is a contraction `T` and a polynomial `P` with `‖P(T)‖ > ‖P(S)‖`. So every variant of the conjecture
restricted to finite or σ-finite measure spaces is refuted too. -/
theorem matsaev_counterexample_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) :
    ∃ T : MeasureTheory.Lp ℂ p (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 2)) →L[ℂ]
        MeasureTheory.Lp ℂ p (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 2)),
      ‖T‖ ≤ 1 ∧ ∃ P : ℂ[X], shiftNorm p ℂ P < ‖aeval T P‖ := by
  obtain ⟨a₀, ha₀, hA⟩ := theorem_A p hp hptop hp2 2 (by norm_num)
  obtain ⟨T, hT1, hlt⟩ := hA (a₀ / 2) (by positivity) (by linarith)
  set φ := (Matsaev.lpCountEquiv p hptop).toContinuousLinearEquiv.conjContinuousAlgEquiv
  have hnorm : ∀ A, ‖φ A‖ = ‖A‖ := Matsaev.norm_conj_linearIsometryEquiv (Matsaev.lpCountEquiv p hptop)
  refine ⟨φ (matOp p (T.map (algebraMap ℝ ℂ))), by rw [hnorm]; exact hT1, Pa ((a₀ / 2 : ℝ) : ℂ) ((2 : ℝ) : ℂ), ?_⟩
  rw [aeval_algHom_apply, hnorm, ← matOp_aeval]
  exact hlt

/-- **Theorem A on `ℓ^p` itself** (`thm:A`, last sentence of its proof in Section 5): for `p ∈ (1, ∞) \ {2}` and `B > 1`,
for every sufficiently small `a > 0` there is a contraction `T` of the complex `ℓ^p(ℕ)` with `‖P_a(T)‖ > ‖P_a(S)‖`, namely
`T ⊕ 0` on `ℓ^p_2 ⊕_p ℓ^p = ℓ^p` for the `T` of `theorem_A`. So eq. (1) (`eq:matsaev`) also fails on `ℓ^p` itself. -/
theorem theorem_A_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) (B : ℝ) (hB : 1 < B) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      ∃ T : lp (fun _ : ℕ => ℂ) p →L[ℂ] lp (fun _ : ℕ => ℂ) p,
        ‖T‖ ≤ 1 ∧ shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) < ‖aeval T (Pa (a : ℂ) (B : ℂ))‖ := by
  obtain ⟨a₀, ha₀, hA⟩ := theorem_A p hp hptop hp2 B hB
  refine ⟨a₀, ha₀, fun a ha ha' => ?_⟩
  obtain ⟨T, hT1, hlt⟩ := hA a ha ha'
  refine ⟨LpNat.sumZero p hptop (matOp p (T.map (algebraMap ℝ ℂ))),
    (LpNat.norm_sumZero_le p hptop _).trans hT1, ?_⟩
  calc shiftNorm p ℂ (Pa (a : ℂ) (B : ℂ)) < matNorm p (aeval (T.map (algebraMap ℝ ℂ)) (Pa (a : ℂ) (B : ℂ))) := hlt
    _ = ‖aeval (matOp p (T.map (algebraMap ℝ ℂ))) (Pa (a : ℂ) (B : ℂ))‖ := by rw [matNorm, matOp_aeval]
    _ ≤ _ := LpNat.norm_aeval_le_sumZero p hptop _ _

/-! ## Section 5: Theorem B, Corollary 5.1, Remark 5.2 -/

/-- **Remark 5.2** (`rem:triv`), its inequality: for real `α ≠ 0` and `1 < p < ∞`, `‖2I + αJ‖_p < 2 + |α|` on the real
`ℓ^p_2` (by strict convexity: equality would force `|ξ₁| = |ξ₂|` and two sign conditions that `α ≠ 0` excludes), and the
same on the complex `ℓ^p_2` (Lemma 2.1). Here `2I + αJ = P̃(J)` for `P̃(z) = 1 + αz - z²`. -/
theorem remark_5_2_lt (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (α : ℝ) (hα : α ≠ 0) :
    matNorm p ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + α • Jmat) < 2 + |α| ∧
      matNorm p (((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + α • Jmat).map (algebraMap ℝ ℂ)) < 2 + |α| := by
  have hq : 1 < p.toReal := by
    have h1 : (1 : ℝ≥0∞).toReal < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).mpr hp
    simpa using h1
  have hq0 : 0 < p.toReal := by linarith
  set M : Matrix (Fin 2) (Fin 2) ℝ := (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + α • Jmat with hM
  have hreal : matNorm p M < 2 + |α| := by
    obtain ⟨x, hx1, hxM⟩ := exists_eq_matNorm p M
    have hxe : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      have h0 : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
      rw [hxe, h.1, h.2, h0, WithLp.toLp_zero, norm_zero] at hx1
      norm_num at hx1
    have hmv : M *ᵥ ![x 0, x 1] = ![2 * x 0 + α * x 1, 2 * x 1 - α * x 0] := by
      rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Jmat_mulVec]
      ext i; fin_cases i <;> simp [sub_eq_add_neg]
    have h1 : ‖WithLp.toLp p x‖ ^ p.toReal = |x 0| ^ p.toReal + |x 1| ^ p.toReal := by
      rw [hxe, norm_toLp_fin2_rpow p hptop]; simp
    have h2 : ‖WithLp.toLp p (M *ᵥ x)‖ ^ p.toReal =
        |2 * x 0 + α * x 1| ^ p.toReal + |2 * x 1 - α * x 0| ^ p.toReal := by
      rw [hxe, hmv, norm_toLp_fin2_rpow p hptop]; simp
    have key := Rem52.pointwise_lt p.toReal hq α (x 0) (x 1) hα hne
    rw [← h1, hx1, Real.one_rpow, mul_one, ← h2, hxM] at key
    exact (Real.rpow_lt_rpow_iff (matNorm_nonneg _ _) (by positivity) hq0).mp key
  exact ⟨hreal, (lemma_2_1_matrix p hptop M).trans_lt hreal⟩

/-- **Theorem B** (`thm:B`): for `P(z) = c₀ + c₁z + c₂z²` with `|c₀| = |c₂|`, `‖P(T)‖_p ≤ ‖P(S)‖_p` for every
`1 ≤ p ≤ ∞` and every contraction `T` of every `L^p` space (Mathlib's `MeasureTheory.Lp ℂ p μ`, any measure space). -/
theorem theorem_B (p : ℝ≥0∞) [Fact (1 ≤ p)] (c₀ c₁ c₂ : ℂ) (hc : ‖c₀‖ = ‖c₂‖) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (T : MeasureTheory.Lp ℂ p μ →L[ℂ] MeasureTheory.Lp ℂ p μ) (hT : ‖T‖ ≤ 1) :
    ‖aeval T (C c₀ + C c₁ * X + C c₂ * X ^ 2)‖ ≤ shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2) :=
  ThmB.theorem_B_proved p c₀ c₁ c₂ hc Ω μ T hT

/-- **Corollary 5.1** (`cor:exactB`): for `P(z) = c₀ + c₁z + c₂z²` with `|c₀| = |c₂| > 0`, `|ζ| = 1` with
`ζ² = -c₂/c₀`, and `1 ≤ p ≤ ∞`: `‖P(S)‖_p = ‖P(ζ̄J)‖_p = max_{|μ|=1} ‖P(μJ)‖_p` (complex `ℓ^p_2`). -/
theorem corollary_5_1 (p : ℝ≥0∞) [Fact (1 ≤ p)] (c₀ c₁ c₂ ζ : ℂ) (hc : ‖c₀‖ = ‖c₂‖) (hpos : 0 < ‖c₀‖)
    (hζ1 : ‖ζ‖ = 1) (hζ : ζ ^ 2 = -c₂ / c₀) :
    shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2) =
        matNorm p (aeval ((starRingEnd ℂ) ζ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C c₀ + C c₁ * X + C c₂ * X ^ 2)) ∧
      IsGreatest {r : ℝ | ∃ μ : ℂ, ‖μ‖ = 1 ∧
          r = matNorm p (aeval (μ • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C c₀ + C c₁ * X + C c₂ * X ^ 2))}
        (shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2)) :=
  ThmB.corollary_5_1_proved p c₀ c₁ c₂ ζ hc hpos hζ1 hζ

/-- **Corollary 5.1** (`cor:exactB`), the remark after it: the factor `ζ̄` cannot be omitted. For `P(z) = 1 + z²`,
`P(J) = 0` while `‖P(S)‖_p = 2`, for every `1 ≤ p ≤ ∞` (here `ζ = i`). -/
theorem corollary_5_1_remark (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2) = 0 ∧
      shiftNorm p ℂ (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2) = 2 := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Jmat, sq]
  · obtain ⟨h, -⟩ := corollary_5_1 p 1 0 1 Complex.I (by simp) (by simp) (by simp) (by simp [sq])
    rw [h]
    have hM : aeval ((starRingEnd ℂ) Complex.I • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2)
        = (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Jmat, sq] <;> norm_num
    rw [hM, ThmB.matNorm_smul_complex]
    have h1 : matNorm p (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
      rw [matNorm]
      have : matOp p (1 : Matrix (Fin 2) (Fin 2) ℂ) = ContinuousLinearMap.id ℂ _ := by
        ext x i
        simp [matOp]
      rw [this, ContinuousLinearMap.norm_id]
    rw [h1]
    norm_num

/-- **Corollary 5.1** (`cor:exactB`), the remark after it (added in v1.70): "with `ζ = i`,
`‖P(S)‖_p = ‖P(-iJ)‖_p = ‖2I‖_p = 2`" for `P(z) = 1 + z²` and every `1 ≤ p ≤ ∞`: Corollary 5.1 at `ζ = i` (`ζ̄ = -i`),
`P(-iJ) = I + (-iJ)² = 2I`, and `‖2I‖_p = 2`. -/
theorem corollary_5_1_remark_value (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    shiftNorm p ℂ (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2) =
        matNorm p (aeval ((-Complex.I) • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2)) ∧
      aeval ((-Complex.I) • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2) =
        (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      matNorm p ((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 2 := by
  obtain ⟨h, -⟩ := corollary_5_1 p 1 0 1 Complex.I (by simp) (by simp) (by simp) (by simp [sq])
  rw [Complex.conj_I] at h
  have hM : aeval ((-Complex.I) • (Jmat : Matrix (Fin 2) (Fin 2) ℂ)) (C (1 : ℂ) + C 0 * X + C 1 * X ^ 2) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jmat, sq] <;> norm_num
  have h1 : matNorm p (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [matNorm]
    have : matOp p (1 : Matrix (Fin 2) (Fin 2) ℂ) = ContinuousLinearMap.id ℂ _ := by
      ext x i
      simp [matOp]
    rw [this, ContinuousLinearMap.norm_id]
  have h2 : matNorm p ((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 2 := by
    rw [ThmB.matNorm_smul_complex, h1]
    norm_num
  exact ⟨h, hM, h2⟩

/-- **Remark 5.2** (`rem:triv`): Theorem B does not reduce to the trivial bound. For `P̃(z) = 1 + αz - z²` (`= Pa α 1`)
with real `α ≠ 0` and `1 < p < ∞`: `‖P̃(S)‖_p = ‖2I + αJ‖_p < 2 + |α| = ∑ |c_k|` (complex spaces). The equality is
Corollary 5.1 with `ζ = 1`; the inequality is `remark_5_2_lt`. -/
theorem remark_5_2 (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (α : ℝ) (hα : α ≠ 0) :
    shiftNorm p ℂ (Pa (α : ℂ) 1) =
        matNorm p (((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + α • Jmat).map (algebraMap ℝ ℂ)) ∧
      shiftNorm p ℂ (Pa (α : ℂ) 1) < 2 + |α| := by
  have hM : aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa (α : ℂ) 1) =
      ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + α • Jmat).map (algebraMap ℝ ℂ) := by
    rw [Matsaev.aeval_Jmat_Pa_proved]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Jmat] <;> norm_num
  have heq : shiftNorm p ℂ (Pa (α : ℂ) 1) = matNorm p (aeval (Jmat : Matrix (Fin 2) (Fin 2) ℂ) (Pa (α : ℂ) 1)) :=
    le_antisymm (ThmB.key_lp p (α : ℂ) (shiftOp p ℂ) (ThmB.norm_shiftOp_le p))
      (lemma_2_2 (𝕜 := ℂ) p (Pa (α : ℂ) 1))
  rw [hM] at heq
  exact ⟨heq, heq ▸ (remark_5_2_lt p hp hptop α hα).2⟩

end Matsaev.Paper
