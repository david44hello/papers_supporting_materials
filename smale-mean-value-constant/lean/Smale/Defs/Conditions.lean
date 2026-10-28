/-
Smale/Defs/Conditions.lean — the conditions of Lemma 4.3 (C) and (R) and the computer-checked fact (R) of
Theorem 5.1 (paper 009, posted v1.80; tex lines of that version). A NEW file (Statements v0.51) so that proof files, which may not import
Paper/Statements.lean, can use them. Moved verbatim from Statements v0.41.
-/
import Smale.Defs.Data

namespace Smale

open Polynomial Complex Metric ComplexConjugate

/-- Condition (C) of Lemma 4.3 (tex l.286-287): `Q' = ZV`, `V` without zeros in `𝔻̄`, `Z` a nonzero constant
times `∏ (z - ζ_ν)^{μ_ν}` with all `|ζ_ν| = 1` and all `μ_ν` positive integers (possibly an empty product). -/
def CondC (Q : ℂ[X]) : Prop :=
  ∃ V : ℂ[X], ∃ κ : ℂ, κ ≠ 0 ∧ ∃ zs : List (ℂ × ℕ), (∀ z ∈ zs, ‖z.1‖ = 1 ∧ 0 < z.2) ∧
    (∀ w ∈ closedDisk, V.eval w ≠ 0) ∧ Q.derivative = C κ * (zs.map fun z => (X - C z.1) ^ z.2).prod * V

/-- Fact (R) of Lemma 4.3 for our data (tex l.288-291): `Res_w(P_c, P_c*) ≠ 0` for every `c ∈ [-1, 1]`, the resultant
being the `(2n-2) × (2n-2)` Sylvester determinant at formal degrees `(n-1, n-1)`, i.e. Mathlib's `resultant _ _ 17 17`
for `n = 18`. Checked by computer (see `CheckR`), NOT proved in Lean; no proof assumes it: the main chain in
Paper/Statements.lean takes it as an explicit hypothesis. -/
def CondRdata : Prop :=
  ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) 17 17 ≠ 0

/-- **COMPUTER-CHECKED, NOT PROVED IN LEAN.** Theorem 5.1, proof (R) (tex l.402-418), stated for `H`:
`F(c) = Res_w(P_c, P_c*)` has real coefficients and degree `578`; `F(±1) ≠ 0`; `F` has no zero in `(-1, 1)`.
The program computes `F` for `L·H`, `L` a positive integer that makes the coefficients Gaussian integers; that `F`
is `L^34` times this one (`thm_5_1_R_scaling`: a positive constant), so the two checks are the same. Checked in
exact arithmetic by the program pair_checks/check_pair.py of the paper's folder (md5 b659ca29); its output
is pair_checks/check_pair.log there. Lean's kernel cannot check it in reasonable time on one core (measured: one of the
47 Descartes tests takes more than 40 minutes; `F = Res` needs 579 exact 34 × 34 determinants or a ~380 MB
certificate). No proof assumes it. -/
def CheckR : Prop :=
  ∃ F : ℝ[X], F.natDegree = 578 ∧
    (∀ c : ℝ, resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) 17 17 = ((F.eval c : ℝ) : ℂ)) ∧
    F.eval (-1) ≠ 0 ∧ F.eval 1 ≠ 0 ∧ ∀ c : ℝ, c ∈ Set.Ioo (-1 : ℝ) 1 → F.eval c ≠ 0

end Smale
