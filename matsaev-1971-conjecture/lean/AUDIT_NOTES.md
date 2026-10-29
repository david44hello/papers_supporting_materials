# The Matsaev (1971) conjecture is false for every p ≠ 2 — notes on the Lean proof

This folder is a formal proof, checked by the Lean 4 proof assistant, of every result of the paper "The Matsaev (1971)
conjecture is false for every p ≠ 2" by Dave Goel: every lemma, theorem, corollary and remark, and the small claims in
its text. Lean checked version 2.00 of the paper. The paper's link will be added here when it is posted.

## The theorems, in plain words

Matsaev's conjecture (1971) says: for 1 < p < ∞, every contraction T on every L^p space and every polynomial P satisfy
‖P(T)‖ ≤ ‖P(S)‖, where S is the right shift on ℓ^p. The paper proves:

- **Theorem A:** let p ∈ (1, ∞), p ≠ 2, B > 1 and P_a(z) = 1 + az − Bz². For every sufficiently small a > 0 (how small
  depends only on p and B) there is a real 2 × 2 matrix T with ‖T‖_p ≤ 1 on ℓ^p_2 such that ‖P_a(T)‖_p > ‖P_a(S)‖_p. So the conjecture is false for every
  p ≠ 2.
- **Theorem B:** let P(z) = c₀ + c₁z + c₂z² with complex coefficients and |c₀| = |c₂|. Then ‖P(T)‖_p ≤ ‖P(S)‖_p for
  every 1 ≤ p ≤ ∞ and every contraction T on every L^p space.

In Lean, with the conjecture in the literature's form (every contraction of every complex L^p(μ), every polynomial):

```lean
theorem Matsaev.Paper.matsaev_conjecture_false_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hptop : p ≠ ⊤) (hp2 : p ≠ 2) :
    ¬ MatsaevConjecture p
theorem Matsaev.Paper.theorem_B (p : ℝ≥0∞) [Fact (1 ≤ p)] (c₀ c₁ c₂ : ℂ) (hc : ‖c₀‖ = ‖c₂‖) (Ω : Type*) [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (T : MeasureTheory.Lp ℂ p μ →L[ℂ] MeasureTheory.Lp ℂ p μ) (hT : ‖T‖ ≤ 1) :
    ‖aeval T (C c₀ + C c₁ * X + C c₂ * X ^ 2)‖ ≤ shiftNorm p ℂ (C c₀ + C c₁ * X + C c₂ * X ^ 2)
```

## What the proof assumes

Nothing beyond Mathlib and Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No result of
another paper is taken as an axiom (there is no `Matsaev/Cited/` folder).

## Where each claim of the paper is

[Matsaev/Paper/Statements.lean](Matsaev/Paper/Statements.lean) has one Lean theorem per claim, named by the paper's
numbering. [AUDIT.md](AUDIT.md), which `scripts/check.sh` regenerates from Lean's `#print axioms`, lists all 76 claims
with their place in the paper: all 76 are PROVED from Lean's three standard axioms alone.

Lean checks every proof. A referee only needs to check that the statements say what the paper says: the definitions in
[Matsaev/Defs/Scalar.lean](Matsaev/Defs/Scalar.lean), [Matsaev/Defs/Spaces.lean](Matsaev/Defs/Spaces.lean),
[Matsaev/Defs/Conjecture.lean](Matsaev/Defs/Conjecture.lean) and [Matsaev/Angle/Defs.lean](Matsaev/Angle/Defs.lean),
and the statements in [Matsaev/Paper/Statements.lean](Matsaev/Paper/Statements.lean).

## Where Lean takes another route

In 17 places Lean proves a step inside a proof by another argument than the paper's text; [AUDIT.md](AUDIT.md) lists
them under "Route differences". The statements are proved; those passages of the paper's text are not checked word for
word.

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib v4.35.0, commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
(all dependencies pinned in `lake-manifest.json`).
