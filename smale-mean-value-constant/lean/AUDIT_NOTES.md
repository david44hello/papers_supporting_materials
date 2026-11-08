## Notes (hand-written; appended by scripts/audit.py)

### A. Route differences (the Lean proof of a claim takes another path than the paper's text)

A1. Lemma 5.3 (tex l.495-507). The paper: d - 1 of the d critical points of p_ε tend to those of p (Hurwitz's
theorem), the remaining one, β_ε, tends to ∞, and p_ε(β_ε)/β_ε → ∞; hence m(p_ε) → m(p). Lean (`lem_5_3_limit`,
Smale/Proofs/Lemma53.lean): an upper bound by Rouché's theorem on a small circle around the critical point of p where
m(p) is attained; a lower bound because, on |w| ≤ R away from the critical points of p, |p'| has a positive minimum, so
for small ε no critical point of p_ε lies there, while for |β| ≥ R the ratio p_ε(β)/β is large (`lem_5_3_far_ratio`).
The paper's steps are proved as separate rows, though this proof does not use the first one: the Hurwitz step
(`lem_5_3_hurwitz`: exactly d - 1 critical points of p_ε stay in a disk that contains those of p, and μ of them are
near each critical point of multiplicity μ) and "β_ε tends to ∞" (`lem_5_3_escape`).

A2. The margin of H' (Remark 5.2, tex l.471-472). The paper gives 1.00001141…. Lean:
H' has no zero with |z| ≤ 1.00001141 (a Schur–Cohn certificate for H'(rw), r = 1.00001141, in
Smale/Proofs/SchurCertR.lean), and H' has a zero within 10⁻¹⁴ of a point zH with 20 decimals and
|zH| + 10⁻¹⁴ < 1.00001142 (a Rouché certificate, Smale/Proofs/RoucheCert.lean). The zero of H' nearest to the circle
is then its zero of least modulus (`rem_5_2_Hprime`).

A3. The control (tex v1.90 l.439-442, removed at v2.90; its rows are RETIRED). The program computes the resultant F for H(sz) and finds a zero in [-1, 1].
Lean proves that such a zero exists without computing F: (H(sz))' has no zero in the closed disk (by A2, as
s = 1.0000072 < 1.00001141); the Dieudonné polynomial of H(sz) at c = 0.9231 has a zero inside the open disk (a Rouché
certificate for P_c of H at c = 0.9231, then the scaling z ↦ z/s); so the zero count of Lemma 4.1 is not constant on
[-1, 1], some P_c of H(sz) has a zero on the circle, and there the resultant vanishes (Lemma 4.3). The claim is the
old text's claim, "the resultant in (R) has a zero in [-1, 1]" (`ctrl_R_fails`).

A4. Remark 2.3 (tex l.200-208) and [JN, Prop. 3.1], whose first sentence Lean proves (`jatarNg_prop_3_1_proved`,
Smale/Proofs/JN31Assembly.lean). Lean uses the pair W = ψ/κ, B = (q∘ψ)/R, as the Remark does, with κ = ψ'(0) not rotated to be
positive (nothing needs it, since B(0) = 1/R whatever κ is), and with these differences. (a) Lean
never states that Ω is simply connected. The Riemann mapping theorem (Smale/Vendor/RiemannMap.lean, ported from Mathlib's open
draft pull request #33505 by Yury Kudryashov, its changes listed at the top of that file) is used in a form that asks only for
square roots of nonvanishing functions on a bounded domain. These come from Runge's theorem on the sublevel sets of Ω, whose
complements are connected by the maximum modulus principle (JN31Domain.lean), through the Cauchy-Pompeiu formula
(JN31Pompeiu.lean, JN31Runge.lean, JN31Root.lean). (b) B is a finite Blaschke product by dividing out the zeros of q∘ψ and the
maximum modulus principle (JN31Blaschke.lean). The other steps are also stated with ψ as a parameter (`rem_2_3_formulas`). This
says nothing about the proof in [JN]. The construction was not tried by hand on a polynomial with m(p) > 1, whose smallest
published degree is 29,984; the check is the Lean proof.

A5. [JN, Prop. 4.2], which the paper cites (Theorem 2.2, tex l.183-185). Lean proves its first sentence
(`jatarNg_prop_4_2_proved`, Smale/Proofs/JNAssembly.lean), not by the route of [JN], which uses their Lemma 2.1, Runge's
theorem and Hilbert's lemniscate theorem. Lean: Ω = W(disk of radius r < 1); Runge on W(closed disk), by the Cauchy formula
pulled back through W and pole pushing (JNRunge.lean, JNPole.lean; the complement of W(closed disk) is connected,
JNUnivalent.lean); one polynomial small on an inner set and larger outside an outer set, from Fekete points (JNFekete.lean,
in place of Hilbert's theorem); then H = P + z q^m (JNCrit.lean), as in [JN]. This says nothing about the proof in [JN].

A6. Dieudonné's criterion, which the paper cites (tex l.280-283). Lean proves the "if" direction
(`dieudonne_criterion_proved`, Smale/Proofs/DieudonneIf.lean), by a minimal pair of points with equal values.

A7. Fact (R) of Lemma 4.3 (tex l.332-335). The paper checks it by computer: F(c) has degree 578, and exact tests show it has no
zero on [-1, 1]. Lean does not compute F. A common zero of P_c and P_c*, anywhere in the complex plane, would make the 17 x 17
Schur-Cohn matrix of P_c singular, so it is enough that this matrix is invertible (`condR_proved`, Smale/Paper/Unconditional.lean,
Smale/R/). For c in [0, 1] that is shown on 299 dyadic intervals that cover [0, 1]: on each one a fixed matrix A makes A B(c) A*
strictly row dominant, for every c of the interval, in exact integer arithmetic checked by the kernel (`decide +kernel`), with the
coefficients of H rounded at 2^-64 and the rounding error bounded. For c < 0 the symmetry P_(-c)(w) = P_c(-w) reduces to c > 0.
Python only proposes the matrices, the list of intervals and the rounded coefficients (scripts/gen_r_intervals.py); the kernel
checks all three. This says nothing about the paper's own check.

### B. Certificates

The certificate files are generated by scripts/gen_schur.py (SchurCertV.lean, SchurCertH.lean) and
scripts/gen_margins.py (SchurCertR.lean, RoucheCert.lean) from the paper's tex and the pair data file. Python only
proposes the data. Lean's kernel checks every step (`decide +kernel` on exact Gaussian rationals); no native code and
no new axiom is used.

### C. Retired rows

RETIRED (proved and kept; the paper no longer states them; not counted): ctrl_dieudonne_scale, ctrl_s_minus_one,
ctrl_margin_c, ctrl_pm_one, ctrl_R_fails, ctrl_D_fails. They are the control of tex v1.90 l.439-442, which v2.90
moved to pair_checks/README.md. The first part of ctrl_margin_c still backs the numerical sentence of Remark 5.2 (N7).

## From the old README

For v2.90 of "Smale's mean value constant exceeds 1.1559" by Dave Goel.

[AUDIT.md](AUDIT.md) lists 84 claims: 77 proved from Lean's standard foundations and 7 proved assuming fact (R) of Theorem 5.1. Six of them are the paper's main results, Theorems 1.1 and 5.1 and Corollary 5.4, each stated twice (once from (R) as the paper states it, once from the exact statement the program checks); the other is Remark 5.2's sentence on where the zeros lie. Fact (R) itself is proved in Lean (`condR_proved`, Smale/Paper/Unconditional.lean), so these seven rows' claims also have rows with no hypothesis (`thm_1_1`, `thm_5_1`, `cor_5_4`, `rem_5_2_zeros_outside_proved`). [The accompanying program](../pair_checks/check_pair.py) checks fact (R) as well, by the route the paper prints (`CheckR`, which stays checked by computer and NOT proved in Lean).

## Assumptions

The project declares no axiom. No Lean proof of a theorem of the paper takes a result of another paper as given. The first sentence of each of Jatar and Ng's Propositions 3.1 and 4.2 (arXiv:2610.21472v2, an unrefereed preprint), and the "if" direction of Dieudonné's criterion (1931, in the form of Jatar and Ng's Lemma 6.3), which is all the paper uses of them, are proved in this project. Three rows state the paper's own deduction from another paper's result, with that result as their hypothesis: `intro_smale_K4`, `intro_conjecture_false`, `intro_AC_degree`. The main theorems do not assume (R): `condR_proved` proves that the resultant F(c) of the Dieudonné polynomial P_c of H and its reflection P_c* has no zero for c in [-1, 1]. The statement `CheckR`, which adds that F has real coefficients and degree 578, stays checked by computer, NOT proved in Lean.

The three standard axioms are `propext`, `Classical.choice` and `Quot.sound`. Every row's `#print axioms` lists only these; the rows marked PROVED-ASSUMING-(R) also take (R) as a hypothesis.

## Scope

The audit lists claims from the numbered results, proofs and running text. Its final sections record seven notes on where the Lean proofs take another path (A3 is on the control that v2.90 moved to pair_checks/README.md), and sentences without a Lean theorem. These include reports of other authors' results, descriptions of the programs, and the numerical observation about where the closest approach occurs. The steps needing a Riemann map are inside the proof of Proposition 3.1 (note A4). The overview at tex l.149-155 and the pointer to Crane at tex l.487-488 repeat what later rows and N items state; they have no row of their own.

Fact (R) is proved in Lean by a route of its own (note A7), and the program checks it as well. Facts (D), (C) and (S), and the stated margins in Remark 5.2, are proved in Lean by exact arithmetic. Paper line references are to v2.90; those marked v1.90 are to text that v2.90 moved to pair_checks/README.md.

Lean v4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned in the toolchain and dependency files. [Smale/Paper/Statements.lean](Smale/Paper/Statements.lean) contains the claims. Optional independent kernel checks are available through `scripts/kernel_replay.sh`, with the checker binaries it names. Its plain run covers every module except fact (R)'s, with all six checkers. Fact (R)'s modules have their own flag, `--r`, which names its checkers; con-leche and con-ron are too slow on these numbers to take all of them; `--names` runs them on a stated sample, such as scripts/r_sample.txt. In our run nanoda did not finish on either export: with the default 8 MB stack it overflows and aborts, and with a 1 GiB stack it was stopped for memory at a cap of 25 GB. It refused no declaration, but it did not check these files, so expect the plain run to report nanoda as FAIL and exit 1; the other five checkers passed that run. On fact (R)'s modules leanchecker, its paranoid mode and lean4lean passed. On scripts/r_sample.txt con-leche and con-ron each stopped at the script's 40-minute limit, which it reports as SKIPPED; on its hardest interval alone, `Smale.RK.t_524287_19`, each passed in about 15 minutes.

## From the old folder README

An expanded version of the paper, with many other results, is on Zenodo: https://doi.org/10.5281/zenodo.23597020

- pairs/pair_I_K2N18.json: the exact data of the pair (W, B) that proves the paper's main theorem.
- pair_checks/check_pair.py: the program that checks the pair; pair_checks/check_pair.log: the output of its run.
- pair_checks/make_controls.py, pair_checks/controls.log: wrong inputs that the program must reject, and the output.
  pairs/pair_XVII_T6.json is a small pair used only by these controls.
- rebuild_from_printed.py: checks that the numbers printed in the paper (its LaTeX source) give this data.
- lean/: a Lean 4 check of the paper (Lean v4.35.0, Mathlib commit 56a005855ea1). It proves every theorem, lemma and corollary of the paper, with no computer check
  as a hypothesis. Fact (R) of Theorem 5.1 is also checked by computer, by the route the paper prints (pair_checks/check_pair.py).
  lean/AUDIT.md lists every claim of the paper with its status.

and, in this folder, with the paper's LaTeX source as the first argument:

    python3 rebuild_from_printed.py <the paper's .tex file> pairs/pair_I_K2N18.json

All lemma, theorem and table numbers in check_pair.py refer to the expanded version: its Lemma 8.6, Lemma 7.11 and (C')
are Lemma 4.3, Lemma 4.2 and (C) of the paper, and its polynomial R and number J are V and Λ. In the output of
check_pair.py --test, the line "CONTROL WRONG" is expected: one test checks that a missing file is reported as an error.
