# The Osserman (1990) conjecture is fully resolved — notes on the Lean proof

## Read this first: Lean does not check the paper's main result

Theorem A of the paper (the Nikolayevsky (2009) conjecture), Corollary B and Remark 1.1 are not formalized. So the
title and the main claim of the abstract are not checked by Lean. The proof of Theorem A uses Sections 9–27 of the
paper. They need complex projective algebraic geometry, divisor class groups, real semialgebraic sets and algebraic
topology, which Lean's mathematics library (Mathlib) does not have. Corollary B is about Riemannian manifolds; Mathlib
has no curvature tensor of a manifold, so Lean cannot state it.

## What Lean checks

Every other claim of Sections 1–8 (Theorems C, E, F and Corollary D, with all their steps; the exceptions are
listed under "Not part of the check"), and six pieces of Sections
9–27: Setting (T), Lemmas 12.1, 12.4, 12.5 and 12.6, the anisotropy step inside the proof of Theorem G, and Lemma
24.5. Theorem G itself, and the facts these six pieces take from Sections 9, 10 and 27, are not formalized. Lean
checked version 4.00 of the paper. Line numbers refer to its LaTeX source: the main file P013_short.tex
(MD5 6e130b9592d813067ed9e12359d97d99) and the section files it inputs.

That makes 351 claims of the paper: 299 proved from Lean's three standard axioms alone, and 52
proved from eight cited published results; none is open. No claim rests on a computer calculation. One of the eight
cited results, the classification of isoparametric hypersurfaces written with polynomials, also contains about one
page of the paper's own Section 3 argument (it turns hypersurfaces into polynomials), which Lean cannot express; that
page is not checked.

## The cited results

The 52 claims rest on these eight statements, each written out in [Osserman/Cited/](Osserman/Cited/):

1. The classification of isoparametric hypersurfaces on R^32, in polynomial form: Münzner, Math. Ann. 251 (1980);
   Ferus, Karcher and Münzner, Math. Z. 177 (1981); Chi, J. Differential Geom. 115 (2020).
2. Symmetric Clifford systems of nine 16×16 matrices are unique up to orthogonal conjugacy and the sign of one
   generator: Ferus, Karcher and Münzner (1981), Sections 3.4–3.5; Nikolayevsky, Ann. Mat. Pura Appl. 191 (2012).
3. Nikolayevsky, "On Osserman manifolds of dimension 16", conference proceedings, Belgrade 2006, Lemma 3.1; the same
   statement is Lemma 2 of Nikolayevsky, Manuscripta Math. 115 (2004).
4. The same 2006 article, Lemma 3.11.
5. The same 2006 article, Theorem 3.1: R[x_1, …, x_16]/(|x|^2) is a unique factorization domain (Nagata's theorem,
   J. Math. Soc. Japan 9 (1957)).
6. The same 2006 article, Proposition 2.1.
7. Nikolayevsky, Math. Ann. 331 (2005), Proposition 1.
8. Andrejić and Lukić, Filomat 37 (2023), Theorem 3 (= Andrejić, J. Geom. Phys. 176 (2022), Theorem 5).

Two of them, 4 and 6, rest only on the 2006 proceedings article, whose refereeing is not stated; the others are in
refereed journals.

## Not part of the check

Besides Theorem A, Corollary B and Remark 1.1: Nikolayevsky's announced manifold theorem and the multiplicities of
CP^8, HP^4 and their duals; that R_Cay is the curvature tensor of the Cayley plane (Lean takes the Brown–Gray formula
as its definition; its normalization is proved); the isomorphism Cl⁺(9) ≅ M16(R) ⊕ M16(R) (only its consequence,
result 2 above, is used); the Section 3 page inside result 1; sentences that only report other papers.
[AUDIT.md](AUDIT.md) lists each with its lines.

## Where each claim is

[AUDIT.md](AUDIT.md) lists every claim with its place in the paper and the axioms Lean reports for its proof
(`#print axioms`); [Osserman/Paper/Statements.lean](Osserman/Paper/Statements.lean) has one Lean theorem per claim.
In four places Lean takes another route than the text (Lemma 4.1, the rotations of Sections 4–5, Remark 7.2,
Lemma 8.1); there the paper's own steps are also proved as separate claims. Line 474 of P013_short.tex uses
ΔF_P = (136 − 16(m+1))s, which needs the hypothesis m ≥ 1 of line 447; the Lean statements carry m ≥ 1, which
result 1 provides.

`scripts/kernel_replay.sh` re-checks every declaration with independent checkers (listed at the top of the script).

Versions: Lean 4.35.0 (pinned in `lean-toolchain`); Mathlib commit `56a005855ea1` (all dependencies pinned in
`lake-manifest.json`).
