# How the programs make the checks of Theorem 5.1

The proof of Theorem 5.1 of the paper says what is computed. This page says which program computes it, and gives the details
the paper leaves out.

## How to run

With Python 3 and python-flint 0.9.0; the first command takes about eight minutes on one core. In this folder:

    python3 check_pair.py ../pairs/pair_I_K2N18.json --bound 1.1559837

and, in the folder above, with the paper's LaTeX source as the first argument:

    python3 rebuild_from_printed.py <the paper's .tex file> pairs/pair_I_K2N18.json

In the output of `check_pair.py --test`, the line "CONTROL WRONG" is expected: one test checks that a missing file is reported
as an error.

## The programs

- `check_pair.py` reads b, a_1, a_2, Q, Q' and H from `../pairs/pair_I_K2N18.json` and makes the checks (D), (C), (R) and (S).
  Its output is in `check_pair.log`.
- `../rebuild_from_printed.py` starts from the numbers printed in the paper. It solves the linear system for (g_0, g_1) exactly
  and checks that the printed numbers give exactly the b, a_1, a_2, Q, Q' and H of the data file.

`check_pair.py` and its output use the numbering of the expanded version of the paper: their Lemma 8.6, Lemma 7.11 and (C') are
Lemma 4.3, Lemma 4.2 and (C) of the paper, and their polynomial R and number J are V and Lambda.

## Checks (C) and (S): keeping the numbers small

In the Schur-Cohn test of Lemma 4.2 the program divides each f_j by its constant term delta_j > 0 before the next step. For
lambda > 0, T(lambda f) = lambda^2 T f, so this changes no later sign. Without it the numbers double in size at each step: on H',
delta_13 already has millions of digits.

## Check (R): how the determinant is computed

The program evaluates the determinant of the 34 x 34 Sylvester matrix at the integer points c = 0, 1, ..., 580, modulo each of
the 1128 largest primes below 2^62 that are congruent to 1 modulo 4.

For each such prime, -1 has a square root r modulo the prime. A Gaussian integer reduces, under i -> r and i -> -r, to two
residues that determine its real and imaginary parts modulo the prime.

Every row of the Sylvester matrix contains each coefficient of P_c or of P_c^* once. So by Hadamard's inequality the real and
imaginary parts of the determinant at each point are at most M^17 in absolute value, where M is the largest squared row norm
over the 581 points. The product of the primes exceeds 4 M^17, so the Chinese remainder theorem gives the values exactly.

## A control: the program can say no

The program rejects the data with H(z) replaced by H(sz), where s = 1250009/1250000. The Dieudonne polynomials of H(sz) are
s P_c(sw), so this divides all their zeros by s. As s - 1 = 7.2e-6 exceeds the margin 7.03e-6 near c = +-0.9231 but not the
margin at c = +-1, check (R) should fail, and the program proves that it does: for these data the resultant in (R) has a zero
in [-1, 1]. Check (D) fails too, since H(sz) no longer matches Q.

`make_controls.py` makes this and the other wrong inputs. Their output is in `controls.log`.
