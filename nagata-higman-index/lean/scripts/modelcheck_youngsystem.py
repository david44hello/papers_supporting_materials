#!/usr/bin/env python3
# modelcheck_youngsystem.py — exact model check of `structure YoungSystem` (NagataHigmanLean) on Young's seminormal form.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
"""Exact-arithmetic model check of the cited statement `NagataHigman.Cited.youngSystem_exists`.

The model: for every shape lam |- N, rho_lam = Young's seminormal form on the standard tableaux of shape lam (rational
matrices). Every one of the 6 property fields of `structure YoungSystem` (NagataHigman/Defs/YoungSystem.lean) is checked
as the Lean text reads, in the Lean conventions:
  * points and tableau entries 0..N-1; product (sigma*tau)(i) = sigma(tau(i)) (Mathlib `Equiv.Perm`);
  * J_k = sum_{i<k} (i k)  (`jucysMurphy`; J_0 = 0);  content = column - row of the cell holding k, cells (row, col) 0-indexed;
  * shapes = partitions of N; lam' = Mathlib `Nat.Partition.conjugate` (column lengths);
  * sigma.partition.parts = Mathlib `Equiv.Perm.partition` = cycle type INCLUDING fixed points;
  * diagonalHooks(lam) = multiset of rowLen i + colLen i - 2i - 1 over diagonal cells (i,i);
  * SYT lam = Lean structure `SYT` literally (pos injective into the cells, pos_mono), enumerated by brute force.

Rigour notes (why each PASS is a proof for the stated N, not a sample):
  (a) rho is DEFINED on all of S_N by breadth-first search from the generators s_k = (k k+1); checking
      rho(s_k * sigma) = rho(s_k) rho(sigma) on every Cayley edge, plus rho(id) = I, proves rho is a homomorphism.
      All pairs are additionally checked for N <= PAIRS_MAX_N, and the Coxeter relations for every N.
  (b) square: sum_lam (f^lam)^2 = N!; full rank: exact over Q for N <= EXACT_RANK_MAX_N, else rank mod PRIME
      (rank mod p <= rank over Q, so full rank mod p proves full rank over Q, hence over every char-0 field F).
      Independently, (c) on the basis gives an explicit left inverse, which with "square" proves bijectivity.
  (c) the identity is linear in a, so the check on every basis element tau (sum_lam f^lam chi_lam(g) = N! [g = id]) is a
      proof; random integer a are checked literally as well.
  (e) span <= commutant is checked exactly (every rho(sigma), sigma(top) = top, commutes with rho(J_top)); then
      dim span = dim commutant (span rank exact, or mod PRIME = a lower bound) gives equality, i.e. both inclusions.
  (f),(g) a relation G A(s_k) = eps B(s_k) G on the generators implies it for every sigma (both sides are multiplicative).
      Summing it over the transpositions in J_k gives G J^A_k = eps J^B_k G; with J diagonal (field (d)) this FORCES
      G[a][b] = 0 unless J^A_k[b][b] = eps J^B_k[a][a] for all k. So solving on that support gives the WHOLE solution
      space. For N <= FULL_UNKNOWN_MAX_N the unrestricted system (all d*d' unknowns) is solved too, as a cross-check.
      (g) is linear in Gamma, so checking a basis of the solution space checks EVERY Gamma.
  (i) commutant of {Y_j}: exact for small dim; for (3,3,2) (dim 42) the F_p-commutant dimension (an UPPER bound for the
      Q-commutant dimension) is computed; value 1 (scalars are always there) proves the commutant is the scalars.

Run:   nice -n 19 taskset -c 12 python3 scripts/modelcheck_youngsystem.py            (N = 0..6, then (3,3,2))
       ... --maxN 5 | --test (quick: N <= 3, negative controls, paper probe on (2,1) only)
"""
import argparse
import itertools
import math
import random
import sys
import time
from fractions import Fraction

import numpy as np

ZERO = Fraction(0)
ONE = Fraction(1)
PRIME = 16777213          # largest prime below 2**24: residue products < 2**48, sums of < 2**15 of them fit in int64
EXACT_RANK_MAX_N = 5      # ranks over Q (Fractions) up to this N; above it, rank mod PRIME (a LOWER bound for rank over Q)
PAIRS_MAX_N = 4           # (a): rho(sigma tau) = rho(sigma) rho(tau) for ALL pairs up to this N
FULL_UNKNOWN_MAX_N = 5    # (f),(g): also solve with all d*d' unknowns up to this N
SMALL_COMMUTANT_DIM = 8   # (i): exact commutant up to this dim, F_p-commutant above
RANDOM_SEED = 20261026
RANDOM_TRIALS = 3
RANDOM_COEFF = 9
PAPER_SHAPES = ((2, 1), (3, 3, 2))
KUZMIN_NS = (2, 3)        # (j): n = 4 would need V_9, dim 9! — out of reach here
FIELDS = ("a", "b", "c", "d", "e", "f", "g")
FIELD_NAMES = {"a": "rho homomorphism", "b": "wedderburn", "c": "fourier", "d": "youngBasis", "e": "restriction (historical: no longer an axiom clause; now PROVED in Lean)",
               "f": "signTwist", "g": "frobenius (historical: no longer an axiom clause; see altsplit_check.py)"}
MAX_SHOWN_PROBLEMS = 3


# ----------------------------------------------------------------------------------------------- permutations
def compose(sigma, tau):
    """Lean/Mathlib product: (sigma * tau)(i) = sigma(tau(i))."""
    return tuple(sigma[tau[point]] for point in range(len(tau)))


def inverse(sigma):
    images = [0] * len(sigma)
    for point, image in enumerate(sigma):
        images[image] = point
    return tuple(images)


def swap_perm(n, first, second):
    images = list(range(n))
    images[first], images[second] = second, first
    return tuple(images)


def cycle_lengths(sigma):
    seen = [False] * len(sigma)
    lengths = []
    for start in range(len(sigma)):
        length, point = 0, start
        while not seen[point]:
            seen[point] = True
            point = sigma[point]
            length += 1
        if length:
            lengths.append(length)
    return lengths


def perm_partition(sigma):
    """Mathlib `sigma.partition.parts` = cycleType + replicate (card - #support) 1: all cycle lengths, fixed points incl."""
    return tuple(sorted(cycle_lengths(sigma), reverse=True))


def cycle_type_without_fixed_points(sigma):
    """Mathlib `sigma.cycleType` (NO 1-cycles) — used only by a negative control."""
    return tuple(length for length in perm_partition(sigma) if length > 1)


def perm_sign(sigma):
    return -1 if (len(sigma) - len(cycle_lengths(sigma))) % 2 else 1


# ----------------------------------------------------------------------------------------------- shapes, tableaux
def partitions(n, max_part=None):
    if max_part is None:
        max_part = n
    if n == 0:
        yield ()
        return
    for part in range(min(n, max_part), 0, -1):
        for rest in partitions(n - part, part):
            yield (part,) + rest


def row_len(shape, row):
    return shape[row] if row < len(shape) else 0


def col_len(shape, col):
    return sum(1 for part in shape if part > col)


def conjugate(shape):
    """Mathlib `Nat.Partition.conjugate` (transpose of the Young diagram): parts = column lengths."""
    return tuple(col_len(shape, col) for col in range(shape[0])) if shape else ()


def cells_of(shape):
    return [(row, col) for row, part in enumerate(shape) for col in range(part)]


def diagonal_hooks(shape):
    """Lean `Shape.diagonalHooks`: i in range N with (i,i) a cell, value rowLen i + colLen i - 2i - 1 (in ℕ)."""
    cells = set(cells_of(shape))
    hooks = [max(0, row_len(shape, idx) + col_len(shape, idx) - 2 * idx - 1)
             for idx in range(sum(shape)) if (idx, idx) in cells]
    return tuple(sorted(hooks, reverse=True))


def syt_recursive(shape):
    """Standard tableaux as tuples pos (pos[k] = (row, col) of entry k), entries placed in order 0..N-1."""
    total, found, filled, pos = sum(shape), [], [0] * len(shape), []

    def extend():
        if len(pos) == total:
            found.append(tuple(pos))
            return
        for row in range(len(shape)):
            col = filled[row]
            if col < shape[row] and (row == 0 or filled[row - 1] > col):
                pos.append((row, col))
                filled[row] += 1
                extend()
                filled[row] -= 1
                pos.pop()

    extend()
    return found


def is_pos_mono(pos):
    """Lean `SYT.pos_mono`: (pos k).1 <= (pos l).1 -> (pos k).2 <= (pos l).2 -> k <= l."""
    size = len(pos)
    return all(first <= second for first in range(size) for second in range(size)
               if pos[first][0] <= pos[second][0] and pos[first][1] <= pos[second][1])


def syt_lean_definition(shape):
    """Lean `SYT lam` literally: pos injective into the N cells (hence a bijection onto them) with pos_mono."""
    return [pos for pos in itertools.permutations(cells_of(shape)) if is_pos_mono(pos)]


def content(pos, entry):
    """Lean `SYT.content`: column - row of the cell holding `entry`."""
    return pos[entry][1] - pos[entry][0]


def hook_length_count(shape):
    cells = cells_of(shape)
    product = 1
    for row, col in cells:
        product *= (shape[row] - col - 1) + (col_len(shape, col) - row - 1) + 1
    return math.factorial(len(cells)) // product


# ----------------------------------------------------------------------------------------------- exact matrices
def zero_matrix(rows, cols):
    return [[ZERO] * cols for _ in range(rows)]


def identity(dim):
    return [[ONE if row == col else ZERO for col in range(dim)] for row in range(dim)]


def diagonal(values):
    dim = len(values)
    return [[Fraction(values[row]) if row == col else ZERO for col in range(dim)] for row in range(dim)]


def matmul(left, right):
    right_cols = list(zip(*right))
    return [[sum((x * y for x, y in zip(row, col)), ZERO) for col in right_cols] for row in left]


def mat_add(left, right):
    return [[x + y for x, y in zip(row_l, row_r)] for row_l, row_r in zip(left, right)]


def mat_scale(scalar, mat):
    return [[scalar * x for x in row] for row in mat]


def trace(mat):
    return sum((mat[idx][idx] for idx in range(len(mat))), ZERO)


def trace_of_product(left, right):
    return sum((left[row][mid] * right[mid][row] for row in range(len(left)) for mid in range(len(right))), ZERO)


def is_diagonal(mat):
    return all(mat[row][col] == 0 for row in range(len(mat)) for col in range(len(mat[row])) if row != col)


def nonzero_rows(mat):
    return [[(col, value) for col, value in enumerate(row) if value != 0] for row in mat]


def nonzero_cols(mat):
    return nonzero_rows([list(col) for col in zip(*mat)])


def left_mul_sparse(left_rows, right):
    """left * right, with left given by nonzero_rows."""
    ncols = len(right[0])
    product = []
    for entries in left_rows:
        row = [ZERO] * ncols
        for mid, value in entries:
            source = right[mid]
            for col in range(ncols):
                if source[col]:
                    row[col] += value * source[col]
        product.append(row)
    return product


def right_mul_sparse(left, right_cols):
    """left * right, with right given by nonzero_cols."""
    return [[sum((row[mid] * value for mid, value in entries), ZERO) for entries in right_cols] for row in left]


# ----------------------------------------------------------------------------------------------- linear algebra
def rref_exact(rows, ncols):
    work = [list(row) for row in rows]
    pivots, prow = [], 0
    for col in range(ncols):
        if prow == len(work):
            break
        piv = next((idx for idx in range(prow, len(work)) if work[idx][col] != 0), None)
        if piv is None:
            continue
        work[prow], work[piv] = work[piv], work[prow]
        lead = work[prow][col]
        work[prow] = [value / lead for value in work[prow]]
        for idx in range(len(work)):
            if idx != prow and work[idx][col] != 0:
                factor, pivot_row = work[idx][col], work[prow]
                work[idx] = [value - factor * pval for value, pval in zip(work[idx], pivot_row)]
        pivots.append(col)
        prow += 1
    return work[:prow], pivots


def rank_exact(rows, ncols):
    return len(rref_exact(rows, ncols)[1])


def nullspace_exact(rows, ncols):
    reduced, pivots = rref_exact(rows, ncols)
    pivot_set = set(pivots)
    basis = []
    for free in (col for col in range(ncols) if col not in pivot_set):
        vec = [ZERO] * ncols
        vec[free] = ONE
        for idx, pcol in enumerate(pivots):
            vec[pcol] = -reduced[idx][free]
        basis.append(vec)
    return basis


def to_mod_p(value):
    value = Fraction(value)
    assert value.denominator % PRIME != 0, ("denominator divisible by PRIME", value)
    return value.numerator * pow(value.denominator, -1, PRIME) % PRIME


def matrix_mod_p(rows):
    return np.array([[to_mod_p(value) for value in row] for row in rows], dtype=np.int64).reshape(len(rows), -1)


def rref_mod_p(matrix):
    work = matrix.copy() % PRIME
    nrows, ncols = work.shape
    pivots, prow = [], 0
    for col in range(ncols):
        if prow == nrows:
            break
        nonzero = np.nonzero(work[prow:, col])[0]
        if nonzero.size == 0:
            continue
        piv = prow + int(nonzero[0])
        if piv != prow:
            work[[prow, piv]] = work[[piv, prow]]
        work[prow, col:] = (work[prow, col:] * pow(int(work[prow, col]), -1, PRIME)) % PRIME
        others = np.nonzero(work[:, col])[0]
        others = others[others != prow]
        if others.size:
            update = np.outer(work[others, col], work[prow, col:]) % PRIME
            work[np.ix_(others, np.arange(col, ncols))] = (work[others, col:] - update) % PRIME
        pivots.append(col)
        prow += 1
    return work[:prow], pivots


def rank_mod_p(rows):
    return len(rref_mod_p(matrix_mod_p(rows))[1])


def nullspace_mod_p(matrix):
    reduced, pivots = rref_mod_p(matrix)
    ncols = matrix.shape[1]
    pivot_set = set(pivots)
    free_cols = [col for col in range(ncols) if col not in pivot_set]
    basis = np.zeros((len(free_cols), ncols), dtype=np.int64)
    for out_row, free in enumerate(free_cols):
        basis[out_row, free] = 1
        for idx, pcol in enumerate(pivots):
            basis[out_row, pcol] = (-reduced[idx, free]) % PRIME
    return basis


def rank_any(rows, ncols, n):
    """Exact rank over Q for n <= EXACT_RANK_MAX_N, else rank mod PRIME (a lower bound for the rank over Q)."""
    if not rows:
        return 0, "exact"
    if n <= EXACT_RANK_MAX_N:
        return rank_exact(rows, ncols), "exact over Q"
    return rank_mod_p(rows), f"mod {PRIME} (lower bound for rank over Q)"


# ----------------------------------------------------------------------------------------------- the model
def seminormal_generators(tableaux, n):
    """Young's seminormal form: rho(s_k) v_T = (1/r) v_T + c v_{s_k T}, r = c_T(k+1) - c_T(k), c = 1 if r > 0 else 1 - 1/r^2.
    Matrix column a = image of v_{T_a}."""
    index = {pos: idx for idx, pos in enumerate(tableaux)}
    dim = len(tableaux)
    gens = []
    for kk in range(n - 1):
        mat = zero_matrix(dim, dim)
        for col, pos in enumerate(tableaux):
            axial = content(pos, kk + 1) - content(pos, kk)
            mat[col][col] = Fraction(1, axial)
            swapped = list(pos)
            swapped[kk], swapped[kk + 1] = pos[kk + 1], pos[kk]
            row = index.get(tuple(swapped))
            if row is not None:
                mat[row][col] = ONE if axial > 0 else ONE - Fraction(1, axial * axial)
        gens.append(mat)
    return gens


def all_rho(gen_rows, n, dim):
    """rho on all of S_N by BFS: rho(s_k * sigma) := rho(s_k) rho(sigma) at first visit (consistency checked in (a))."""
    ident = tuple(range(n))
    rho = {ident: identity(dim)}
    gen_perms = [swap_perm(n, kk, kk + 1) for kk in range(n - 1)]
    frontier = [ident]
    while frontier:
        next_frontier = []
        for sigma in frontier:
            for kk, gen in enumerate(gen_perms):
                tau = compose(gen, sigma)
                if tau not in rho:
                    rho[tau] = left_mul_sparse(gen_rows[kk], rho[sigma])
                    next_frontier.append(tau)
        frontier = next_frontier
    assert len(rho) == math.factorial(n), ("BFS did not reach all of S_N", n, len(rho))
    return rho


def jucys_murphy_matrices(rho, n, dim):
    """rho(J_k) = sum_{i<k} rho((i k)), computed from rho itself (J_0 = 0)."""
    mats = []
    for kk in range(n):
        total = zero_matrix(dim, dim)
        for ii in range(kk):
            total = mat_add(total, rho[swap_perm(n, ii, kk)])
        mats.append(total)
    return mats


def build_model(shape, n):
    tableaux = syt_recursive(shape)
    dim = len(tableaux)
    gens = seminormal_generators(tableaux, n)
    gen_rows = [nonzero_rows(gen) for gen in gens]
    rho = all_rho(gen_rows, n, dim)
    return {"shape": shape, "dim": dim, "tableaux": tableaux, "lean_tableaux": syt_lean_definition(shape),
            "gens": gens, "gen_rows": gen_rows, "rho": rho, "jm": jucys_murphy_matrices(rho, n, dim)}


# ----------------------------------------------------------------------------------------------- verdict helper
def verdict(problems, instances, note=""):
    if problems:
        shown = "; ".join(problems[:MAX_SHOWN_PROBLEMS])
        more = f" (+{len(problems) - MAX_SHOWN_PROBLEMS} more)" if len(problems) > MAX_SHOWN_PROBLEMS else ""
        return {"ok": False, "instances": instances, "detail": shown + more}
    return {"ok": True, "instances": instances, "detail": note}


# ----------------------------------------------------------------------------------------------- (a) homomorphism
def coxeter_problems(gens, dim, label):
    problems = []
    ident = identity(dim)
    gen_rows = [nonzero_rows(gen) for gen in gens]
    for kk, gen in enumerate(gens):
        if left_mul_sparse(gen_rows[kk], gen) != ident:
            problems.append(f"{label}: s_{kk}^2 != I")
        for ll in range(kk + 1, len(gens)):
            if ll == kk + 1:
                lhs = left_mul_sparse(gen_rows[kk], left_mul_sparse(gen_rows[ll], gen))
                rhs = left_mul_sparse(gen_rows[ll], left_mul_sparse(gen_rows[kk], gens[ll]))
                if lhs != rhs:
                    problems.append(f"{label}: braid s_{kk} s_{ll}")
            elif left_mul_sparse(gen_rows[kk], gens[ll]) != left_mul_sparse(gen_rows[ll], gen):
                problems.append(f"{label}: s_{kk} s_{ll} != s_{ll} s_{kk}")
    return problems


def check_hom(models, n, perms):
    problems, instances = [], 0
    ident = tuple(range(n))
    gen_perms = [swap_perm(n, kk, kk + 1) for kk in range(n - 1)]
    for shape, model in models.items():
        rho = model["rho"]
        if rho[ident] != identity(model["dim"]):
            problems.append(f"{shape}: rho(id) != I")
        problems += coxeter_problems(model["gens"], model["dim"], str(shape))
        for sigma in perms:
            for kk, gen in enumerate(gen_perms):
                instances += 1
                if rho[compose(gen, sigma)] != left_mul_sparse(model["gen_rows"][kk], rho[sigma]):
                    problems.append(f"{shape}: Cayley edge s_{kk}*{sigma}")
        if n <= PAIRS_MAX_N:
            for sigma, tau in itertools.product(perms, perms):
                instances += 1
                if rho[compose(sigma, tau)] != matmul(rho[sigma], rho[tau]):
                    problems.append(f"{shape}: rho({sigma}*{tau}) != rho rho")
    how = "all pairs + Cayley edges + Coxeter" if n <= PAIRS_MAX_N else "Cayley edges + Coxeter (a proof)"
    return verdict(problems, instances, how)


# ----------------------------------------------------------------------------------------------- (b) wedderburn
def check_wedderburn(models, n, perms):
    total = sum(model["dim"] ** 2 for model in models.values())
    problems = [] if total == math.factorial(n) else [f"not square: sum f^2 = {total} != N! = {math.factorial(n)}"]
    rows = [[value for model in models.values() for row in model["rho"][sigma] for value in row] for sigma in perms]
    rank, how = rank_any(rows, total, n)
    if rank != len(perms):
        problems.append(f"rank {rank} != N! = {len(perms)} ({how})")
    return verdict(problems, 1, f"sum f^2 = {total} = N!, rank {rank} ({how})")


# ----------------------------------------------------------------------------------------------- (c) fourier
def fourier_basis_problems(models, n, perms):
    problems = []
    for sigma in perms:
        value = sum((model["dim"] * trace(model["rho"][sigma]) for model in models.values()), ZERO)
        expected = math.factorial(n) if sigma == tuple(range(n)) else 0
        if value != expected:
            problems.append(f"sum_lam f chi_lam({sigma}) = {value} != {expected}")
    return problems


def fourier_random_problems(models, n, perms, rng, dims):
    problems = []
    coeff = {sigma: rng.randint(-RANDOM_COEFF, RANDOM_COEFF) for sigma in perms}
    rho_a = {}
    for shape, model in models.items():
        total = zero_matrix(model["dim"], model["dim"])
        for tau in perms:
            if coeff[tau]:
                total = mat_add(total, mat_scale(coeff[tau], model["rho"][tau]))
        rho_a[shape] = total
    for sigma in perms:
        sigma_inv = inverse(sigma)
        rhs = sum((Fraction(dims[shape], math.factorial(n)) * trace_of_product(model["rho"][sigma_inv], rho_a[shape])
                   for shape, model in models.items()), ZERO)
        if rhs != coeff[sigma]:
            problems.append(f"a({sigma}) = {coeff[sigma]} but Fourier gives {rhs}")
    return problems


def check_fourier(models, n, perms, dims=None):
    if dims is None:
        dims = {shape: model["dim"] for shape, model in models.items()}
    rng = random.Random(RANDOM_SEED + n)
    problems = [] if dims != {shape: model["dim"] for shape, model in models.items()} else \
        fourier_basis_problems(models, n, perms)
    trials = RANDOM_TRIALS if n <= EXACT_RANK_MAX_N else 1
    for _ in range(trials):
        problems += fourier_random_problems(models, n, perms, rng, dims)
    return verdict(problems, len(perms) * (trials + 1), f"all basis elements (a proof) + {trials} random integer a")


# ----------------------------------------------------------------------------------------------- (d) youngBasis
def check_young_basis(models, n, content_sign=1):
    problems, instances = [], 0
    for shape, model in models.items():
        lean_set, rec_set = set(model["lean_tableaux"]), set(model["tableaux"])
        if lean_set != rec_set or len(lean_set) != model["dim"] or model["dim"] != hook_length_count(shape):
            problems.append(f"{shape}: #SYT(Lean def) {len(lean_set)} vs dim {model['dim']}")
        vectors = [tuple(content(pos, kk) for kk in range(n)) for pos in model["tableaux"]]
        if len(set(vectors)) != len(vectors):
            problems.append(f"{shape}: content vectors not distinct")
        for kk in range(n):
            instances += model["dim"]
            expected = diagonal([content_sign * content(pos, kk) for pos in model["tableaux"]])
            if model["jm"][kk] != expected:
                problems.append(f"{shape}: rho(J_{kk}) != diag(content(T,{kk}))")
    return verdict(problems, instances, "#SYT(Lean def) = f^lam; rho(J_k) = diag(c_T(k)) for all T, k")


# ----------------------------------------------------------------------------------------------- (e) restriction
def commutant_dim_exact(mat):
    dim = len(mat)
    rows = []
    for row in range(dim):
        for col in range(dim):
            eq = [ZERO] * (dim * dim)
            for mid in range(dim):      # (X M - M X)[row][col] = sum X[row][mid] M[mid][col] - M[row][mid] X[mid][col]
                eq[row * dim + mid] += mat[mid][col]
                eq[mid * dim + col] -= mat[row][mid]
            rows.append(eq)
    return dim * dim - rank_exact(rows, dim * dim)


def commutant_dim_diagonal(mat):
    values = [mat[idx][idx] for idx in range(len(mat))]
    return sum(values.count(value) ** 2 for value in set(values))


def check_restriction(models, n, perms, top=None):
    if n == 0:
        return verdict([], 0, "vacuous: no top : Fin 0")
    top = n - 1 if top is None else top
    problems, notes = [], []
    stab = [sigma for sigma in perms if sigma[top] == top]
    for shape, model in models.items():
        jm, dim = model["jm"][top], model["dim"]
        bad = [sigma for sigma in stab if matmul(model["rho"][sigma], jm) != matmul(jm, model["rho"][sigma])]
        if bad:
            problems.append(f"{shape}: rho({bad[0]}) does not commute with rho(J_{top})")
        comm = commutant_dim_diagonal(jm) if is_diagonal(jm) else None
        if n <= EXACT_RANK_MAX_N:
            comm_exact = commutant_dim_exact(jm)
            if comm is not None and comm != comm_exact:
                problems.append(f"{shape}: commutant dims disagree {comm} vs {comm_exact}")
            comm = comm_exact
        span, how = rank_any([[value for row in model["rho"][sigma] for value in row] for sigma in stab], dim * dim, n)
        if comm is None or span != comm:
            problems.append(f"{shape}: dim span{{rho(Stab {top})}} = {span} ({how}) != dim commutant = {comm}")
        notes.append(f"{shape}:{span}={comm}")
    return verdict(problems, len(models), "dim span = dim commutant: " + " ".join(notes))


# ----------------------------------------------------------------------------------------------- (f),(g) intertwiners
def forced_support(target_jm, source_jm, dim_t, dim_s, eps, n):
    """G (target x source) with G J^S_k = eps J^T_k G and J diagonal: G[a][b] != 0 only if J^S_k[b][b] = eps J^T_k[a][a]."""
    assert all(is_diagonal(mat) for mat in target_jm + source_jm), "J not diagonal: support argument invalid"
    return [(row, col) for row in range(dim_t) for col in range(dim_s)
            if all(source_jm[kk][col][col] == eps * target_jm[kk][row][row] for kk in range(n))]


def intertwiner_basis(target_gens, source_gens, dim_t, dim_s, eps, support):
    """Exact basis of {G : G A_k = eps B_k G for all k}, A = source_gens, B = target_gens, G supported on `support`."""
    unknown = {pos: idx for idx, pos in enumerate(support)}
    rows = []
    for gen_s, gen_t in zip(source_gens, target_gens):
        for row in range(dim_t):
            for col in range(dim_s):
                eq = [ZERO] * len(support)
                for mid in range(dim_s):          # (G A)[row][col] = sum_mid G[row][mid] A[mid][col]
                    if (row, mid) in unknown and gen_s[mid][col]:
                        eq[unknown[(row, mid)]] += gen_s[mid][col]
                for mid in range(dim_t):          # - eps (B G)[row][col] = - eps sum_mid B[row][mid] G[mid][col]
                    if (mid, col) in unknown and gen_t[row][mid]:
                        eq[unknown[(mid, col)]] -= eps * gen_t[row][mid]
                if any(eq):
                    rows.append(eq)
    basis = nullspace_exact(rows, len(support)) if rows else [[ONE if idx == jdx else ZERO for jdx in range(len(support))]
                                                                for idx in range(len(support))]
    mats = []
    for vec in basis:
        mat = zero_matrix(dim_t, dim_s)
        for (row, col), idx in unknown.items():
            mat[row][col] = vec[idx]
        mats.append(mat)
    return mats


def solve_intertwiners(target, source, eps, n):
    """Whole solution space (via the J-forced support), cross-checked against all unknowns for small N."""
    support = forced_support(target["jm"], source["jm"], target["dim"], source["dim"], eps, n)
    basis = intertwiner_basis(target["gens"], source["gens"], target["dim"], source["dim"], eps, support)
    full_dim = None
    if n <= FULL_UNKNOWN_MAX_N:
        everything = [(row, col) for row in range(target["dim"]) for col in range(source["dim"])]
        full_dim = len(intertwiner_basis(target["gens"], source["gens"], target["dim"], source["dim"], eps, everything))
    return basis, full_dim


def intertwines_all(gamma, target, source, eps_of, perms):
    """G rho_S(sigma) = eps(sigma) rho_T(sigma) G for every sigma."""
    gamma_rows, gamma_cols = nonzero_rows(gamma), nonzero_cols(gamma)
    for sigma in perms:
        lhs = left_mul_sparse(gamma_rows, source["rho"][sigma])
        rhs = mat_scale(eps_of(sigma), right_mul_sparse(target["rho"][sigma], gamma_cols))
        if lhs != rhs:
            return sigma
    return None


def check_sign_twist(models, n, perms, eps=-1):
    problems, notes = [], []
    eps_of = (lambda sigma: perm_sign(sigma)) if eps == -1 else (lambda sigma: 1)
    for shape, model in models.items():
        source = models[conjugate(shape)]
        basis, full_dim = solve_intertwiners(model, source, eps, n)
        if full_dim is not None and full_dim != len(basis):
            problems.append(f"{shape}: support-restricted dim {len(basis)} != full dim {full_dim}")
        invertible = [gamma for gamma in basis if rank_exact(gamma, source["dim"]) == model["dim"] == source["dim"]]
        if not invertible:
            problems.append(f"{shape}: no invertible intertwiner (solution space dim {len(basis)})")
        for gamma in basis:
            bad = intertwines_all(gamma, model, source, eps_of, perms)
            if bad is not None:
                problems.append(f"{shape}: Gamma fails at sigma = {bad}")
        notes.append(f"{shape}->{conjugate(shape)}:dim{len(basis)}")
    return verdict(problems, len(models), "invertible Gamma, all sigma; solution-space dims " + " ".join(notes))


def frobenius_traces(model, gamma, perms):
    """For even sigma: partition -> (number of sigma, number with tr(rho(sigma) Gamma) != 0, set of nonzero values)."""
    table = {}
    for sigma in perms:
        if perm_sign(sigma) != 1:
            continue
        value = trace_of_product(model["rho"][sigma], gamma)
        entry = table.setdefault(perm_partition(sigma), [0, 0, set()])
        entry[0] += 1
        if value != 0:
            entry[1] += 1
            entry[2].add(value)
    return table


def frobenius_shape(model, n, perms, partition_of):
    shape = model["shape"]
    hooks = diagonal_hooks(shape)
    basis, full_dim = solve_intertwiners(model, model, -1, n)
    problems, constrained, notes = [], 0, []
    if full_dim is not None and full_dim != len(basis):
        problems.append(f"{shape}: support-restricted dim {len(basis)} != full dim {full_dim}")
    for gamma in basis:
        if intertwines_all(gamma, model, model, perm_sign, perms) is not None:
            problems.append(f"{shape}: basis Gamma is not an intertwiner")
        gamma_sq = matmul(gamma, gamma)
        scalar = gamma_sq[0][0]
        for sigma in perms:
            if perm_sign(sigma) == 1 and partition_of(sigma) != hooks:
                constrained += 1
                if trace_of_product(model["rho"][sigma], gamma) != 0:
                    problems.append(f"{shape}: tr(rho({sigma}) Gamma) != 0, partition {partition_of(sigma)} != h {hooks}")
        table = frobenius_traces(model, gamma, perms)
        nonzero = {part: (cnt, nz) for part, (cnt, nz, _) in table.items() if nz}
        eps_prod = (-1) ** ((n - len(hooks)) // 2) * math.prod(hooks)
        sq_ratio = {value * value / scalar for part, (_, _, vals) in table.items() if part == hooks for value in vals} \
            if scalar != 0 and gamma_sq == mat_scale(scalar, identity(model["dim"])) else "Gamma^2 not scalar"
        notes.append(f"{shape}: h={list(hooks)}, sol.dim={len(basis)}, nonzero at partitions {nonzero} "
                     f"(even sigma of that type, nonzero count); tr^2/Gamma^2 = {sq_ratio} vs eps*prod(h) = {eps_prod}")
    return problems, constrained, notes


def check_frobenius(models, n, perms, partition_of=perm_partition):
    problems, constrained, notes = [], 0, []
    selfconj = [shape for shape in models if conjugate(shape) == shape]
    for shape in selfconj:
        shape_problems, shape_constrained, shape_notes = frobenius_shape(models[shape], n, perms, partition_of)
        problems += shape_problems
        constrained += shape_constrained
        notes += shape_notes
    note = f"self-conjugate shapes {selfconj}; constrained (Gamma, sigma) instances = {constrained}"
    if notes:
        note += "\n        " + "\n        ".join(notes)
    return verdict(problems, constrained, note)


# ----------------------------------------------------------------------------------------------- per-N driver
def run_degree(n):
    start = time.time()
    perms = list(itertools.permutations(range(n)))
    models = {shape: build_model(shape, n) for shape in partitions(n)}
    results = {"a": check_hom(models, n, perms), "b": check_wedderburn(models, n, perms),
               "c": check_fourier(models, n, perms), "d": check_young_basis(models, n),
               "e": check_restriction(models, n, perms), "f": check_sign_twist(models, n, perms),
               "g": check_frobenius(models, n, perms)}
    dims = {shape: model["dim"] for shape, model in models.items()}
    print(f"\n=== N = {n}: {len(perms)} permutations, shapes/dims {dims}  ({time.time() - start:.1f}s)")
    for field in FIELDS:
        res = results[field]
        print(f"  ({field}) {FIELD_NAMES[field]:<17} {'PASS' if res['ok'] else 'FAIL'}  "
              f"[instances {res['instances']}] {res['detail']}")
    sys.stdout.flush()
    return results, models, perms


def edge_case_notes(n, models, perms):
    """(h): how each field reads at small N, computed from the data."""
    ident = tuple(range(n))
    selfconj = [shape for shape in models if conjugate(shape) == shape]
    constrained = [(shape, sigma) for shape in selfconj for sigma in perms
                   if perm_sign(sigma) == 1 and perm_partition(sigma) != diagonal_hooks(shape)]
    return [f"Shape {n} = {list(models)}, dims {[m['dim'] for m in models.values()]} (= #SYT by Lean def), "
            f"|Perm(Fin {n})| = {len(perms)}, rho(id) = I_dim",
            f"youngBasis: k ranges over Fin {n} ({n} values); J_0 = 0 = content of entry 0 (cell (0,0))" if n else
            "youngBasis: k : Fin 0 is empty; basis of F^1 indexed by the 1 tableau of the empty shape",
            "restriction: no top : Fin 0 -> vacuous" if n == 0 else
            f"restriction: top = {n - 1}, |Stab(top)| = {sum(1 for s in perms if s[n - 1] == n - 1)}",
            f"signTwist: conjugate pairs {[(s, conjugate(s)) for s in models]}",
            f"frobenius: self-conjugate {selfconj}; partition(id) = {list(perm_partition(ident))}, "
            f"h = {[list(diagonal_hooks(s)) for s in selfconj]}; constrained (lam, even sigma) pairs: {len(constrained)}"
            + (" -> vacuous" if not constrained else "")]


# ----------------------------------------------------------------------------------------------- (i) paper probe
def transposition_matrices(gens, n):
    gen_rows = [nonzero_rows(gen) for gen in gens]
    gen_cols = [nonzero_cols(gen) for gen in gens]
    trans = {}
    for low in range(n - 1):
        trans[(low, low + 1)] = gens[low]
        for high in range(low + 2, n):        # (low high) = s_{high-1} (low high-1) s_{high-1}
            trans[(low, high)] = right_mul_sparse(left_mul_sparse(gen_rows[high - 1], trans[(low, high - 1)]),
                                                  gen_cols[high - 1])
    return trans


def commutant_dim_mod_p(mats, dim):
    """dim of the F_p-commutant of `mats` (an upper bound for the Q-commutant dim); diagonal matrices are used first."""
    order = sorted(range(len(mats)), key=lambda idx: not is_diagonal(mats[idx]))
    basis = np.eye(dim * dim, dtype=np.int64)
    for idx in order:
        mod = matrix_mod_p(mats[idx])
        if is_diagonal(mats[idx]) and basis.shape[0] == dim * dim:     # first constraint, basis = all E_ab
            basis = basis[[row * dim + col for row in range(dim) for col in range(dim) if mod[row, row] == mod[col, col]]]
            print(f"      F_p-commutant of the diagonal Y_(N-1): dim {basis.shape[0]}")
            continue
        count = basis.shape[0]
        stacked = basis.reshape(count, dim, dim)
        comm = (np.matmul(stacked, mod) % PRIME - np.matmul(mod, stacked) % PRIME) % PRIME
        null = nullspace_mod_p(comm.reshape(count, dim * dim).T)
        basis = (null @ basis) % PRIME
        print(f"      F_p-commutant after one more Y_j: dim {basis.shape[0]}")
        sys.stdout.flush()
    return basis.shape[0]


def paper_probe(shape):
    n, start = sum(shape), time.time()
    tableaux = syt_recursive(shape)
    dim = len(tableaux)
    problems = []
    if set(syt_lean_definition(shape)) != set(tableaux) or dim != hook_length_count(shape):
        problems.append("SYT enumeration mismatch")
    gens = seminormal_generators(tableaux, n)
    problems += coxeter_problems(gens, dim, str(shape))
    trans = transposition_matrices(gens, n)
    stars = [None] * n
    for center in range(n):
        total = zero_matrix(dim, dim)
        for other in range(n):
            if other != center:
                total = mat_add(total, trans[(min(center, other), max(center, other))])
        stars[center] = total
    if stars[n - 1] != diagonal([content(pos, n - 1) for pos in tableaux]):
        problems.append("Y_{N-1} != J_{N-1} = diag(contents)")
    identity_ok = gens[n - 2] == mat_scale(-1, matmul(matmul(stars[n - 1], stars[n - 2]), stars[n - 1]))
    if not identity_ok:
        problems.append("rho((N-2 N-1)) != -Y_{N-1} Y_{N-2} Y_{N-1}")
    if dim <= SMALL_COMMUTANT_DIM:
        rows = []
        for mat in stars:
            for row in range(dim):
                for col in range(dim):
                    eq = [ZERO] * (dim * dim)
                    for mid in range(dim):
                        eq[row * dim + mid] += mat[mid][col]
                        eq[mid * dim + col] -= mat[row][mid]
                    rows.append(eq)
        comm, how = dim * dim - rank_exact(rows, dim * dim), "exact over Q"
    else:
        comm, how = commutant_dim_mod_p(stars, dim), f"F_{PRIME}-commutant dim (upper bound for Q)"
    if comm != 1:
        problems.append(f"commutant of {{Y_j}} has dim {comm} ({how})")
    note = (f"nu={shape} N={n} dim={dim}: rho((N-2 N-1)) = -Y_(N-1) Y_(N-2) Y_(N-1): {identity_ok}; "
            f"commutant dim {comm} ({how}); Coxeter relations OK: {not any('braid' in p or '^2' in p for p in problems)}"
            f"  ({time.time() - start:.1f}s)")
    return verdict(problems, 1, note)


# ----------------------------------------------------------------------------------------------- (j) Kuzmin, small n
def compositions(total, parts):
    """Ordered tuples of `parts` positive integers summing to `total`."""
    if parts == 0:
        if total == 0:
            yield ()
        return
    for first in range(1, total - parts + 2):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def linearization_generators(n, m, with_ends):
    """Spanning set of V_m ∩ T(x^n) over a char-0 field (with_ends=True): u P_n(w_1..w_n) v, P_n = full linearization of
    x^n, u, v monomials (possibly empty), w_i nonempty, every letter 0..m-1 used once. with_ends=False keeps only
    P_n(w_1..w_n) (Domokos Lemma 3.1's set) — a subset of T in any case. Rows indexed by the m! multilinear words."""
    index = {word: idx for idx, word in enumerate(itertools.permutations(range(m)))}
    ends = range(m + 1) if with_ends else (0,)
    seen, rows = set(), []
    for word in index:
        for head, tail in itertools.product(ends, ends):
            for lengths in compositions(m - head - tail, n) if m - head - tail >= n else ():
                cuts = list(itertools.accumulate((head,) + lengths))
                pieces = [word[cuts[idx]:cuts[idx + 1]] for idx in range(n)]
                key = (word[:head], frozenset(pieces), word[m - tail:])
                if key in seen:
                    continue
                seen.add(key)
                row = [0] * len(index)
                for order in itertools.permutations(pieces):
                    row[index[word[:head] + sum(order, ()) + word[m - tail:]]] += 1
                rows.append(row)
    return rows, index


def word_not_in_T_exact(n, m):
    """Exact over Q: is x_0 x_1 ... x_{m-1} outside span(V_m ∩ T(x^n))? (reduce it against the RREF)."""
    rows, index = linearization_generators(n, m, with_ends=True)
    reduced, pivots = rref_exact([[Fraction(value) for value in row] for row in rows], len(index))
    target = [ZERO] * len(index)
    target[index[tuple(range(m))]] = ONE
    for prow, pcol in enumerate(pivots):
        if target[pcol] != 0:
            factor = target[pcol]
            target = [value - factor * pval for value, pval in zip(target, reduced[prow])]
    return any(target), len(pivots), len(index)


def kuzmin_small_n(n):
    """Lean `kuzmin_lower_bound` at n: word of length m = n(n+1)/2 - 1 NOT in T (exact), and length m+1 IS in T
    (V_{m+1} ⊆ T: rank of Domokos-Lemma-3.1 generators mod PRIME = (m+1)!, a lower bound for the rank over Q)."""
    length = n * (n + 1) // 2 - 1
    outside, rank_m, dim_m = word_not_in_T_exact(n, length)
    rows_next, index_next = linearization_generators(n, length + 1, with_ends=False)
    rank_next = rank_mod_p(rows_next)
    ok = outside and rank_next == len(index_next)
    note = (f"n={n}: m={length}: x_0..x_(m-1) not in T(x^n): {outside} (exact; dim V_m ∩ T = {rank_m} of {dim_m}); "
            f"m+1={length + 1}: V_(m+1) ⊆ T: {rank_next == len(index_next)} (rank {rank_next} of {len(index_next)} mod p)")
    return verdict([] if ok else [note], 1, note)


# ----------------------------------------------------------------------------------------------- negative controls
def negative_controls():
    """Each MUST come out FAIL; shows the checker can fail and which conventions are load-bearing."""
    out = []
    data = {}
    for n in (3, 4):
        perms = list(itertools.permutations(range(n)))
        data[n] = ({shape: build_model(shape, n) for shape in partitions(n)}, perms)
    models3, perms3 = data[3]
    models4, perms4 = data[4]
    out.append(("youngBasis with content = row - col (wrong sign), N=3", check_young_basis(models3, 3, content_sign=-1)))
    out.append(("frobenius with cycle type WITHOUT fixed points, N=4 (lam=(2,2))",
                check_frobenius(models4, 4, perms4, partition_of=cycle_type_without_fixed_points)))
    out.append(("restriction with top = 0 instead of N-1, N=3", check_restriction(models3, 3, perms3, top=0)))
    out.append(("signTwist with the sign dropped (eps = +1), N=3", check_sign_twist(models3, 3, perms3, eps=1)))
    out.append(("fourier with every f^lam replaced by 1, N=3",
                check_fourier(models3, 3, perms3, dims={shape: 1 for shape in models3})))
    return out


# ----------------------------------------------------------------------------------------------- main
def verify_prime():
    assert PRIME > 2 and all(PRIME % div for div in range(2, math.isqrt(PRIME) + 1)), "PRIME is not prime"


def main_modelcheck(max_n, paper_shapes, kuzmin_ns):
    verify_prime()
    summary = {field: [] for field in FIELDS}
    edge_ok = True
    for n in range(max_n + 1):
        results, models, perms = run_degree(n)
        for field in FIELDS:
            summary[field].append((n, results[field]["ok"]))
        if n <= 2:
            edge_ok &= all(results[field]["ok"] for field in FIELDS)
            print("  (h) edge-case reading:")
            for line in edge_case_notes(n, models, perms):
                print("        " + line)
    print("\n=== Negative controls (each MUST be FAIL)")
    controls_ok = True
    for label, res in negative_controls():
        controls_ok &= not res["ok"]
        print(f"  {'FAIL (as required)' if not res['ok'] else 'PASS (!! control did not fail)'}: {label} -- "
              f"{res['detail'].splitlines()[0]}")
    print("\n=== (i) Paper-side probe")
    paper_ok = True
    for shape in paper_shapes:
        res = paper_probe(shape)
        paper_ok &= res["ok"]
        print(f"  {'PASS' if res['ok'] else 'FAIL'}  {res['detail']}")
    print("\n=== (j) Kuzmin axiom at small n (extra; char 0, exact)")
    kuzmin_ok = True
    for n in kuzmin_ns:
        res = kuzmin_small_n(n)
        kuzmin_ok &= res["ok"]
        print(f"  {'PASS' if res['ok'] else 'FAIL'}  {res['detail']}")
        sys.stdout.flush()
    print("\n=== SUMMARY")
    all_ok = controls_ok and paper_ok and edge_ok and kuzmin_ok
    for field in FIELDS:
        good = [n for n, ok in summary[field] if ok]
        bad = [n for n, ok in summary[field] if not ok]
        all_ok &= not bad
        print(f"  ({field}) {FIELD_NAMES[field]:<17} {'PASS' if not bad else 'FAIL'}  N = {good}" +
              (f"  FAILED at N = {bad}" if bad else ""))
    print(f"  (h) edge cases N=0,1,2      {'PASS' if edge_ok else 'FAIL'}")
    print(f"  (i) paper probe {list(paper_shapes)}  {'PASS' if paper_ok else 'FAIL'}")
    print(f"  (j) Kuzmin n = {list(kuzmin_ns)}      {'PASS' if kuzmin_ok else 'FAIL'}")
    print(f"  negative controls           {'all FAIL as required' if controls_ok else 'SOME CONTROL PASSED (!!)'}")
    return all_ok


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--maxN", type=int, default=6, help="check N = 0..maxN (default 6)")
    parser.add_argument("--test", action="store_true", help="quick run: N <= 3, paper probe on (2,1) only")
    args = parser.parse_args()
    start = time.time()
    if args.test:
        ok = main_modelcheck(3, ((2, 1),), (2,))
    else:
        ok = main_modelcheck(args.maxN, PAPER_SHAPES, KUZMIN_NS)
    print(f"\nTotal time {time.time() - start:.1f}s.  OVERALL: {'ALL PASS' if ok else 'SOMETHING FAILED'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
