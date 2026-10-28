#!/usr/bin/env python3
# best_constant_second.py - the best constant (last section of the paper), second independent code: lambda_{*,N} by a 1-D LP
#   (HiGHS, through SciPy) on nested grids N = 600 ... 9600. Floating point: numerical, not certified.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# HV holds with constant C = lam^(1/p) * C_HV iff a q-subtrigonometric phi <= m_lam exists, where
# m_lam(t) = min_y [lam ((cosh y + cos t)/(1 + cos(pi/p)))^q - cosh(sy/2)^(p/s)]. So C*/C_HV = lam*^(1/p), lam* = least feasible lam.
# Discretisation on t_i = -pi + i h, h = 2 pi/N: the q-sinusoidal interpolant of (phi_i) is q-subtrig iff every node jump
# J_i = q (phi_{i+1} + phi_{i-1} - 2 cos(qh) phi_i)/sin(qh) >= 0. The node problem is a RELAXATION (phi <= m only at nodes), so
# lam*_N <= lam* and lam*_N is nondecreasing along nested grids (a built-in check).
# Phase I: sigma*(lam) = min sigma s.t. J_i/h >= -sigma (density units, N-independent), phi_i <= m_lam(t_i); feasible iff sigma* = 0.
# The interior-point method can fail on an exactly degenerate LP (lam = lam*_N): it is then re-solved by dual simplex, printed and
# counted. N = 19200 is below double precision and is not used.
# Usage: python3 best_constant_second.py --test | --run
import sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix, hstack, csr_matrix

Y_MAX = 8.0          # Gamma -> +oo in |y|; the argmin is checked to stay inside [0, Y_MAX)
Y_COARSE = 801       # coarse y grid before the golden-section refinement
GOLDEN_STEPS = 60    # interval shrinks by 0.618^60 ~ 3e-13
SIGMA_TOL = 1e-9     # feasible <=> sigma* <= SIGMA_TOL (density units)
LAM_WIDTH = 1e-10    # bisection stops at this bracket width (lam* - 1 ~ 6e-5: 6 digits)
T_CHUNK = 2000       # t-points per vectorised chunk (memory)
DS_RETRIES = []      # N of every LP re-solved by dual simplex after an IPM error (printed at the end)


def gamma_lam(lam, p, s, y, t):
    """Gamma_lam(y, t) = lam ((cosh y + cos t)/(1 + cos(pi/p)))^q - cosh(s y/2)^(p/s); y, t broadcast."""
    base = (np.cosh(y) + np.cos(t)) / (1 + np.cos(np.pi / p))
    return lam * np.maximum(base, 0.0) ** (p / 2) - np.cosh(s * y / 2) ** (p / s)


def golden_refine(func, lo, hi):
    """Vectorised golden-section minimisation of func on [lo, hi] (arrays); returns the minimum values."""
    ratio = (np.sqrt(5) - 1) / 2
    for _ in range(GOLDEN_STEPS):
        left, right = hi - ratio * (hi - lo), lo + ratio * (hi - lo)
        go_left = func(left) < func(right)
        hi = np.where(go_left, right, hi)
        lo = np.where(go_left, lo, left)
    return func((lo + hi) / 2)


def m_lam_chunk(lam, p, s, t_chunk):
    """min over y >= 0 of Gamma_lam (even in y) for each t in t_chunk: coarse grid, then golden refinement."""
    y_grid = np.linspace(0.0, Y_MAX, Y_COARSE)
    step = y_grid[1] - y_grid[0]
    values = gamma_lam(lam, p, s, y_grid[None, :], t_chunk[:, None])
    k_best = np.argmin(values, axis=1)
    if np.any(k_best >= Y_COARSE - 2):
        raise RuntimeError("argmin at the y-grid edge: raise Y_MAX")
    lo = np.maximum(y_grid[k_best] - step, 0.0)
    hi = y_grid[k_best] + step
    return golden_refine(lambda yy: gamma_lam(lam, p, s, yy, t_chunk), lo, hi)


def m_lam(lam, p, s, t_nodes):
    """m_lam on all nodes, in chunks."""
    parts = [m_lam_chunk(lam, p, s, t_nodes[k:k + T_CHUNK]) for k in range(0, len(t_nodes), T_CHUNK)]
    return np.concatenate(parts)


def jump_matrix(n_nodes, q, h):
    """Sparse rows J_i/h = q (phi_{i+1} + phi_{i-1} - 2 cos(qh) phi_i)/(h sin(qh)), periodic indices."""
    idx = np.arange(n_nodes)
    scale = q / (h * np.sin(q * h))
    rows = np.concatenate([idx, idx, idx])
    cols = np.concatenate([(idx + 1) % n_nodes, (idx - 1) % n_nodes, idx])
    vals = np.concatenate([np.full(n_nodes, scale), np.full(n_nodes, scale), np.full(n_nodes, -2 * np.cos(q * h) * scale)])
    return coo_matrix((vals, (rows, cols)), shape=(n_nodes, n_nodes))


def phase_one_sigma(m_nodes, q, h, method="highs-ipm"):
    """sigma* = min sigma s.t. J/h + sigma >= 0, phi <= m, sigma >= 0. Returns (sigma*, phi). IPM: 10x faster than dual
    simplex at N = 19200 (2.2 s vs 21 s); run_tests checks both agree."""
    n_nodes = len(m_nodes)
    a_ub = csr_matrix(hstack([-jump_matrix(n_nodes, q, h), -np.ones((n_nodes, 1))]))
    cost = np.zeros(n_nodes + 1)
    cost[-1] = 1.0
    bounds = [(None, mm) for mm in m_nodes] + [(0, None)]
    opts = {"primal_feasibility_tolerance": 1e-10, "dual_feasibility_tolerance": 1e-10}
    res = linprog(cost, A_ub=a_ub, b_ub=np.zeros(n_nodes), bounds=bounds, method=method, options=opts)
    if res.status == 4 and method == "highs-ipm":
        # IPM fails on the exactly degenerate LP at lam = lam*_N (seen at N = 9600, (3/2, 3.9), lam = 1). Dual simplex
        # is the reference method (run_tests: ipm = ds); the switch is printed and counted, never silent.
        DS_RETRIES.append(n_nodes)
        print(f"  [IPM status 4 at N = {n_nodes}: re-solved with dual simplex (retry #{len(DS_RETRIES)})]", flush=True)
        return phase_one_sigma(m_nodes, q, h, method="highs-ds")
    if res.status != 0:
        raise RuntimeError(f"LP status {res.status} ({method}): {res.message}")
    return res.x[-1], res.x[:-1]


def nodes(n_nodes):
    """t_i = -pi + i h, h = 2 pi/N."""
    h = 2 * np.pi / n_nodes
    return -np.pi + h * np.arange(n_nodes), h


def sigma_at(lam, p, s, n_nodes):
    t_nodes, h = nodes(n_nodes)
    return phase_one_sigma(m_lam(lam, p, s, t_nodes), p / 2, h)


def lam_star(p, s, n_nodes, lam_lo, lam_hi):
    """Bisection for the least lam with sigma* <= SIGMA_TOL; checks the bracket ends first."""
    if sigma_at(lam_hi, p, s, n_nodes)[0] > SIGMA_TOL or sigma_at(lam_lo, p, s, n_nodes)[0] <= SIGMA_TOL:
        raise RuntimeError(f"bad bracket [{lam_lo}, {lam_hi}] at p={p}, s={s}, N={n_nodes}")
    while lam_hi - lam_lo > LAM_WIDTH:
        mid = (lam_lo + lam_hi) / 2
        if sigma_at(mid, p, s, n_nodes)[0] <= SIGMA_TOL:
            lam_hi = mid
        else:
            lam_lo = mid
    return lam_hi


def solution_diagnostics(lam, p, s, n_nodes):
    """At a feasible lam: min node jump density and max (phi - m) at nodes, from the returned phi (a posteriori, numpy)."""
    t_nodes, h = nodes(n_nodes)
    m_nodes = m_lam(lam, p, s, t_nodes)
    sigma, phi = phase_one_sigma(m_nodes, p / 2, h)
    density = jump_matrix(n_nodes, p / 2, h).tocsr() @ phi
    return sigma, density.min(), (phi - m_nodes).max()


def sweep(p, s, grid_sizes, lam_lo, lam_hi):
    """lam*_N on nested grids; prints C*/C - 1 = lam*^(1/p) - 1 and the monotonicity check."""
    previous = None
    for n_nodes in grid_sizes:
        lam = lam_star(p, s, n_nodes, lam_lo, lam_hi)
        sigma, dens_min, excess = solution_diagnostics(lam, p, s, n_nodes)
        mono = "" if previous is None else f"  step {lam - previous:+.3e} ({'OK' if lam >= previous - 2 * LAM_WIDTH else 'DROP!'})"
        print(f"p={p} s={s} N={n_nodes:6d}: lam*-1 = {lam - 1:+.6e}  C*/C-1 = {lam ** (1 / p) - 1:+.6e}"
              f"  [sigma {sigma:.1e}, min J/h {dens_min:.1e}, max phi-m {excess:.1e}]{mono}", flush=True)
        previous = lam


def run_tests():
    """Controls at small N: (a) lam = 1, s = 3.9 < s0(3/2): sigma* = 0; (b) lam = 1, s = 4: sigma* > 0 (HV false at C_conj);
    (c) the jump matrix kills q-sinusoids; (d) m_1(pi/p) at s = 4 is 0 to 1e-12 (contact point)."""
    t_nodes, h = nodes(600)
    test_phi = np.cos(0.75 * (t_nodes + 0.3))           # not 2 pi-periodic: test interior rows only (the wrap row sees a kink)
    assert np.abs((jump_matrix(600, 0.75, h).tocsr() @ test_phi)[1:-1]).max() < 1e-6, "q-sinusoid not in the kernel"
    assert abs(m_lam(1.0, 1.5, 4.0, np.array([2 * np.pi / 3]))[0]) < 1e-12, "contact value"
    assert sigma_at(1.0, 1.5, 3.9, 600)[0] <= SIGMA_TOL, "s = 3.9 should be feasible at lam = 1"
    assert sigma_at(1.0, 1.5, 4.0, 600)[0] > SIGMA_TOL, "s = 4 should be infeasible at lam = 1"
    t_nodes, h = nodes(1200)
    m_nodes = m_lam(1.0, 1.5, 4.0, t_nodes)
    sig_ipm, sig_ds = phase_one_sigma(m_nodes, 0.75, h)[0], phase_one_sigma(m_nodes, 0.75, h, method="highs-ds")[0]
    assert abs(sig_ipm - sig_ds) < 1e-10 * max(1.0, sig_ds), (sig_ipm, sig_ds)
    print(f"tests: kernel, contact, feasible control (3/2, 3.9), infeasible control (3/2, 4), ipm = ds "
          f"({sig_ipm:.12e} vs {sig_ds:.12e}) - PASS")


def main_cstar_lp():
    grid_sizes = [600, 1200, 2400, 4800, 9600]
    for p, s, lam_lo, lam_hi in [(1.5, 4.0, 1.0, 1.001), (1.5, 3.98, 1.0, 1.001),
                                 (1.5, 3.9, 0.99, 1.01), (1.3, 1 / np.cos(np.pi / 2.6) ** 2, 0.99, 1.01)]:
        sweep(p, s, grid_sizes, lam_lo, lam_hi)
    print(f"dual-simplex re-solves after IPM errors: {len(DS_RETRIES)} (N = {sorted(set(DS_RETRIES))})")
    print(f"note: sigma tolerance {SIGMA_TOL} biases every lam*_N DOWN by about SIGMA_TOL/0.57 = {SIGMA_TOL / 0.57:.1e} (safe side)")


def main():
    if "--test" in sys.argv:
        run_tests()
    elif "--run" in sys.argv:
        main_cstar_lp()
    else:
        raise SystemExit("usage: best_constant_second.py --test | --run")


if __name__ == "__main__":
    main()
