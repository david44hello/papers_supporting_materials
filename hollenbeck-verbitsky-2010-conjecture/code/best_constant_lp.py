#!/usr/bin/env python3
# best_constant_lp.py - the best constant (last section of the paper): lambda_{*,N} by linear programming (HiGHS, through SciPy).
#   Floating point: numerical, not certified.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# HV with the constant lam^(1/p) C_HV holds <=> some q-subtrigonometric phi on the circle (phi'' + q^2 phi >= 0) satisfies
#   phi <= m_lam(t) = min_y Gamma_lam(y, t), Gamma_lam = lam (cosh y + cos t)^q / (1 + cos(pi/p))^q - cosh(s y / 2)^(p/s).
#   lam = 1 is the conjectured constant; the best constant is lam_*^(1/p) C_HV, lam_* = the least feasible lam.
# Discrete scheme: phi(t+h) + phi(t-h) - 2 cos(qh) phi(t) >= 0 is EXACT for q-trig functions (cos(qt) is an exact discrete
#   solution); +-pi/p are grid points when N = 2 p K, K an integer. --constant bisects lam with the phase-I LP:
#   min sigma s.t. D phi / h^2 >= -sigma, -PHI_FLOOR <= phi <= m (always feasible); feasible <=> sigma* <= SIGMA_TOL.
# report / obstacle_1d: the monotone iteration phi <- min(m, (phi(t+h) + phi(t-h)) / (2 cos qh)) from phi = m (a control in --test).
# --upper (not used in the paper): a floating-point upper bound for lam_*, checked on FINE points per cell.
"""Usage: python3 best_constant_lp.py P S K                  (LP feasibility at lam = 1; N = 2 P K points, must be an integer)
          python3 best_constant_lp.py --constant P S K STEPS   (LP bisection for the smallest feasible lam; prints A*/A)
          python3 best_constant_lp.py --upper P S K STEPS SAMPLES FINE   (floating-point UPPER bound for lam*, verified on FINE pts/cell)
          python3 best_constant_lp.py --test"""
import math
import sys

import numpy as np
import scipy.optimize as spo
import scipy.sparse as sps

Y_MAX, N_Y = 6.0, 6001
T_CHUNK = 500                                                # t-rows per coarse block: 500 x 6001 doubles = 24 MB
PHI_FLOOR = 100.0                                            # phase-I lower bound on phi (feasible phi are >= e >= -tan(th))
SIGMA_TOL = 1.0e-9                                           # sigma* (mu units) at or below this = feasible
GOLDEN_STEPS = 60
RUNOFF = -1.0e6
TOL = 1.0e-13
MARGIN_M = 3.0e-8                                            # upper bound: phi <= m - MARGIN_M at nodes and cell samples
MARGIN_MU = 1.0e-8                                           # upper bound: D phi / h^2 >= MARGIN_MU (jumps stay > 0 after tolerance)
LP_TOL = 1.0e-10                                             # HiGHS primal feasibility tolerance of the upper-bound LP
UPPER_HI = 1.0e-4                                            # upper-bound bisection runs on [1, 1 + UPPER_HI]


def gamma_lam(yy, tt, pp, ss, lam):
    qq = pp / 2
    return lam * (np.cosh(yy) + np.cos(tt)) ** qq / (1 + math.cos(math.pi / pp)) ** qq - np.cosh(ss * yy / 2) ** (pp / ss)


def helper_e(tt, pp):
    return math.tan(math.pi / (2 * pp)) * np.cos(pp * np.abs(tt) / 2)


def golden_min(func, lo, hi):
    """Golden-section minimisation of func, elementwise on the arrays [lo, hi]."""
    ratio = (math.sqrt(5) - 1) / 2
    for _ in range(GOLDEN_STEPS):
        aa, bb = hi - ratio * (hi - lo), lo + ratio * (hi - lo)
        left = func(aa) < func(bb)
        lo, hi = np.where(left, lo, aa), np.where(left, bb, hi)
    return 0.5 * (lo + hi)


def m_of_t(ts, pp, ss, lam):
    """m(t) = min over y >= 0 (Gamma is even in y): coarse grid (in t-chunks of T_CHUNK, memory), then golden refinement."""
    ys = np.linspace(0, Y_MAX, N_Y)
    step = ys[1] - ys[0]
    out, ystar = np.empty(len(ts)), np.empty(len(ts))
    for start in range(0, len(ts), T_CHUNK):
        chunk = ts[start: start + T_CHUNK]
        vals = gamma_lam(ys[None, :], chunk[:, None], pp, ss, lam)
        idx = vals.argmin(axis=1)
        lo, hi = np.maximum(0.0, ys[idx] - step), np.minimum(Y_MAX, ys[idx] + step)
        ybest = golden_min(lambda yv: gamma_lam(yv, chunk, pp, ss, lam), lo, hi)
        ychunk = np.where(gamma_lam(ybest, chunk, pp, ss, lam) < vals[:, 0], ybest, 0.0)
        ystar[start: start + len(chunk)] = ychunk
        out[start: start + len(chunk)] = gamma_lam(ychunk, chunk, pp, ss, lam)
    return out, ystar


def circle(pp, kk):
    """N = 2pK points t_i = -pi + 2 pi i / N; +-pi/p are nodes (i = K(p -+ 1)) iff K p is an integer (at p = 3/2: K even)."""
    if abs(kk * pp - round(kk * pp)) > 1e-9:
        raise SystemExit(f"K p = {kk * pp} is not an integer: +-pi/p would not be grid points")
    npts = int(round(2 * pp * kk))
    return -math.pi + 2 * math.pi * np.arange(npts) / npts


def obstacle_1d(mm, pp, hh, iters):
    """Largest phi <= m with the exact-trig inequality; returns (phi, status, sweeps)."""
    denom = 2 * math.cos(pp / 2 * hh)
    phi = mm.copy()
    for sweep in range(1, iters + 1):
        new = np.minimum(mm, (np.roll(phi, 1) + np.roll(phi, -1)) / denom)
        change = np.abs(new - phi).max()
        phi = new
        if phi.min() < RUNOFF:
            return phi, "RUNOFF", sweep
        if change < TOL:
            return phi, "CONVERGED", sweep
    return phi, "UNDECIDED", iters


def trig_matrix(npts, pp, hh):
    """Rows: -(phi(k+1) + phi(k-1) - 2 cos(qh) phi(k)) / h^2 <= 0, periodic (scaled so the tolerance acts on mu)."""
    rows = np.repeat(np.arange(npts), 3)
    cols = np.stack([(np.arange(npts) + 1) % npts, (np.arange(npts) - 1) % npts, np.arange(npts)], axis=1).ravel()
    vals = np.tile([-1.0, -1.0, 2 * math.cos(pp / 2 * hh)], npts) / hh ** 2
    return sps.csr_matrix((vals, (rows, cols)), shape=(npts, npts))


def lp_slack(mm, pp, hh):
    """Phase-I LP: least sigma >= 0 with (D phi)/h^2 >= -sigma and -PHI_FLOOR <= phi <= m. Returns (sigma*, phi)."""
    npts = len(mm)
    a_ub = sps.hstack([trig_matrix(npts, pp, hh), sps.csr_matrix(-np.ones((npts, 1)))], format="csr")
    cost = np.zeros(npts + 1)
    cost[-1] = 1.0
    bounds = list(zip([-PHI_FLOOR] * npts, mm)) + [(0.0, None)]
    res = spo.linprog(cost, A_ub=a_ub, b_ub=np.zeros(npts), bounds=bounds, method="highs")
    if res.status != 0:
        raise SystemExit(f"phase-I LP status {res.status}: {res.message}")
    return res.x[-1], res.x[:-1]


def lp_feasible(mm, pp, hh):
    """Discrete test: is there phi <= m with the exact-trig inequalities? Returns (bool, phi, sigma*)."""
    sigma, phi = lp_slack(mm, pp, hh)
    return sigma <= SIGMA_TOL, phi, sigma


def lp_report(pp, ss, kk, lam=1.0):
    ts = circle(pp, kk)
    mm, ystar = m_of_t(ts, pp, ss, lam)
    feas, phi, sigma = lp_feasible(mm, pp, ts[1] - ts[0])
    gap = mm - helper_e(ts, pp)
    worst = int(gap.argmin())
    extra = f"; phi - e min {(phi - helper_e(ts, pp)).min():.3e}" if feas else ""
    print(f"LP p={pp} s={ss} lam={lam:.12f} N={len(ts)}: {'FEASIBLE' if feas else 'INFEASIBLE'} (sigma* = {sigma:.3e}); "
          f"min(m - e) = {gap[worst]:.6e} at t = {ts[worst]:.5f} (y* = {ystar[worst]:.5f}){extra}", flush=True)
    return feas, gap[worst]


def report(pp, ss, kk, iters, lam=1.0):
    ts = circle(pp, kk)
    mm, ystar = m_of_t(ts, pp, ss, lam)
    phi, status, sweeps = obstacle_1d(mm, pp, ts[1] - ts[0], iters)
    gap = mm - helper_e(ts, pp)
    worst = int(gap.argmin())
    print(f"p={pp} s={ss} lam={lam:.12f} N={len(ts)}: {status} after {sweeps} sweeps; min(m - e) = {gap[worst]:.6e} at t = "
          f"{ts[worst]:.5f} (y* = {ystar[worst]:.5f}); phi(0) = {phi[len(ts)//2]:.6f}", flush=True)
    return status, gap[worst]


def best_constant(pp, ss, kk, steps):
    """Bisect lam in [1, 1.01] with the exact LP: smallest feasible lam (A*/A = lam^(1/p))."""
    lo, hi = 1.0, 1.01
    if lp_report(pp, ss, kk, lo)[0]:
        print(f"lam = 1 FEASIBLE: HV holds at p={pp} s={ss} (A* = A)", flush=True)
        return 1.0, 1.0
    if not lp_report(pp, ss, kk, hi)[0]:
        raise SystemExit("lam = 1.01 not feasible: widen the bracket")
    for _ in range(steps):
        mid = 0.5 * (lo + hi)
        lo, hi = (lo, mid) if lp_report(pp, ss, kk, mid)[0] else (mid, hi)
    print(f"CONSTANT p={pp} s={ss}: lam* in [{lo:.12f}, {hi:.12f}]; A*/A in [{lo**(1/pp):.12f}, {hi**(1/pp):.12f}]", flush=True)
    return lo, hi


def cell_weights(pp, hh, thetas):
    """q-trig interpolation on a cell [t_i, t_i + h]: Phi(t_i + theta h) = w1 phi_i + w2 phi_(i+1)."""
    qq = pp / 2
    return np.sin(qq * (1 - thetas) * hh) / math.sin(qq * hh), np.sin(qq * thetas * hh) / math.sin(qq * hh)


def sample_points(ts, hh, thetas):
    """The points t_i + theta_j h of every cell (the last cell ends at pi), cell-major order."""
    return (ts[:, None] + thetas[None, :] * hh).ravel()


def interpolant(phi, pp, hh, thetas):
    """The q-trig interpolant of the node values phi at the sample_points (cell-major order, periodic)."""
    w1, w2 = cell_weights(pp, hh, thetas)
    return (phi[:, None] * w1[None, :] + np.roll(phi, -1)[:, None] * w2[None, :]).ravel()


def sample_matrix(npts, pp, hh, thetas):
    """Rows w1 phi_i + w2 phi_(i+1) (row i * len(thetas) + j), periodic in i."""
    w1, w2 = cell_weights(pp, hh, thetas)
    left = np.repeat(np.arange(npts), len(thetas))
    rows = np.repeat(np.arange(npts * len(thetas)), 2)
    cols = np.stack([left, (left + 1) % npts], axis=1).ravel()
    vals = np.stack([np.tile(w1, npts), np.tile(w2, npts)], axis=1).ravel()
    return sps.csr_matrix((vals, (rows, cols)), shape=(npts * len(thetas), npts))


def solve_upper_lp(cost, a_ub, b_ub, bounds):
    res = spo.linprog(cost, A_ub=a_ub, b_ub=b_ub, bounds=bounds, method="highs", options={"primal_feasibility_tolerance": LP_TOL})
    if res.status != 0:
        raise SystemExit(f"upper-bound LP status {res.status}: {res.message}")
    return res.x


def lp_slack_upper(mm, msamp, pp, hh, thetas):
    """LP for the UPPER bound. Stage 1 (phase I): least sigma >= 0 with D phi / h^2 >= MARGIN_MU - sigma, phi <= m - MARGIN_M at the
    nodes and interpolant <= m - MARGIN_M at the cell samples. Stage 2 (if feasible): sigma held at sigma*, minimise sum(phi), which
    pushes phi away from m wherever nothing pins it (near t = pi, m = -1 + c |pi - t|^(3/2) has unbounded curvature and a phi that
    touches m there pokes above it between samples). Returns (sigma*, phi)."""
    npts, nsamp = len(mm), len(msamp)
    trig = sps.hstack([trig_matrix(npts, pp, hh), sps.csr_matrix(-np.ones((npts, 1)))])
    samp = sps.hstack([sample_matrix(npts, pp, hh, thetas), sps.csr_matrix((nsamp, 1))])
    a_ub = sps.vstack([trig, samp], format="csr")
    b_ub = np.concatenate([np.full(npts, -MARGIN_MU), msamp - MARGIN_M])
    phi_bounds = list(zip([-PHI_FLOOR] * npts, mm - MARGIN_M))
    cost = np.zeros(npts + 1)
    cost[-1] = 1.0
    sigma = solve_upper_lp(cost, a_ub, b_ub, phi_bounds + [(0.0, None)])[-1]
    if sigma > SIGMA_TOL:
        return sigma, None
    low = solve_upper_lp(np.concatenate([np.ones(npts), [0.0]]), a_ub, b_ub, phi_bounds + [(sigma, sigma)])
    return sigma, low[:-1]


def upper_feasible(pp, ss, ts, lam, thetas):
    """Is the SAMPLED LP feasible at lam? Returns (bool, phi, sigma*)."""
    hh = ts[1] - ts[0]
    mm = m_of_t(ts, pp, ss, lam)[0]
    msamp = m_of_t(sample_points(ts, hh, thetas), pp, ss, lam)[0]
    sigma, phi = lp_slack_upper(mm, msamp, pp, hh, thetas)
    return sigma <= SIGMA_TOL, phi, sigma


def verify_upper(phi, ts, pp, ss, lam, fine):
    """LP-independent floating-point check: (min jump in mu units, max of Phi - m_lam over the nodes and `fine` interior points per
    cell). Jumps >= 0 make the interpolant Phi q-subtrigonometric (the jump criterion of the paper); with Phi <= m_lam this gives lam >= lam*."""
    hh = ts[1] - ts[0]
    thetas = np.arange(1, fine + 1) / (fine + 1)
    jumps = -(trig_matrix(len(ts), pp, hh) @ phi)
    mfine = m_of_t(sample_points(ts, hh, thetas), pp, ss, lam)[0]
    excess = max((interpolant(phi, pp, hh, thetas) - mfine).max(), (phi - m_of_t(ts, pp, ss, lam)[0]).max())
    return jumps.min(), excess


def lift_jumps(phi, pp, hh):
    """Repair LP tolerance: HiGHS may leave jumps ~ -1e-9 (mu units) at sigma* near SIGMA_TOL. A constant c raises every jump by
    c (2 - 2 cos(qh)) / h^2 > 0, so phi + c with c = 2 * deficit / that factor has all jumps >= 0; it costs c of the MARGIN_M room,
    which verify_upper then checks. Returns (phi + c, c)."""
    per_unit = (2 - 2 * math.cos(pp / 2 * hh)) / hh ** 2
    jumps = -(trig_matrix(len(phi), pp, hh) @ phi)
    shift = 2 * max(0.0, -jumps.min()) / per_unit
    return phi + shift, shift


def upper_constant(pp, ss, kk, steps, samples, fine):
    """Smallest lam with a feasible SAMPLED LP (bisection on [1, 1 + UPPER_HI]), then verify_upper of its interpolant: a
    floating-point UPPER bound for lam* (best_constant gives the lower bound lam*_N)."""
    ts = circle(pp, kk)
    thetas = np.arange(1, samples + 1) / (samples + 1)
    lo, hi = 1.0, 1.0 + UPPER_HI
    if not upper_feasible(pp, ss, ts, hi, thetas)[0]:
        raise SystemExit(f"sampled LP infeasible at lam = 1 + {UPPER_HI}: widen UPPER_HI")
    if upper_feasible(pp, ss, ts, lo, thetas)[0]:
        hi = lo
    for _ in range(steps if hi > lo else 0):
        mid = 0.5 * (lo + hi)
        lo, hi = (lo, mid) if upper_feasible(pp, ss, ts, mid, thetas)[0] else (mid, hi)
    feas, phi, sigma = upper_feasible(pp, ss, ts, hi, thetas)
    phi, shift = lift_jumps(phi, pp, ts[1] - ts[0])
    jump, excess = verify_upper(phi, ts, pp, ss, hi, fine)
    verdict = "VERIFIED" if feas and jump >= 0.0 and excess <= 0.0 else "NOT VERIFIED"
    print(f"UPPER p={pp} s={ss} N={len(ts)} samples={samples} fine={fine}: lam_up = {hi:.12f} (sigma* {sigma:.2e}, shift "
          f"{shift:.2e}); min jump {jump:.3e} (mu units), max(Phi - m) {excess:.3e} -> {verdict}; A*/A <= {hi ** (1 / pp):.12f}",
          flush=True)
    return hi, verdict, phi


def run_tests():
    """Proved range (p = 1.5, s = 2.5): CONVERGED, min(m - e) >= 0 (touching only). s = 4.5 > sec^2: RUNOFF. Exactness: cos(qt)
    satisfies the discrete equality to rounding."""
    ts = circle(1.5, 40)
    hh = ts[1] - ts[0]
    trig = np.cos(0.75 * ts)
    exact = np.abs(np.roll(trig, 1)[1:-1] + np.roll(trig, -1)[1:-1] - 2 * math.cos(0.75 * hh) * trig[1:-1]).max()
    good = lp_report(1.5, 2.5, 40)
    bad = lp_report(1.5, 4.5, 40)
    runoff = report(1.5, 4.5, 40, 200000)
    ok = exact < 1e-12 and good[0] and good[1] > -1e-9 and not bad[0] and runoff[0] == "RUNOFF"
    print(f"  exact-trig residual {exact:.2e}")
    ok = upper_tests() and ok
    print("ALL TESTS PASS" if ok else "TEST FAILURE", flush=True)
    return ok


def upper_tests():
    """Upper-bound controls at N = 1200 (24 samples, 48 check points per cell; at N = 120 the gap between samples is too wide for
    MARGIN_M): s = 2.5 (HV holds) gives lam_up - 1 < 1e-6 (the margins only), VERIFIED; s = 4 gives lam*_N <= lam_up, VERIFIED;
    and verify_upper CAN fail: the same phi shifted up by 1e-6 (excess > 0), or dented by 1e-3 at one node (a negative jump)."""
    good = upper_constant(1.5, 2.5, 400, 14, 24, 48)
    lower = best_constant(1.5, 4.0, 400, 14)
    upper = upper_constant(1.5, 4.0, 400, 14, 24, 48)
    ts = circle(1.5, 400)
    shifted = verify_upper(upper[2] + 1e-6, ts, 1.5, 4.0, upper[0], 48)
    dent = upper[2].copy()
    dent[len(ts) // 3] += 1e-3
    dented = verify_upper(dent, ts, 1.5, 4.0, upper[0], 48)
    print(f"  upper controls: shifted phi max(Phi - m) {shifted[1]:.2e} (> 0); dented phi min jump {dented[0]:.2e} (< 0)")
    return (good[0] - 1 < 1e-6 and good[1] == "VERIFIED" and upper[1] == "VERIFIED" and lower[0] <= upper[0]
            and shifted[1] > 0 and dented[0] < 0)


def main_1d(argv):
    if argv == ["--test"]:
        return 0 if run_tests() else 1
    if argv and argv[0] == "--constant":
        best_constant(float(argv[1]), float(argv[2]), int(argv[3]), int(argv[4]))
        return 0
    if argv and argv[0] == "--upper":
        verdict = upper_constant(float(argv[1]), float(argv[2]), int(argv[3]), int(argv[4]), int(argv[5]), int(argv[6]))[1]
        return 0 if verdict == "VERIFIED" else 1
    lp_report(float(argv[0]), float(argv[1]), int(argv[2]))
    return 0


def main():
    sys.exit(main_1d(sys.argv[1:]))


if __name__ == "__main__":
    main()
