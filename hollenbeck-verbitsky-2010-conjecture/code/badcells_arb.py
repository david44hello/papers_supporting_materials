#!/usr/bin/env python3
# badcells_arb.py - failure of Gamma >= e, certified in Arb (100 bits): the upper bounds s_+ of the bracket proposition (--points)
#   and the false cells: Gamma < e at s = sec^2(pi/2p) - Delta for every p of a cell (--cells).
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# Psi(y, t) = Gamma(y, t) - e(t) = -cosh(sy/2)^(p/s) + ((cosh y + cos t)/(1 + cos(pi/p)))^(p/2) - tan(pi/2p) cos(pt/2).
# POINT CLAIM (main_points): one rational s_bad (= s_+) and one rational point (y*, t*), 0 <= t* < pi/p, with Psi_{p, s_bad}(y*, t*) < 0
#   (Arb upper bound < 0), and s_bad < sec^2(pi/2p). Gamma decreases in s (power means), so Gamma >= e fails for every s in
#   [s_bad, sec^2(pi/2p)], and the conjecture fails there (the failure proposition of the paper): s0(p) < s_bad.
#   The floating-point search only CHOOSES s_bad and the points; it is not part of the proof.
# CELL CLAIM (main_cells): one rational Delta > 0 per cell (delta in the code) with Psi_{p, sec^2(pi/2p) - Delta}(y*, t*) < 0 for every
#   p of each sub-cell (s is an Arb function of the p-ball), i.e. the conjecture fails on [sec^2(pi/2p) - Delta, sec^2(pi/2p)] for
#   every p of the cell. A cell where no Delta is proved is reported as NOT COVERED.
# One thread: OMP_NUM_THREADS = OPENBLAS_NUM_THREADS = MKL_NUM_THREADS = 1 is required (checked).
# Usage: python3 badcells_arb.py --points P1 P2 ... --digits D | --cells ... (see code/run_false_cells.sh) | --test
import argparse
import os
import sys
from fractions import Fraction

import flint
import numpy as np
from flint import arb, ctx
from scipy.optimize import minimize

ctx.prec = 100
GRID_Y, GRID_T, Y_MAX = 241, 361, 3.0


class CertFail(Exception):
    """A proof step did not go through."""


def require(cond, msg):
    if not cond:
        raise CertFail(msg)


def a_of(frac):
    return arb(frac.numerator) / arb(frac.denominator)


def psi_float(x, p, s):
    y, t = x
    return (-np.cosh(s * y / 2) ** (p / s) + ((np.cosh(y) + np.cos(t)) / (1 + np.cos(np.pi / p))) ** (p / 2)
            - np.tan(np.pi / (2 * p)) * np.cos(p * t / 2))


def psi_arb(p, s, y, t):
    """arb enclosure of Psi (p an arb ball; s, y, t arbs). cosh y + cos t > 0 is required (checked)."""
    w = (y.cosh() + t.cos()) / (1 + (arb.pi() / p).cos())
    require(w > 0, "base of the power is not positive")
    return -(((s * y) / 2).cosh() ** (p / s)) + w ** (p / 2) - (arb.pi() / (2 * p)).tan() * ((p * t) / 2).cos()


def float_min(p, s):
    """(min value, y*, t*) of Psi over y in [0, Y_MAX], t in [0, pi] away from the touching point (grid + L-BFGS)."""
    yy = np.linspace(0, Y_MAX, GRID_Y)[:, None]
    tt = np.linspace(0, np.pi, GRID_T)[None, :]
    vals = psi_float((yy, tt), p, s)
    best = (float(vals.min()), None, None)
    for idx in np.argsort(vals, axis=None)[:12]:
        i, j = np.unravel_index(idx, vals.shape)
        res = minimize(lambda x: psi_float(x, p, s), [yy[i, 0], tt[0, j]], bounds=[(0, Y_MAX), (0, np.pi)], method="L-BFGS-B",
                       options={"ftol": 1e-16, "gtol": 1e-13})
        if res.fun < best[0]:
            best = (float(res.fun), float(res.x[0]), float(res.x[1]))
    return best


def float_s0(p, iters=34, tol=1e-12):
    """Float threshold: largest s with min Psi >= -tol (bisection between p/(p-1) and sec^2)."""
    lo, hi = p / (p - 1), 1 / np.cos(np.pi / (2 * p)) ** 2
    for _ in range(iters):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if float_min(p, mid)[0] > -tol else (lo, mid)
    return hi


def rational_above(x, digits):
    return Fraction(int(np.ceil(x * 10 ** digits)), 10 ** digits)


def bad_upper(pa, pb, s, y, t):
    """Rigorous upper bound of Psi_{p, s}(y, t) over p in [pa, pb]."""
    return psi_arb(a_of(pa).union(a_of(pb)), a_of(s), a_of(y), a_of(t)).upper()


def prove_bad_cell(pa, pb, s, max_pieces=4000):
    """Adaptive p-bisection; each piece gets its own float-optimal rational point. Returns the list of (pa, pb, y, t, upper)."""
    require(a_of(s) < 1 / ((arb.pi() / (2 * a_of(pb))).cos() ** 2), f"s_bad = {s} is not below sec^2 at pb = {pb}")
    stack, done = [(pa, pb)], []
    while stack:
        aa, bb = stack.pop()
        require(len(done) + len(stack) < max_pieces, f"piece budget exceeded near p = {float(aa):.6f}")
        val, ys, ts = float_min(float((aa + bb) / 2), float(s))
        require(ys is not None and val < 0, f"float search finds no negative point at p = {float((aa + bb) / 2):.6f}, s = {s}")
        y, t = Fraction(round(ys * 10 ** 6), 10 ** 6), Fraction(round(ts * 10 ** 6), 10 ** 6)
        require(Fraction(0) <= t and a_of(t) < arb.pi() / a_of(bb), "t* must lie in [0, pi/p)")
        upper = bad_upper(aa, bb, s, y, t)
        if upper < 0:
            done.append((aa, bb, y, t, upper))
            continue
        require(bb - aa > Fraction(1, 10 ** 9), f"no proof on [{float(aa):.9f}, {float(bb):.9f}] at s = {s}")
        mid = (aa + bb) / 2
        stack.extend([(mid, bb), (aa, mid)])
    return sorted(done)


def sec2_float(p):
    return 1 / np.cos(np.pi / (2 * p)) ** 2


def s_offset(p_ball, delta):
    """arb enclosure of sec^2(pi/2p) - delta over the p-ball."""
    return 1 / ((arb.pi() / (2 * p_ball)).cos() ** 2) - a_of(delta)


def prove_offset_cell(pa, pb, delta, max_pieces=4000):
    """Like prove_bad_cell, with s = sec^2(pi/2p) - delta varying with p. Returns the list of (pa, pb, y, t, upper)."""
    require(delta > 0, f"delta = {delta} must be positive")
    stack, done = [(pa, pb)], []
    while stack:
        aa, bb = stack.pop()
        require(len(done) + len(stack) < max_pieces, f"piece budget exceeded near p = {float(aa):.6f}")
        pm = float((aa + bb) / 2)
        val, ys, ts = float_min(pm, sec2_float(pm) - float(delta))
        require(ys is not None and val < 0, f"float search finds no negative point at p = {pm:.6f}, delta = {delta}")
        y, t = Fraction(round(ys * 10 ** 6), 10 ** 6), Fraction(round(ts * 10 ** 6), 10 ** 6)
        require(Fraction(0) <= t and a_of(t) < arb.pi() / a_of(bb), "t* must lie in [0, pi/p)")
        p_ball = a_of(aa).union(a_of(bb))
        upper = psi_arb(p_ball, s_offset(p_ball, delta), a_of(y), a_of(t)).upper()
        if upper < 0:
            done.append((aa, bb, y, t, upper))
            continue
        require(bb - aa > Fraction(1, 10 ** 9), f"no proof on [{float(aa):.9f}, {float(bb):.9f}] at delta = {delta}")
        mid = (aa + bb) / 2
        stack.extend([(mid, bb), (aa, mid)])
    return sorted(done)


def main_points(ps, digits):
    """Per exact p: float s0, then s_bad = s0 rounded UP at `digits` digits plus one unit; proved bad point."""
    for p in ps:
        s0f = float_s0(float(p))
        s_bad = rational_above(s0f, digits) + Fraction(1, 10 ** digits)
        pieces = prove_bad_cell(p, p, s_bad)
        _a, _b, y, t, upper = pieces[0]
        sec2 = 1 / np.cos(np.pi / (2 * float(p))) ** 2
        print(f"POINT p = {p} ({float(p):.4f}): float s0 = {s0f:.7f}; Gamma >= e FAILS at s_bad = {s_bad} (sec^2 - s_bad = {sec2 - float(s_bad):.5f}) "
              f"at (y, t) = ({y}, {t}): Psi <= {float(upper):.3e}  PROVED", flush=True)


def main_cells(p_from, p_to, cells, digits, max_pieces, fractions):
    """Per cell: gap = smallest float sliver width sec^2 - s0 at the ends and midpoint; try delta = fraction * gap (rounded down at
    `digits` decimals) for the fractions in DEcreasing order; report the first that proves for every p, else NOT COVERED."""
    edges = [p_from + (p_to - p_from) * Fraction(k, cells) for k in range(cells + 1)]
    for pa, pb in zip(edges, edges[1:]):
        gap = min(sec2_float(float(pp)) - float_s0(float(pp)) for pp in (pa, (pa + pb) / 2, pb))
        result, reason = None, "no fraction tried"
        for frac in fractions:
            delta = Fraction(int(np.floor(float(frac) * gap * 10 ** digits)), 10 ** digits)
            try:
                result = (frac, delta, prove_offset_cell(pa, pb, delta, max_pieces))
                break
            except CertFail as err:
                reason = str(err)[:60]
        if result is None:
            print(f"BADCELL p in [{float(pa):.6f}, {float(pb):.6f}] (exact [{pa}, {pb}]): NOT COVERED (float gap {gap:.2e}; last: {reason})",
                  flush=True)
            continue
        frac, delta, pieces = result
        worst = max(float(piece[4]) for piece in pieces)
        print(f"BADCELL p in [{float(pa):.6f}, {float(pb):.6f}] (exact [{pa}, {pb}]): Gamma >= e FAILS at s = sec^2(pi/2p) - {delta} "
              f"({float(delta):.5f} = {frac} of float gap {gap:.5f}) for every p: {len(pieces)} pieces, max upper {worst:.2e}  PROVED", flush=True)


def run_tests():
    if not __debug__:
        raise SystemExit("tests need asserts: do not run with python -O")
    # (1) a known point (two interval reads): Psi = -8.93397e-4 at p = 3/2, s = 3.98, y = 0.567, t = 1.676
    val = psi_arb(a_of(Fraction(3, 2)), a_of(Fraction(398, 100)), a_of(Fraction(567, 1000)), a_of(Fraction(1676, 1000)))
    assert abs(float(val.mid()) + 8.933967616735896e-4) < 1e-15 and val.upper() < 0, val
    # (2) float s0(3/2) in (3.957, 3.96) (min(m - e) = +2.6e-8 at 3.957, -9.5e-5 at 3.96)
    s0 = float_s0(1.5)
    assert 3.957 < s0 < 3.96, s0
    # (3) NEGATIVE control: at s = 3.9 < s0 no bad cell can be proved
    try:
        prove_bad_cell(Fraction(3, 2), Fraction(3, 2), Fraction(39, 10))
        raise SystemExit("NEGATIVE CONTROL PASSED: a bad point proved at s = 3.9 < s0 - unsound")
    except CertFail as err:
        print(f"negative control failed as it must (s = 3.9): {str(err)[:70]}")
    # (4) s_bad must stay below sec^2 at the right end of the cell
    try:
        prove_bad_cell(Fraction(3, 2), Fraction(3, 2), Fraction(4))
        raise SystemExit("s_bad = sec^2 accepted - the range check is broken")
    except CertFail as err:
        print(f"range check works (s = sec^2 refused): {str(err)[:60]}")
    # (5) POSITIVE control: a narrow cell at s = 3.98
    pieces = prove_bad_cell(Fraction(3, 2), Fraction(3, 2) + Fraction(1, 1000), Fraction(398, 100))
    print(f"positive control: cell [1.5, 1.501] at s = 3.98 proved bad with {len(pieces)} pieces; float s0(3/2) = {s0:.7f}")
    # (6) offset mode: delta = 0.02 proves on [1.5, 1.501]; delta = 0.06 (s = 3.94 < s0 at p = 3/2) must NOT prove
    pieces = prove_offset_cell(Fraction(3, 2), Fraction(3, 2) + Fraction(1, 1000), Fraction(2, 100))
    print(f"offset positive control: cell [1.5, 1.501], s = sec^2 - 0.02 proved bad with {len(pieces)} pieces")
    try:
        prove_offset_cell(Fraction(3, 2), Fraction(3, 2), Fraction(6, 100))
        raise SystemExit("NEGATIVE CONTROL PASSED: offset delta = 0.06 proved bad at p = 3/2 - unsound")
    except CertFail as err:
        print(f"offset negative control failed as it must (delta = 0.06): {str(err)[:60]}")
    print("tests done")


def check_single_thread():
    """One thread: numpy/scipy (OpenBLAS) spawn threads unless these are set before Python starts."""
    unset = [name for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS") if os.environ.get(name) != "1"]
    if unset:
        raise SystemExit(f"set {', '.join(unset)}=1 before running (one thread only)")


def main():
    check_single_thread()
    parser = argparse.ArgumentParser()
    parser.add_argument("--points", type=Fraction, nargs="*")
    parser.add_argument("--p-from", type=Fraction)
    parser.add_argument("--p-to", type=Fraction)
    parser.add_argument("--cells", type=int)
    parser.add_argument("--digits", type=int, default=4, help="s_bad is rounded up at this many decimals")
    parser.add_argument("--max-pieces", type=int, help="cells mode: p-pieces allowed per attempt")
    parser.add_argument("--fractions", help="cells mode: decreasing comma list of fractions of the float sliver width, e.g. 9/10,1/2")
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        run_tests()
        return
    print(f"RUN argv = {' '.join(sys.argv)} | python {sys.version.split()[0]} | python-flint {flint.__version__} | prec {ctx.prec}", flush=True)
    if args.points:
        main_points(args.points, args.digits)
    if args.cells:
        require(args.max_pieces is not None and args.fractions is not None, "--cells needs --max-pieces and --fractions")
        fractions = [Fraction(ff) for ff in args.fractions.split(",")]
        require(fractions == sorted(fractions, reverse=True) and all(0 < ff < 1 for ff in fractions), "fractions: decreasing, in (0, 1)")
        main_cells(args.p_from, args.p_to, args.cells, args.digits, args.max_pieces, fractions)


if __name__ == "__main__":
    main()
