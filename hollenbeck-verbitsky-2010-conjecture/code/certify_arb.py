#!/usr/bin/env python3
# certify_arb.py - Arb certificate that Gamma >= e (so the conjecture holds) on a p-cell [pa, pb] at one rational s: the cell
#   proposition (140 cells), and, through truepoints_arb.py, the lower bounds s_- of the bracket proposition.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# Theorem shape. For a p-cell [pa, pb] and ONE rational s: Psi(y, t) >= 0 for all p in [pa, pb], y >= 0, t in [0, pi], where
#   Psi(y, t) = Gamma(y, t) - e(t) = -cosh(s y/2)^(p/s) + ((cosh y + cos t)/(1 + cos(pi/p)))^(p/2) - tan(pi/2p) cos(p t/2)
# (Melentijevic eq. (37)) = e^(py/2) Phi(e^-y, t), with Phi as in Jaguzovic. Psi >= 0 gives the conjecture at (p, s) (the method
# recalled in the paper), hence at every s' <= s (power means). Psi is even in y and t, so y >= 0, t in [0, pi] suffice.
# Parts (every part must pass; any failure is printed and the cell FAILS loudly):
#  (A) touching box N = {0 <= y <= ey, |t - pi/p| <= et}: interval Hessian of Psi positive definite for all p in the cell. Psi is then
#      convex on the convex box {|y| <= ey} x {|t - pi/p| <= et} (Psi even in y), whose point (0, pi/p) has Psi = 0, grad Psi = 0
#      (the contact lemma), so Psi >= 0 on N.
#  (B) y in [0, Y], t in [0, pi] minus N: adaptive bisection of (p, y, t) boxes until the lower bound of Psi is > 0 (the larger of
#      the naive interval bound and a mean-value bound, gradients by forward-mode automatic differentiation: arb_dual.py).
#  (C) y >= Y, i.e. r = e^-y in [0, R], R = e^-Y: same for Phi(r, t) (r-form; r^a handled as [0, R^a] near 0).
# Per cell, s is the rational just below p/(p-1) + kappa (sec^2(pi/2p) - p/(p-1)) at pb; the kappas are tried in increasing order
#   and the last that proves is kept.
# Usage: python3 certify_arb.py --test | --p-from A --p-to B --cells N --kappas K1,K2,... --ey E --et E --ymax Y --max-boxes M
import argparse
import sys
import time
from fractions import Fraction

import flint
from flint import arb, ctx

from arb_dual import NonPositiveBase, mean_value_lower

ctx.prec = 80
MIN_WIDTH = Fraction(1, 10 ** 12)      # a box this narrow in every coordinate that still fails is a genuine failure: stop there


class CertFail(Exception):
    """A proof step did not go through (never printed as PROVED)."""


def require(cond, msg):
    if not cond:
        raise CertFail(msg)


def a_of(frac):
    """Exact rational -> arb ball (exact up to precision of the division)."""
    return arb(frac.numerator) / arb(frac.denominator)


def span(lo, hi):
    """arb ball containing the real interval [lo, hi] (lo, hi rationals or arbs)."""
    lo = lo if isinstance(lo, arb) else a_of(lo)
    hi = hi if isinstance(hi, arb) else a_of(hi)
    return lo.union(hi)


def pos_pow(x, e):
    """x^e for an arb x known (mathematically) to be >= 0, e > 0; x's ball may dip below 0."""
    lo, hi = x.lower(), x.upper()
    up = hi ** e if hi > 0 else arb(0)
    down = lo ** e if lo > 0 else arb(0)
    return down.union(up)


def psi_box(p, s, y, t):
    """Interval enclosure of Psi over the box (p, y, t are arb balls; s an arb)."""
    first = -(((s * y) / 2).cosh() ** (p / s))
    w = (y.cosh() + t.cos()) / (1 + (arb.pi() / p).cos())
    second = pos_pow(w, p / 2)
    third = -(arb.pi() / (2 * p)).tan() * ((p * t) / 2).cos()
    return first + second + third


def psi_dual(p, y, t, s):
    """Psi with Dual (or arb) inputs p, y, t; s an arb. Needs W > 0 on the box (Dual pow raises NonPositiveBase otherwise)."""
    first = -((((s * y) / 2).cosh()) ** (p / s))
    w = (y.cosh() + t.cos()) / (1 + (arb.pi() / p).cos())
    second = w ** (p / 2)
    third = -(arb.pi() / (2 * p)).tan() * ((p * t) / 2).cos()
    return first + second + third


def psi_lower(p, s, y, t):
    """Best rigorous lower bound of Psi on the box: max(naive interval, mean-value form when W > 0 on the box)."""
    naive = psi_box(p, s, y, t).lower()
    try:
        mv, _ = mean_value_lower(lambda pp, yy, tt: psi_dual(pp, yy, tt, s), [p, y, t], [arb(p.mid()), arb(y.mid()), arb(t.mid())])
    except NonPositiveBase:
        return naive
    return max(naive, mv)


def phi_r_box(p, s, r, t):
    """Interval enclosure of Phi(r, t) (Jaguzovic (2)) for r in [0, R] small; r is an arb ball with r >= 0 mathematically."""
    c = (arb.pi() / (2 * p)).cos()
    a_term = -(((1 + pos_pow(r, s)) / 2) ** (p / s))
    b_term = pos_pow(1 + r * r + 2 * r * t.cos(), p / 2) / ((2 * c) ** p)
    c_term = -pos_pow(r, p / 2) * (arb.pi() / (2 * p)).tan() * ((t * p) / 2).cos()
    return a_term + b_term + c_term


def hessian_box(p, s, y, t):
    """Interval enclosures of (Psi_yy, Psi_tt, Psi_yt) over the box (checked against finite differences in --test)."""
    u, v = ((s * y) / 2).cosh(), ((s * y) / 2).sinh()
    f1_yy = -(p / 4) * ((p - s) * u ** (p / s - 2) * v * v + s * u ** (p / s))
    kap = (1 + (arb.pi() / p).cos()) ** (-p / 2)
    w = y.cosh() + t.cos()
    require(w > 0, "touching box reaches W = 0")
    w1, w2 = w ** (p / 2 - 1), w ** (p / 2 - 2)
    f2_yy = kap * (p / 2) * ((p / 2 - 1) * w2 * y.sinh() ** 2 + w1 * y.cosh())
    f2_tt = kap * (p / 2) * ((p / 2 - 1) * w2 * t.sin() ** 2 - w1 * t.cos())
    f2_yt = -kap * (p / 2) * (p / 2 - 1) * w2 * t.sin() * y.sinh()
    f3_tt = (arb.pi() / (2 * p)).tan() * (p * p / 4) * ((p * t) / 2).cos()
    return f1_yy + f2_yy, f2_tt + f3_tt, f2_yt


def hessian_pd(p, s, y, t):
    hyy, htt, hyt = hessian_box(p, s, y, t)
    return bool(hyy > 0 and htt > 0 and hyy * htt - hyt * hyt > 0), (hyy, htt, hyt)


def touching_box_ok(pa, pb, s, ey, et, max_boxes=200000):
    """(A): Hessian PD at every point of p in [pa, pb], y in [0, ey], t in [pi/pa... ] - checked on sub-boxes (PD is pointwise).
    The t-range [T_lo, T_hi] = [pi/pb - et, pi/pa + et] (rational outer bounds) contains every [pi/p - et, pi/p + et]."""
    t_lo = Fraction(int(float((arb.pi() / a_of(pb) - a_of(et)).lower()) * 10 ** 9) - 1, 10 ** 9)
    t_hi = Fraction(int(float((arb.pi() / a_of(pa) + a_of(et)).upper()) * 10 ** 9) + 1, 10 ** 9)
    require(a_of(t_lo) < arb.pi() / a_of(pb) - a_of(et) and a_of(t_hi) > arb.pi() / a_of(pa) + a_of(et), "touching t-range")
    stack, count, sa = [((pa, pb), (Fraction(0), ey), (t_lo, t_hi))], 0, a_of(s)
    while stack:
        box = stack.pop()
        count += 1
        if count > max_boxes:
            return False, f"budget {max_boxes} exceeded at {fmt_box(box)}"
        ok, _h = hessian_pd(span(*box[0]), sa, span(*box[1]), span(*box[2]))
        if not ok:
            if too_narrow(box):
                return False, f"Hessian not PD at {fmt_box(box)}"
            stack.extend(bisect(box, (Fraction(1, 2), Fraction(1), Fraction(1))))
    return True, f"{count} sub-boxes"


def inside_touching(pbox, ybox, tbox, ey, et):
    """True iff the box lies in N for EVERY p of its p-range (then (A) covers it)."""
    (pa, pb), (_ya, yb), (ta, tb) = pbox, ybox, tbox
    return (yb <= ey and bool(a_of(ta) >= arb.pi() / a_of(pa) - a_of(et)) and bool(a_of(tb) <= arb.pi() / a_of(pb) + a_of(et)))


def too_narrow(box):
    return all(hi - lo < MIN_WIDTH for lo, hi in box)


def fmt_box(box):
    """Short float text of a box (its exact rational ends can be very long)."""
    return " x ".join(f"[{float(lo):.9g}, {float(hi):.9g}]" for lo, hi in box)


def bisect(box, scales):
    widths = [(hi - lo) / sc for (lo, hi), sc in zip(box, scales)]
    k = widths.index(max(widths))
    lo, hi = box[k]
    mid = (lo + hi) / 2
    left, right = list(box), list(box)
    left[k], right[k] = (lo, mid), (mid, hi)
    return tuple(left), tuple(right)


def certify_region(s, root, value_fn, skip_fn, scales, max_boxes):
    """Adaptive bisection; returns (#leaves proved, min lower bound seen). Raises if max_boxes is exceeded."""
    stack, proved, worst, count = [root], 0, None, 0
    sa = a_of(s)
    while stack:
        box = stack.pop()
        count += 1
        require(count <= max_boxes, f"box budget {max_boxes} exceeded (s = {s})")
        if skip_fn(box):
            proved += 1
            continue
        low = value_fn(span(*box[0]), sa, span(*box[1]), span(*box[2]))
        if low > 0:
            proved += 1
            worst = low if worst is None or low < worst else worst
            continue
        require(not too_narrow(box), f"lower bound {float(low):.3e} <= 0 on {fmt_box(box)} (s = {s})")
        stack.extend(bisect(box, scales))
    return proved, worst


def certify_cell(pa, pb, s, ey, et, ymax, max_boxes):
    ok, info_a = touching_box_ok(pa, pb, s, ey, et)
    require(ok, f"(A) FAILS on [{pa}, {pb}], s = {s}: {info_a}")
    pi_hi = Fraction(355, 113)                     # > pi (3.14159292 > 3.14159265): t-range [0, 355/113] covers [0, pi]
    root_b = ((pa, pb), (Fraction(0), ymax), (Fraction(0), pi_hi))
    nb, wb = certify_region(s, root_b, psi_lower, lambda box: inside_touching(*box, ey, et), (Fraction(1, 2), Fraction(1), Fraction(1)),
                            max_boxes)
    root_c = ((pa, pb), (Fraction(0), rmax_cover(ymax)), (Fraction(0), pi_hi))      # r in [0, R], R >= e^-Y: covers all y >= Y
    nc, wc = certify_region(s, root_c, lambda *args: phi_r_box(*args).lower(), lambda box: False,
                            (Fraction(1, 2), Fraction(1, 4), Fraction(1)), max_boxes)
    return nb, wb, nc, wc


def rmax_cover(ymax):
    """A rational R with R >= e^-ymax (so r in [0, R] covers every y >= ymax), certified with arb."""
    cand = Fraction(int(1e6 * float((-a_of(ymax)).exp().upper())) + 1, 10 ** 6)
    require(a_of(cand) > (-a_of(ymax)).exp(), "R does not cover e^-Y")
    return cand


def s_for_cell(pa, pb, kappa):
    """Rational s just below kappa-way into the window at pb (both window ends decrease in p), asserted > pa/(pa - 1)."""
    p_hi = a_of(pb)
    s_lo, s_hi = p_hi / (p_hi - 1), 1 / ((arb.pi() / (2 * p_hi)).cos() ** 2)
    target = (s_lo + a_of(kappa) * (s_hi - s_lo)).lower()
    s = Fraction(int(float(target) * 10 ** 6) - 1, 10 ** 6)
    require(a_of(s) < s_lo + a_of(kappa) * (s_hi - s_lo), "s rounding")
    gain = a_of(s) - a_of(pa) / (a_of(pa) - 1)
    return s, gain


def prove_cell(pa, pb, kappa, ey, et, ymax, max_boxes):
    """One attempt: returns a result line, or raises CertFail."""
    start = time.time()
    s, gain = s_for_cell(pa, pb, kappa)
    require(gain > 0, f"cell [{pa}, {pb}]: s = {s} is not above p/(p-1) at pa (refine the cells)")
    for shrink in (1, 2, 4):                           # (A) needs a box where the Hessian stays PD; it shrinks as p -> 2
        if touching_box_ok(pa, pb, s, ey / shrink, et / shrink)[0]:
            break
    nb, wb, nc, wc = certify_cell(pa, pb, s, ey / shrink, et / shrink, ymax, max_boxes)
    return (f"CELL p in [{float(pa):.6f}, {float(pb):.6f}] (exact [{pa}, {pb}]) kappa = {kappa} s = {s} ({float(s):.6f}; above p/(p-1) "
            f"by >= {float(gain.lower()):.4f}): PROVED  (A) touching box ok (ey = et = {ey / shrink}); (B) {nb} boxes, min lb "
            f"{float(wb):.2e}; (C) {nc} boxes, min lb {float(wc):.2e}; {time.time() - start:.0f} s")


def main_certify(p_from, p_to, cells, kappas, ey, et, ymax, max_boxes):
    """For each cell: try the kappas in increasing order, keep the LAST that proves; stop at the first failure. No kappa proves -> exit 2."""
    edges = [p_from + (p_to - p_from) * Fraction(k, cells) for k in range(cells + 1)]
    for pa, pb in zip(edges, edges[1:]):
        best = None
        for kappa in kappas:
            try:
                best = prove_cell(pa, pb, kappa, ey, et, ymax, max_boxes)
            except CertFail as err:
                print(f"  cell [{float(pa):.6f}, {float(pb):.6f}] kappa = {kappa}: not proved ({str(err)[:70]})", flush=True)
                break
        if best is None:
            raise SystemExit(f"CELL [{pa}, {pb}]: NO kappa proved - certificate INCOMPLETE")
        print(best, flush=True)


def run_tests():
    if not __debug__:
        raise SystemExit("tests need asserts: do not run with python -O")
    # (1) touching point: Psi(0, pi/p) = 0 exactly (enclosure contains 0, tiny radius), for p = 3/2, s = 7/2
    val = psi_box(a_of(Fraction(3, 2)), a_of(Fraction(7, 2)), arb(0), arb.pi() / a_of(Fraction(3, 2)))
    assert val.contains(0) and val.rad() < 1e-15, val
    # (2) Hessian at the touching point = its closed forms
    p, s = Fraction(3, 2), Fraction(7, 2)
    hyy, htt, hyt = hessian_box(a_of(p), a_of(s), arb(0), arb.pi() / a_of(p))     # at the exact touching point
    th = arb.pi() / (2 * a_of(p))
    assert (hyy - a_of(p) / 4 * (1 / th.cos() ** 2 - a_of(s))).contains(0)
    assert (htt - a_of(p) / 4 * ((a_of(p) - 1) * th.tan() ** 2 - 1)).contains(0) and hyt.contains(0)
    # (3) NEGATIVE control on part (B): at s = sec^2 = 4 (p = 3/2) Psi < 0 near y = -log 0.56 = 0.58, t = 1.66: the region must NOT prove
    near = ((Fraction(3, 2), Fraction(3, 2)), (Fraction(55, 100), Fraction(61, 100)), (Fraction(163, 100), Fraction(169, 100)))
    try:
        certify_region(Fraction(4), near, psi_lower, lambda box: False, (Fraction(1, 2), Fraction(1), Fraction(1)), 5000)
        raise SystemExit("NEGATIVE CONTROL PASSED - the certifier is unsound")
    except CertFail as err:
        print(f"negative control (B) failed as it must: {str(err)[:80]}")
    ok, info = touching_box_ok(Fraction(3, 2), Fraction(3, 2), Fraction(4), Fraction(1, 20), Fraction(1, 20), 3000)
    assert not ok, "touching-box check passed at s = sec^2 where Psi_yy(0, pi/p) = 0 - unsound"
    print(f"negative control (A) failed as it must at s = sec^2: {info[:60]}")
    # (4) POSITIVE control: a narrow cell at p ~ 1.5, s = 3.4 (inside the numerically valid range)
    print(certify_cell(Fraction(3, 2), Fraction(3, 2) + Fraction(1, 1000), Fraction(17, 5), Fraction(1, 5), Fraction(1, 5), Fraction(3),
                       400000))
    # (5) Hessian formulas (used by part (A)) = finite differences of psi_box at 200 random points away from W = 0
    import random
    random.seed(5)
    def psi_f(pp, ss, yy, tt):
        return float(psi_box(arb(pp), arb(ss), arb(yy), arb(tt)).mid())
    checked, step = 0, 1e-4
    while checked < 200:
        pp, ss, yy, tt = random.uniform(1.34, 1.99), random.uniform(2.0, 6.5), random.uniform(0.0, 1.5), random.uniform(0.2, 2.9)
        if float((arb(yy).cosh() + arb(tt).cos()).mid()) < 0.05:
            continue
        f0 = psi_f(pp, ss, yy, tt)
        fyy = (psi_f(pp, ss, yy + step, tt) - 2 * f0 + psi_f(pp, ss, yy - step, tt)) / step ** 2
        ftt = (psi_f(pp, ss, yy, tt + step) - 2 * f0 + psi_f(pp, ss, yy, tt - step)) / step ** 2
        fyt = (psi_f(pp, ss, yy + step, tt + step) - psi_f(pp, ss, yy + step, tt - step) - psi_f(pp, ss, yy - step, tt + step)
               + psi_f(pp, ss, yy - step, tt - step)) / (4 * step * step)
        hyy, htt, hyt = (float(vv.mid()) for vv in hessian_box(arb(pp), arb(ss), arb(yy), arb(tt)))
        assert max(abs(hyy - fyy), abs(htt - ftt), abs(hyt - fyt)) < 1e-5, ("Hessian formula mismatch", pp, ss, yy, tt)
        checked += 1
    print("Hessian formulas = finite differences at 200 random points")
    print("tests done")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--p-from", type=Fraction)
    parser.add_argument("--p-to", type=Fraction)
    parser.add_argument("--cells", type=int)
    parser.add_argument("--kappas", default="1/2", help="comma list, increasing, e.g. 1/2,3/5,7/10")
    parser.add_argument("--ey", type=Fraction, default=Fraction(1, 20))
    parser.add_argument("--et", type=Fraction, default=Fraction(1, 20))
    parser.add_argument("--ymax", type=Fraction, default=Fraction(3))
    parser.add_argument("--max-boxes", type=int, default=2_000_000)
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        run_tests()
        return
    kappas = [Fraction(kk) for kk in args.kappas.split(",")]
    require(kappas == sorted(kappas), "kappas must be increasing")
    print(f"RUN argv = {' '.join(sys.argv)} | python {sys.version.split()[0]} | python-flint {flint.__version__} | prec {ctx.prec}", flush=True)
    main_certify(args.p_from, args.p_to, args.cells, kappas, args.ey, args.et, args.ymax, args.max_boxes)


if __name__ == "__main__":
    main()
