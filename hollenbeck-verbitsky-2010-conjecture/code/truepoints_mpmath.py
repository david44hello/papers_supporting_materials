#!/usr/bin/env python3
# truepoints_mpmath.py - the lower bounds s_- of the bracket proposition, second independent code (mpmath interval arithmetic on
#   the compact (r, t) form): Gamma >= e HOLDS at the six (p, s_-).
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# Gamma >= e <=> Phi(r,t) := e^{-q|y|} (Gamma - e) = kap P^q - Q^(p/s) - tan(th) cos(qt) r^q >= 0 on [0,1] x [0,pi], with r = e^{-|y|},
# P = (1 + r^2)/2 + r cos t, Q = (1 + r^s)/2, kap = (2 cos^2 th)^(-q), q = p/2, th = pi/(2p) (evenness in y and t; compact, no tail).
# (C) touching box W = [-eps, eps] x [pi/p - eps, pi/p + eps] in (y,t): interval Hessian of Psi = Gamma - e positive definite on
#     sub-boxes => Psi convex on W; Psi = grad Psi = 0 at (0, pi/p) (the contact lemma + evenness) => Psi >= 0 on W.
# (B) the rest: adaptive bisection, lower bound = max(naive interval, mean-value form with interval gradient).
# Written independently of certify_arb.py: own formulas, mpmath iv, own domain.
# Usage: python3 truepoints_mpmath.py --test | --run | --cells
#   --cells is a stress test on three thin cells of the cell proposition. The cell [79/40, 99/50] is NOT proved by this code (the
#   run stops at a box it cannot certify); the cell proposition rests on certify_arb.py alone, as the paper states.
import sys
import time
import mpmath
from mpmath import iv, mp, mpf

iv.dps = 30
mp.dps = 36                                  # mp precision > iv precision: end points from iv are exact in mp
MIN_WIDTH = mpf("1e-9")                      # a box narrower than this that is not certified = FAIL
EPS_LIST = [mpf(1) / k for k in (10, 20, 40, 80, 160, 320, 640, 1280)]
HESS_SPLIT = 8                               # sub-boxes per side for the Hessian check
MAX_BOXES = 2_000_000


def lo(x):
    """Exact lower end point as an mpf (x.a.a is still an ivmpf)."""
    return mpf(iv.mpf(x)._mpi_[0])


def hi(x):
    """Exact upper end point as an mpf."""
    return mpf(iv.mpf(x)._mpi_[1])


def edges(start, stop, pieces):
    """pieces + 1 end points from start to stop; first and last EXACTLY start and stop (no rounding gap)."""
    inner = [start + (stop - start) * k / pieces for k in range(1, pieces)]
    return [start] + inner + [stop]


def cosh_iv(x):
    """Tight interval cosh (mpmath iv has none): even, increasing in |x|; end points from exp of point intervals."""
    at = lambda v: (iv.exp(iv.mpf(v)) + iv.exp(-iv.mpf(v))) / 2
    a, b = lo(x), hi(x)
    if a >= 0:
        return iv.mpf([lo(at(a)), hi(at(b))])
    if b <= 0:
        return iv.mpf([lo(at(b)), hi(at(a))])
    return iv.mpf([mpf(1), max(hi(at(a)), hi(at(b)))])


def sinh_iv(x):
    """Tight interval sinh (increasing)."""
    at = lambda v: (iv.exp(iv.mpf(v)) - iv.exp(-iv.mpf(v))) / 2
    return iv.mpf([lo(at(lo(x))), hi(at(hi(x)))])


def rational_iv(text):
    """'a/b' -> interval enclosure of a/b; 'a/b:c/d' -> the whole cell [a/b, c/d] (every p in it at once)."""
    if ":" in text:
        left, right = text.split(":")
        return iv.mpf([lo(rational_iv(left)), hi(rational_iv(right))])
    num, den = (int(part) for part in text.split("/"))
    return iv.mpf(num) / iv.mpf(den)


def constants(p, s):
    """Interval constants for exact rationals p, s (given as mpmath iv numbers)."""
    q = p / 2
    th = iv.pi / (2 * p)
    return {"p": p, "s": s, "q": q, "kap": (2 * iv.cos(th) ** 2) ** (-q), "tan": iv.tan(th), "c": iv.pi / p}


def phi_box(cst, rr, tt):
    """Naive interval extension of Phi on the box rr x tt (P clamped to its true range P >= 0)."""
    q, s, p = cst["q"], cst["s"], cst["p"]
    pp = (1 + rr ** 2) / 2 + rr * iv.cos(tt)
    pp = iv.mpf([max(mpf(0), lo(pp)), hi(pp)])
    return cst["kap"] * pp ** q - ((1 + rr ** s) / 2) ** (p / s) - cst["tan"] * iv.cos(q * tt) * rr ** q


def grad_box(cst, rr, tt):
    """Interval gradient (Phi_r, Phi_t, Phi_p) on the box (p = the interval in cst), or None where it is singular (r = 0 or P = 0).
    Phi_p (by hand): kap P^q = exp(q ln(P/(2cos^2 th))), th = pi/(2p): d/dp = kap P^q [ln(P/(2cos^2 th))/2 - pi tan(th)/(2p)];
    d/dp Q^(p/s) = Q^(p/s) ln(Q)/s; d/dp [tan(th) cos(qt) r^q] = r^q [tan' cos(qt) - tan(th) sin(qt) t/2 + tan(th) cos(qt) ln(r)/2],
    tan' = -(pi/(2p^2)) sec^2(th)."""
    q, s, p = cst["q"], cst["s"], cst["p"]
    pp = (1 + rr ** 2) / 2 + rr * iv.cos(tt)
    if lo(rr) <= 0 or lo(pp) <= 0:
        return None
    qq = (1 + rr ** s) / 2
    th = iv.pi / (2 * p)
    first = cst["kap"] * pp ** q
    d_r = q * cst["kap"] * pp ** (q - 1) * (rr + iv.cos(tt)) - q * qq ** (p / s - 1) * rr ** (s - 1) \
        - q * cst["tan"] * iv.cos(q * tt) * rr ** (q - 1)
    d_t = -q * cst["kap"] * pp ** (q - 1) * rr * iv.sin(tt) + q * cst["tan"] * iv.sin(q * tt) * rr ** q
    tan_p = -(iv.pi / (2 * p ** 2)) / iv.cos(th) ** 2
    d_p = first * (iv.log(pp / (2 * iv.cos(th) ** 2)) / 2 - iv.pi * cst["tan"] / (2 * p)) - qq ** (p / s) * iv.log(qq) / s \
        - rr ** q * (tan_p * iv.cos(q * tt) - cst["tan"] * iv.sin(q * tt) * tt / 2 + cst["tan"] * iv.cos(q * tt) * iv.log(rr) / 2)
    return d_r, d_t, d_p


def lower_bound(s, box):
    """max(naive, mean-value) lower bound of Phi on box = (p0, p1, r0, r1, t0, t1) (mpf end points), and the per-coordinate
    overestimation |grad_i| x width_i (for the split rule; None if the gradient is singular there)."""
    p0, p1, r0, r1, t0, t1 = box
    cst = constants(iv.mpf([p0, p1]), s)
    rr, tt = iv.mpf([r0, r1]), iv.mpf([t0, t1])
    best = lo(phi_box(cst, rr, tt))
    grad = grad_box(cst, rr, tt)
    if grad is None:
        return best, None
    pc, rc, tc = (p0 + p1) / 2, iv.mpf((r0 + r1) / 2), iv.mpf((t0 + t1) / 2)
    mv = phi_box(constants(iv.mpf(pc), s), rc, tc) + grad[0] * (rr - rc) + grad[1] * (tt - tc) \
        + grad[2] * (iv.mpf([p0, p1]) - iv.mpf(pc))
    mag = lambda x: max(abs(lo(x)), abs(hi(x)))
    spread = (mag(grad[2]) * (p1 - p0), mag(grad[0]) * (r1 - r0), mag(grad[1]) * (t1 - t0))
    return max(best, lo(mv)), spread


def hessian_pd(cst, yy, tt):
    """Interval Hessian of Psi(y,t) = Gamma - e positive definite on the box yy x tt (sufficient test)."""
    q, s, p, kap = cst["q"], cst["s"], cst["p"], cst["kap"]
    bb = cosh_iv(yy) + iv.cos(tt)
    if lo(bb) <= 0:
        return False
    ch, sh = cosh_iv(s * yy / 2), sinh_iv(s * yy / 2)
    psi_yy = q * kap * ((q - 1) * bb ** (q - 2) * sinh_iv(yy) ** 2 + bb ** (q - 1) * cosh_iv(yy)) \
        - (q * s / 2) * ((p / s - 1) * ch ** (p / s - 2) * sh ** 2 + ch ** (p / s))
    psi_yt = -q * (q - 1) * kap * bb ** (q - 2) * iv.sin(tt) * sinh_iv(yy)
    psi_tt = q * kap * (q - 1) * bb ** (q - 2) * iv.sin(tt) ** 2 - q * kap * bb ** (q - 1) * iv.cos(tt) \
        + q ** 2 * cst["tan"] * iv.cos(q * tt)
    off = max(abs(lo(psi_yt)), abs(hi(psi_yt)))
    return lo(psi_yy) > 0 and lo(psi_tt) > 0 and lo(psi_yy) * lo(psi_tt) > off ** 2


def touch_t_range(cst, eps):
    """t-range of W: [c_lo - eps, c_hi + eps], one definition for the Hessian check AND for inside_touch."""
    return lo(cst["c"]) - eps, hi(cst["c"]) + eps


def touching_box_ok(cst, eps):
    """Hessian PD on [0, eps] x t-range (evenness covers y < 0), checked on HESS_SPLIT^2 sub-boxes that tile W exactly."""
    y_edges = edges(mpf(0), eps, HESS_SPLIT)
    t_edges = edges(*touch_t_range(cst, eps), HESS_SPLIT)
    for i in range(HESS_SPLIT):
        for j in range(HESS_SPLIT):
            yy = iv.mpf([y_edges[i], y_edges[i + 1]])
            tt = iv.mpf([t_edges[j], t_edges[j + 1]])
            if not hessian_pd(cst, yy, tt):
                return False
    return True


def choose_eps(cst):
    """Largest eps in EPS_LIST whose touching box passes; None if none does."""
    for eps in EPS_LIST:
        if touching_box_ok(cst, eps):
            return eps
    return None


def inside_touch(box, cst, eps):
    """Box inside W (W is built for the WHOLE p-cell, so any p-sub-box is covered): r >= e^{-eps} and t in the W t-range."""
    p0, p1, r0, r1, t0, t1 = box
    w_t0, w_t1 = touch_t_range(cst, eps)
    return r0 >= hi(iv.exp(-iv.mpf(eps))) and t0 >= w_t0 and t1 <= w_t1


def split(box, spread):
    """Halve the coordinate with the largest |grad| x width (p, r, t); without a gradient, the widest of r, t/pi (p last)."""
    p0, p1, r0, r1, t0, t1 = box
    if spread is None:
        axis = 1 if (r1 - r0) * mp.pi >= (t1 - t0) else 2
    else:
        axis = max(range(3), key=lambda k: spread[k])
    lo_end, hi_end = box[2 * axis], box[2 * axis + 1]
    mid = (lo_end + hi_end) / 2
    left, right = list(box), list(box)
    left[2 * axis + 1], right[2 * axis] = mid, mid
    return [tuple(left), tuple(right)]


def too_small(box):
    p0, p1, r0, r1, t0, t1 = box
    return r1 - r0 < MIN_WIDTH and t1 - t0 < MIN_WIDTH


def branch_and_bound(cst, eps):
    """Certify Phi > 0 on p-cell x [0,1] x [0, pi_hi] minus the touching box. Returns (ok, n_boxes, min_lb, fail_box)."""
    p_iv, s = cst["p"], cst["s"]
    stack, n_boxes, min_lb = [(lo(p_iv), hi(p_iv), mpf(0), mpf(1), mpf(0), hi(iv.pi))], 0, None
    while stack:
        box = stack.pop()
        n_boxes += 1
        if n_boxes > MAX_BOXES:
            return False, n_boxes, min_lb, box
        if inside_touch(box, cst, eps):
            continue
        bound, spread = lower_bound(s, box)
        if bound > 0:
            min_lb = bound if min_lb is None else min(min_lb, bound)
            continue
        if too_small(box):
            return False, n_boxes, min_lb, box
        stack.extend(split(box, spread))
    return True, n_boxes, min_lb, None


def certify(p_text, s_text):
    """Gamma >= e at the rational point (p, s), e.g. ('3/2', '9893/2500'). Prints and returns True iff PROVED."""
    start = time.time()
    p, s = rational_iv(p_text), rational_iv(s_text)
    cst = constants(p, s)
    eps = choose_eps(cst)
    if eps is None:
        print(f"p = {p_text}, s = {s_text}: (C) touching box FAILS for every eps in the list -> NOT PROVED", flush=True)
        return False
    ok, n_boxes, min_lb, fail_box = branch_and_bound(cst, eps)
    tag = "PROVED" if ok else f"NOT PROVED (stuck box p [{mpmath.nstr(fail_box[0], 8)}, {mpmath.nstr(fail_box[1], 8)}], " \
                                f"r [{mpmath.nstr(fail_box[2], 8)}, {mpmath.nstr(fail_box[3], 8)}], " \
                                f"t [{mpmath.nstr(fail_box[4], 8)}, {mpmath.nstr(fail_box[5], 8)}])"
    lb_text = "none" if min_lb is None else mpmath.nstr(min_lb, 3)
    print(f"p = {p_text}, s = {s_text} ({mpmath.nstr(mpf(lo(s)), 7)}): Gamma >= e {tag}; (C) eps = 1/{int(1 / eps)}; (B) {n_boxes} boxes, "
          f"min certified lb {lb_text}; {time.time() - start:.0f} s", flush=True)
    return ok


def run_tests():
    """Positive control (3/2, 3.9); negative controls: s = sec^2 at 3/2 (= 4, touching box must fail) and s_+ = 3.9575 (B must fail)."""
    assert certify("3/2", "39/10"), "positive control"
    assert not certify("3/2", "4/1"), "s = sec^2 must fail"
    assert not certify("3/2", "39575/10000"), "s_+ must fail"
    print("tests: positive control, sec^2 control, s_+ control - PASS")


def main_truepoints():
    points = [("7/5", "26493/5000"), ("3/2", "9893/2500"), ("8/5", "31799/10000"), ("17/10", "26921/10000"),
              ("9/5", "5941/2500"), ("19/10", "5397/2500")]
    results = [certify(pp, ss) for pp, ss in points]
    print(f"ALL SIX PROVED: {all(results)}")


def main_thin_cells():
    """Stress test: the three cells of the cell proposition with the smallest certified lower bound in part (B) of certify_arb.py."""
    cells = [("1981/1000:991/500", "2025227/1000000"), ("1989/1000:199/100", "2013877/1000000"), ("79/40:99/50", "20281/10000")]
    results = [certify(pp, ss) for pp, ss in cells]
    print(f"ALL THREE CELLS PROVED: {all(results)}")


def main():
    if "--test" in sys.argv:
        run_tests()
    elif "--run" in sys.argv:
        main_truepoints()
    elif "--cells" in sys.argv:
        main_thin_cells()
    else:
        raise SystemExit("usage: truepoints_mpmath.py --test | --run | --cells")


if __name__ == "__main__":
    main()
