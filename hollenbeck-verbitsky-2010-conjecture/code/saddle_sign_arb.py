#!/usr/bin/env python3
# saddle_sign_arb.py - the saddle proposition: H > 0 and K > 0 on (4/3, 2), proved in Arb interval arithmetic (100 bits).
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# Notation: q = p/2, theta = pi/(2p), S = sec^2 theta, u = tan^2 theta = S - 1, tau = t - pi/p, and
#   Psi(y, t) = Gamma(y, t) - e(t) = ((cosh y + cos t)/(1 + cos(pi/p)))^(p/2) - cosh(sy/2)^(p/s) - tan(theta) cos(pt/2).
# Psi is even in y, and Psi = grad Psi = 0 at the contact point (0, pi/p). Taylor expansion at (0, pi/p) when s = S:
#   Psi = a02 tau^2 + a21 y^2 tau + a40 y^4 + O(|tau|^3 + y^2 tau^2 + y^4 |tau| + y^6),   a20 = (p/8)(S - s) = 0,
#   a02 = (p/8) K, K = (p - 1) u - 1;   a21 = p (2 - p) tan(theta) S / 16;   a40 = p S (S - 1)(S - 2) / 192.
# Along tau = -a21 y^2 / (2 a02): Psi = A y^4 + O(y^6), where A = a40 - a21^2 / (4 a02) = -p S u H / (384 K),
#   H(p) = -2 (p - 1) u^2 + (3 (2 - p)^2 + 2 p) u + 3 (2 - p)^2 - 2      (u = u(p)).
# Exact facts: u(4/3) = (1 + sqrt 2)^2 is a root of u^2 - 6u + 1, so H(4/3) = 0; u(2) = 1, H(2) = H'(2) = 0,
#   H''(2) = 12 + 2 pi - pi^2 > 0; K(2) = 0, K'(2) = 1 - pi/2 < 0.
# main_prove proves H > 0 and K > 0 on (4/3, 2), hence A < 0: at s = sec^2 theta the contact point is a saddle of Psi, so
#   Gamma < e at points arbitrarily close to it. For p < 4/3, H < 0 (A > 0): no saddle there.
# Usage: python3 saddle_sign_arb.py          (the proof)
#        python3 saddle_sign_arb.py --test   (closed forms against mpmath derivatives, exact values, a negative control)
import argparse
import sys
from fractions import Fraction

import flint
from flint import arb, ctx

ctx.prec = 100
P_LO, P_HI = Fraction(4, 3), Fraction(2)


class CertFail(Exception):
    """A proof step did not go through."""


def require(cond, msg):
    if not cond:
        raise CertFail(msg)


def a_of(frac):
    return arb(frac.numerator) / arb(frac.denominator)


def span(lo, hi):
    return a_of(lo).union(a_of(hi))


def u_derivs(p):
    """u = tan^2(pi/2p) and its first two p-derivatives (p an arb ball)."""
    th = arb.pi() / (2 * p)
    tt = th.tan()
    u = tt * tt
    th1, th2 = -th / p, 2 * th / (p * p)
    du, d2u = 2 * tt * (1 + u), 2 * (1 + u) * (1 + 3 * u)          # d/dtheta, d^2/dtheta^2
    return u, du * th1, d2u * th1 * th1 + du * th2


def h_parts(p, u):
    """h(p, u) and its partial derivatives (h is a polynomial)."""
    h = -2 * (p - 1) * u * u + (3 * (2 - p) ** 2 + 2 * p) * u + 3 * (2 - p) ** 2 - 2
    h_p = -2 * u * u + (2 - 6 * (2 - p)) * u - 6 * (2 - p)
    h_u = -4 * (p - 1) * u + 3 * (2 - p) ** 2 + 2 * p
    h_pp, h_pu, h_uu = 6 * u + 6, -4 * u - 6 * (2 - p) + 2, -4 * (p - 1)
    return h, h_p, h_u, h_pp, h_pu, h_uu


def big_h(p):
    """(H, H', H'') at p (total p-derivatives along u = u(p))."""
    u, u1, u2 = u_derivs(p)
    h, h_p, h_u, h_pp, h_pu, h_uu = h_parts(p, u)
    return h, h_p + h_u * u1, h_pp + 2 * h_pu * u1 + h_uu * u1 * u1 + h_u * u2


def big_k(p):
    """(K, K') with K = (p - 1) u - 1."""
    u, u1, _ = u_derivs(p)
    return (p - 1) * u - 1, u + (p - 1) * u1


def cover(lo, hi, test, max_boxes=100000):
    """Adaptive bisection of [lo, hi] until test(arb ball) holds on every piece; returns #pieces. Fails loudly."""
    stack, done, count = [(lo, hi)], 0, 0
    while stack:
        aa, bb = stack.pop()
        count += 1
        require(count <= max_boxes, f"budget exceeded near [{float(aa):.9g}, {float(bb):.9g}]")
        if test(span(aa, bb)):
            done += 1
            continue
        require(bb - aa > Fraction(1, 10 ** 15), f"test fails on [{float(aa):.12g}, {float(bb):.12g}]")
        mid = (aa + bb) / 2
        stack.extend([(aa, mid), (mid, bb)])
    return done


def prove_h_positive(a_cut, b_cut):
    """H > 0 on (4/3, 2): H(4/3) = 0 and H' > 0 on [4/3, a]; H > 0 on [a, b]; H(2) = H'(2) = 0 and H'' > 0 on [b, 2] (Taylor)."""
    h0 = big_h(a_of(P_LO))[0]
    h2, dh2, _ = big_h(a_of(P_HI))
    require(h0.contains(0) and h2.contains(0) and dh2.contains(0), "exact zeros H(4/3) = H(2) = H'(2) = 0 not enclosed")
    n1 = cover(P_LO, a_cut, lambda pp: big_h(pp)[1] > 0)
    n2 = cover(a_cut, b_cut, lambda pp: big_h(pp)[0] > 0)
    n3 = cover(b_cut, P_HI, lambda pp: big_h(pp)[2] > 0)
    return n1, n2, n3


def prove_k_positive(b_cut):
    """K > 0 on [4/3, 2): K > 0 on [4/3, b]; K(2) = 0 and K' < 0 on [b, 2] (mean value)."""
    require(big_k(a_of(P_HI))[0].contains(0), "exact zero K(2) = 0 not enclosed")
    return cover(P_LO, b_cut, lambda pp: big_k(pp)[0] > 0), cover(b_cut, P_HI, lambda pp: big_k(pp)[1] < 0)


def coeffs(p):
    """Closed forms (a02, a21, a40, A) at s = S, as arbs."""
    th = arb.pi() / (2 * p)
    tt = th.tan()
    u = tt * tt
    big_s = 1 + u
    kk = (p - 1) * u - 1
    a02, a21, a40 = p * kk / 8, p * (2 - p) * tt * big_s / 16, p * big_s * u * (big_s - 2) / 192
    return a02, a21, a40, -p * big_s * u * big_h(p)[0] / (384 * kk)


def main_prove(a_cut, b_cut):
    print(f"RUN argv = {' '.join(sys.argv)} | python {sys.version.split()[0]} | python-flint {flint.__version__} | prec {ctx.prec}")
    n1, n2, n3 = prove_h_positive(a_cut, b_cut)
    print(f"H > 0 on (4/3, 2): PROVED  (H' > 0 on [4/3, {a_cut}]: {n1} pieces; H > 0 on [{a_cut}, {b_cut}]: {n2} pieces; "
          f"H'' > 0 on [{b_cut}, 2]: {n3} pieces; exact zeros H(4/3) = H(2) = H'(2) = 0)")
    k1, k2 = prove_k_positive(b_cut)
    print(f"K > 0 on [4/3, 2): PROVED  (K > 0 on [4/3, {b_cut}]: {k1} pieces; K(2) = 0, K' < 0 on [{b_cut}, 2]: {k2} pieces)")
    print("=> A(p) = -p S u H / (384 K) < 0 for every p in (4/3, 2): (0, pi/p) is a saddle of Psi at s = sec^2(pi/2p).")
    for pp in (Fraction(7, 5), Fraction(3, 2), Fraction(17, 10), Fraction(19, 10)):
        a02, a21, a40, big_a = coeffs(a_of(pp))
        print(f"  p = {pp}: a02 = {float(a02.mid()):.6f}, a21 = {float(a21.mid()):.6f}, a40 = {float(a40.mid()):.6f}, A = {float(big_a.mid()):.6f}")


def psi_mp(mp, p, s, y, t):
    return (-mp.cosh(s * y / 2) ** (p / s) + ((mp.cosh(y) + mp.cos(t)) / (1 + mp.cos(mp.pi / p))) ** (p / 2)
            - mp.tan(mp.pi / (2 * p)) * mp.cos(p * t / 2))


def test_coefficients(mp):
    """Closed forms = mpmath numerical derivatives of Psi at the touching point, and Psi on the valley curve / y^4 -> A."""
    for pf in (Fraction(7, 5), Fraction(3, 2), Fraction(17, 10), Fraction(19, 10)):
        p = mp.mpf(pf.numerator) / pf.denominator
        s, t0 = 1 / mp.cos(mp.pi / (2 * p)) ** 2, mp.pi / p
        a02, a21, a40, big_a = (mp.mpf(vv.str(28, radius=False)) for vv in coeffs(a_of(pf)))
        num_a02 = mp.diff(lambda tt: psi_mp(mp, p, s, 0, tt), t0, 2) / 2
        num_a21 = mp.diff(lambda yy, tt: psi_mp(mp, p, s, yy, tt), (0, t0), (2, 1)) / 2
        num_a40 = mp.diff(lambda yy: psi_mp(mp, p, s, yy, t0), 0, 4) / 24
        num_a20 = mp.diff(lambda yy: psi_mp(mp, p, s, yy, t0), 0, 2) / 2
        assert abs(num_a20) < 1e-20 and abs(num_a02 - a02) < 1e-15 and abs(num_a21 - a21) < 1e-15 and abs(num_a40 - a40) < 1e-15, pf
        y = mp.mpf("1e-3")
        on_curve = psi_mp(mp, p, s, y, t0 - a21 * y * y / (2 * a02)) / y ** 4
        assert abs(on_curve - big_a) < 1e-4 and on_curve < 0, (pf, on_curve, big_a)
    print("closed forms a02, a21, a40 = mpmath derivatives at p = 7/5, 3/2, 17/10, 19/10; Psi / y^4 on the valley curve -> A < 0")


def test_exact_values():
    """A(3/2) = -3/32; H(4/3) = H(2) = H'(2) = 0; H''(2) = 12 + 2 pi - pi^2; negative control A(13/10) > 0 (p < 4/3)."""
    assert (coeffs(a_of(Fraction(3, 2)))[3] + arb(3) / 32).contains(0)
    h0, h2, dh2 = big_h(a_of(P_LO))[0], big_h(a_of(P_HI))[0], big_h(a_of(P_HI))[1]
    assert h0.contains(0) and h0.rad() < 1e-25 and h2.contains(0) and dh2.contains(0)
    assert (big_h(a_of(P_HI))[2] - (12 + 2 * arb.pi() - arb.pi() ** 2)).contains(0)
    assert coeffs(a_of(Fraction(13, 10)))[3] > 0, "negative control: A should be > 0 for p < 4/3"
    print("A(3/2) = -3/32; H(4/3) = 0 (radius < 1e-25); H(2) = H'(2) = 0; H''(2) = 12 + 2pi - pi^2; control A(13/10) > 0")


def test_derivatives():
    """H', H'', K' = central differences of H, K at 50 points."""
    step = arb(1) / 10 ** 8
    for kk in range(50):
        p = a_of(Fraction(4, 3) + Fraction(2, 3) * Fraction(kk, 50) + Fraction(1, 300))
        hm, h0, hp = big_h(p - step)[0], big_h(p), big_h(p + step)[0]
        fd1, fd2 = (hp - hm) / (2 * step), (hp - 2 * h0[0] + hm) / (step * step)
        kd = (big_k(p + step)[0] - big_k(p - step)[0]) / (2 * step)
        assert abs(float((fd1 - h0[1]).mid())) < 1e-6 and abs(float((fd2 - h0[2]).mid())) < 1e-4
        assert abs(float((kd - big_k(p)[1]).mid())) < 1e-6
    print("H', H'', K' = finite differences at 50 points")


def run_tests():
    if not __debug__:
        raise SystemExit("tests need asserts: do not run with python -O")
    import mpmath
    mpmath.mp.dps = 40
    test_exact_values()
    test_derivatives()
    test_coefficients(mpmath.mp)
    try:
        cover(Fraction(13, 10), Fraction(4, 3), lambda pp: big_h(pp)[0] > 0, 2000)
        raise SystemExit("NEGATIVE CONTROL PASSED: H > 0 proved on [1.3, 4/3] where H < 0 - unsound")
    except CertFail as err:
        print(f"negative control failed as it must (H < 0 on [13/10, 4/3]): {str(err)[:70]}")
    print("tests done")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a-cut", type=Fraction, default=Fraction(4, 3) + Fraction(1, 100))
    parser.add_argument("--b-cut", type=Fraction, default=Fraction(2) - Fraction(1, 100))
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        run_tests()
        return
    main_prove(args.a_cut, args.b_cut)


if __name__ == "__main__":
    main()
