#!/usr/bin/env python3
# counterexample_beta_arb.py - the explicit counterexample, second independent code: the arc integrals by Euler's Beta function
#   plus delta-free integrals I1, I2 (Arb, 320 bits) and explicitly bounded O(delta) remainders.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# On T, |zw| = prod_j (2 sin(phi_j/2))^(-al_j), phi_j = theta - th_j mod 2pi, th_A = -delta/2, th_B = delta/2, th_C = pi;
# arg(zw) = -2pi/3, t*, b and log|z/w| = 0, y2, 0 on the arcs (-pi,-delta/2), (-delta/2,delta/2), (delta/2,pi)
# (checked by hand from the principal branches and gamma). With a = q al_A, bb = q al_B, c = q al_C, H0 = 2^-c, e1 = a + bb - 1 > 0:
#   2pi J_short = H0 delta^(-e1) B(1-a, 1-bb) (1 + [0, 3 delta^2])
#   2pi J_far(d) = H0 [delta^(-e1) B(1-d, e1) - (1-delta/2)^(-e1)/e1 (1 - [0, 2 delta])] + I1 + I2 + [+-R]   (d = bb for arc (delta/2, pi),
#                  d = a for arc (-pi, -delta/2)), I1 = int_0^1 th^(-a-bb) (H(th) - H0), I2 = int_1^pi (2 sin(th/2))^(-a-bb) (2 cos(th/2))^(-c),
#   H(th) = (2 sin(th/2)/th)^(-a-bb) (2 cos(th/2))^(-c); R = 40 (C2 + 1) delta (2pi J_far) collects every O(delta) term (bounds in run_read).
# int G = Gamma(y2, t*) J_short + Gamma(0, b) J_b + Gamma(0, -2pi/3) J_A, the last Gamma = 0 exactly (contact point).
# Usage: python3 counterexample_beta_arb.py --necks 2000 2200 ... --v-cut 120   (neck = ln(1/delta))   |   --test
import argparse
import sys
from fractions import Fraction

import flint
from flint import acb, arb, ctx

ctx.prec = 320


class CertFail(Exception):
    """A proof step did not go through."""


def require(cond, msg):
    if not cond:
        raise CertFail(msg)


def a_of(frac):
    return arb(frac.numerator) / arb(frac.denominator)


def beta(x, y):
    return x.gamma() * y.gamma() / (x + y).gamma()


def parameters(neck):
    """Exponents of the explicit counterexample (p = 3/2, t* = 179/100, b = 2pi/3 + 136/10000); neck = ln(1/delta)."""
    pp, tstar = a_of(Fraction(3, 2)), a_of(Fraction(179, 100))
    q = pp / 2
    b = 2 * arb.pi() / 3 + a_of(Fraction(136, 10000))
    al_a, al_b = tstar / arb.pi() + arb(2) / 3, (b - tstar) / arb.pi()
    al_c = 2 - al_a - al_b
    expo = {"a": q * al_a, "bb": q * al_b, "c": q * al_c}
    require(all(0 < vv < 1 for vv in expo.values()), "exponents q al_j must lie in (0, 1) (z, w in H^p)")
    require(expo["a"] + expo["bb"] > 1, "neck exponent a + bb - 1 must be positive")
    return pp, q, b, tstar, expo, arb(neck)


def gamma_fn(pp, s, y, t):
    """Gamma(y, t) of the paper (averaged power mean normalisation)."""
    q = pp / 2
    return ((y.cosh() + t.cos()) / (1 + (arb.pi() / pp).cos())) ** q - ((s * y) / 2).cosh() ** (pp / s)


def h_of(th, a_plus_b, c, analytic):
    """H(th) = (2 sin(th/2)/th)^(-a-bb) (2 cos(th/2))^(-c) as an acb, principal branches (checked when analytic)."""
    sig = (th / 2).sinc()                                      # = 2 sin(th/2)/th, finite on boxes containing 0
    cs = 2 * (th / 2).cos()
    return (-(a_plus_b) * sig.log(analytic=analytic) - c * cs.log(analytic=analytic)).exp()


def integral_i1(expo, v_cut):
    """I1 = int_0^1 th^(-a-bb)(H - H0) dth: th = e^v on [-v_cut, 0] in Arb, plus the [0, e^-v_cut] piece bounded by C2."""
    apb, c = expo["a"] + expo["bb"], expo["c"]
    h0 = arb(2) ** (-c)

    def integrand(v, analytic):
        th = v.exp()
        return (v * (1 - apb)).exp() * (h_of(th, apb, c, analytic) - h0)
    main = acb.integral(integrand, -v_cut, 0).real
    c2 = c2_bound(expo)
    tail = c2 * (-(3 - apb) * v_cut).exp() / (3 - apb)
    return main + arb(0, tail.upper()), c2


def integral_i2(expo, v_cut):
    """I2 = int_1^pi (2 sin(th/2))^(-a-bb)(2 cos(th/2))^(-c) dth; phi = pi - th = e^v on [-v_cut, log(pi - 1)], tail bounded."""
    apb, c = expo["a"] + expo["bb"], expo["c"]

    def integrand(v, analytic):
        phi = v.exp()
        sig = (phi / 2).sinc()                                 # (2 sin(phi/2))^(-c) = phi^(-c) sig^(-c)
        cs = 2 * (phi / 2).cos()
        return ((1 - c) * v - c * sig.log(analytic=analytic) - apb * cs.log(analytic=analytic)).exp()
    main = acb.integral(integrand, -v_cut, (arb.pi() - 1).log()).real
    tail = 2 * (-(1 - c) * v_cut).exp() / (1 - c)            # 0 < integrand <= 2 phi^(-c) on [0, e^-v_cut] (sig^-c, cos^-(a+bb) <= 1.01)
    return main + arb(0, tail.upper())


def c2_bound(expo):
    """C2 >= sup_[0,1] |H(th) - H0| / th^2 via Cauchy: |H''| <= 2 M / r^2 on [0, 1], r = 3/2, M = max |H| on |zeta| <= 5/2."""
    apb, c = expo["a"] + expo["bb"], expo["c"]
    big_m = arb(0)
    steps = 720
    for kk in range(steps):                                    # max modulus principle: |H| on the circle |zeta| = 5/2
        ang = arb.pi() * 2 * arb(kk) / steps
        ang_ball = ang.union(arb.pi() * 2 * arb(kk + 1) / steps)
        zeta = acb(arb(5) / 2) * acb(0, ang_ball).exp()
        val = h_of(zeta, apb, c, True)
        require(val.is_finite(), "H not analytic on a box of the circle |zeta| = 5/2")
        upper = abs(val).upper()
        if upper > big_m:
            big_m = upper
    require(disc_is_analytic(apb, c), "H is not analytic on the disc |zeta| <= 5/2 (branch cut touched)")
    return big_m / (arb(3) / 2) ** 2


def disc_is_analytic(apb, c):
    """Principal branches of sigma(zeta) and 2 cos(zeta/2) stay off the cut on a box cover of |zeta| <= 5/2."""
    n_box = 40
    width = Fraction(5, n_box)
    for ix in range(n_box):
        for iy in range(n_box):
            x0, y0 = Fraction(-5, 2) + width * ix, Fraction(-5, 2) + width * iy
            near_x = min(abs(x0), abs(x0 + width)) if x0 * (x0 + width) > 0 else Fraction(0)
            near_y = min(abs(y0), abs(y0 + width)) if y0 * (y0 + width) > 0 else Fraction(0)
            if near_x ** 2 + near_y ** 2 > Fraction(25, 4):  # box misses the disc |zeta| <= 5/2 (exact rational test)
                continue
            box = acb(a_of(x0).union(a_of(x0 + width)), a_of(y0).union(a_of(y0 + width)))
            if not h_of(box, apb, c, True).is_finite():
                return False
    return True


def arc_integrals(expo, neck, i1, i2, c2):
    """(J_A, J_short, J_b) with the O(delta) remainders included as ball radii."""
    a, bb, c = expo["a"], expo["bb"], expo["c"]
    e1, h0 = a + bb - 1, arb(2) ** (-c)
    delta = (-neck).exp()
    big = (neck * e1).exp()                                    # delta^(-e1)
    j_short = h0 * big * beta(1 - a, 1 - bb) * (1 + arb(0, (3 * delta * delta).upper()))

    def far(d_exp):
        tail = (1 - delta / 2) ** (-e1) / e1 * (1 - arb(delta, delta))
        core = h0 * (big * beta(1 - d_exp, e1) - tail) + i1 + i2
        return core * (1 + arb(0, (40 * (c2 + 1) * delta).upper()))
    two_pi = 2 * arb.pi()
    return far(a) / two_pi, j_short / two_pi, far(bb) / two_pi


def run_read(neck, s_frac, y2_frac, v_cut):
    pp, q, b, tstar, expo, neck_a = parameters(neck)
    s, y2 = a_of(s_frac), a_of(y2_frac)
    i1, c2 = integral_i1(expo, arb(v_cut))
    i2 = integral_i2(expo, arb(v_cut))
    j_a, j_short, j_b = arc_integrals(expo, neck_a, i1, i2, c2)
    g_short, g_b, g_a = gamma_fn(pp, s, y2, tstar), gamma_fn(pp, s, arb(0), b), gamma_fn(pp, s, arb(0), -2 * arb.pi() / 3)
    require(g_a.contains(0) and g_a.rad() < 1e-80, "Gamma(0, -2pi/3) must be 0 (contact point)")
    total = g_short * j_short + g_b * j_b                       # + 0 * J_A
    return {"expo": expo, "I1": i1, "I2": i2, "C2": c2, "J": (j_a, j_short, j_b), "Gamma": (g_a, g_short, g_b), "total": total}


def show(tag, res):
    ex = res["expo"]
    print(f"{tag}: a = {ex['a'].str(12)}, bb = {ex['bb'].str(12)}, c = {ex['c'].str(12)}, a + bb - 1 = {(ex['a'] + ex['bb'] - 1).str(12)}")
    print(f"   I1 = {res['I1'].str(15)}, I2 = {res['I2'].str(15)}, C2 <= {float(res['C2'].upper()):.3f}")
    print(f"   J (arcs -2pi/3, t*, b) = {', '.join(jj.str(15) for jj in res['J'])}")
    print(f"   Gamma = {', '.join(gg.str(15) for gg in res['Gamma'])}")
    print(f"   int G = sum Gamma_j J_j = {res['total'].str(15)}", flush=True)


def brute_arcs(neck, dps=40):
    """Direct mpmath quadrature of the three arc integrals at delta = e^-neck (moderate neck only): a check of the Beta formulas."""
    import mpmath as mp
    mp.mp.dps = dps
    q, t_s = mp.mpf(3) / 4, mp.mpf(179) / 100
    b = 2 * mp.pi / 3 + mp.mpf(136) / 10000
    al_a, al_b = t_s / mp.pi + mp.mpf(2) / 3, (b - t_s) / mp.pi
    al_c = 2 - al_a - al_b
    delta = mp.exp(-neck)
    a, bb, c = q * al_a, q * al_b, q * al_c
    v_lo = -2000                                               # tail below e^v_lo is ~ e^(-2000 (1 - a)) relative: negligible

    def quad_v(fn, v_hi):
        pts = [mp.mpf(v_lo) + 25 * kk for kk in range(int((v_hi - v_lo) / 25) + 1)] + [v_hi]
        return mp.quad(fn, sorted(set(pts)))

    def far(e_near, e_other):                                  # distance d = e^v from the near end (theta = +-(delta/2 + d))
        def fn(v):
            d = mp.exp(v)
            return d * (2 * mp.sin(d / 2)) ** (-e_near) * (2 * mp.sin((d + delta) / 2)) ** (-e_other) * (2 * mp.cos((delta / 2 + d) / 2)) ** (-c)
        return quad_v(fn, mp.log(mp.pi - delta / 2)) / (2 * mp.pi)

    def short_half(e_near, e_other):                           # d from one end of the short arc up to its midpoint
        def fn(v):
            d = mp.exp(v)
            return d * (2 * mp.sin(d / 2)) ** (-e_near) * (2 * mp.sin((delta - d) / 2)) ** (-e_other) * (2 * mp.cos((d - delta / 2) / 2)) ** (-c)
        return quad_v(fn, mp.log(delta / 2))
    j_short = (short_half(a, bb) + short_half(bb, a)) / (2 * mp.pi)
    return far(a, bb), j_short, far(bb, a)


def run_tests():
    if not __debug__:
        raise SystemExit("tests need asserts: do not run with python -O")
    neck = 30
    res = run_read(neck, Fraction(398, 100), Fraction(4865, 10000), 120)
    brute = brute_arcs(neck)
    for name, mine, ref in zip(("J_A", "J_short", "J_b"), res["J"], brute):
        rel = abs(float(mine.mid()) - float(ref)) / float(ref)
        print(f"test ln(1/delta) = {neck}: {name} Beta formula {float(mine.mid()):.12f} vs direct quadrature {float(ref):.12f} (rel {rel:.1e})")
        assert rel < 1e-9, (name, rel)
    print("tests done")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--necks", type=int, nargs="+", help="values of ln(1/delta)")
    parser.add_argument("--v-cut", type=int, help="log-scale cut for I1, I2 (tails bounded)")
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        run_tests()
        return
    require(args.necks is not None and args.v_cut is not None, "--necks and --v-cut are required")
    print(f"RUN argv = {' '.join(sys.argv)} | python {sys.version.split()[0]} | python-flint {flint.__version__} | prec {ctx.prec}", flush=True)
    for neck in args.necks:
        show(f"ln(1/delta) = {neck}", run_read(neck, Fraction(398, 100), Fraction(4865, 10000), args.v_cut))


if __name__ == "__main__":
    main()
