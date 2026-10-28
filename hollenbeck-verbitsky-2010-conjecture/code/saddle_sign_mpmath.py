#!/usr/bin/env python3
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
"""saddle_sign_mpmath.py - the saddle proposition: a second, independent interval check (mpmath iv) of H > 0, K > 0 on (4/3, 2).

Same split as the paper: dH/dp > 0 on [4/3, 403/300], H > 0 on [403/300, 199/100], d2H/dp2 > 0 on [199/100, 2];
K > 0 on [4/3, 199/100], dK/dp < 0 on [199/100, 2]. With H(4/3) = H(2) = H'(2) = 0 and K(2) = 0 this gives H > 0, K > 0 on (4/3, 2).
H(p, u) = -2(p-1)u^2 + (3(2-p)^2 + 2p)u + 3(2-p)^2 - 2,  K = (p-1)u - 1,  u(p) = tan^2(pi/2p). Total p-derivatives in closed form.
Every check bisects [a, b] (rational ends) until the interval enclosure of the quantity is > 0 on every piece; depth-limited,
loud failure. Three negative controls must fail. Usage: python3 saddle_sign_mpmath.py
"""
import argparse
import sys
from fractions import Fraction

from mpmath import iv

iv.dps = 40
MAX_DEPTH = 30


def u_derivs(p):
    """u, u', u'' at an interval p (u = T^2, T = tan(pi/2p), S = 1 + T^2)."""
    theta = iv.pi / (2 * p)
    tt = iv.tan(theta)
    ss = 1 + tt ** 2
    u0 = tt ** 2
    u1 = -(iv.pi / p ** 2) * tt * ss
    u2 = (2 * iv.pi / p ** 3) * tt * ss + (iv.pi ** 2 / (2 * p ** 4)) * ss * (ss + 2 * tt ** 2)
    return u0, u1, u2


def h_total(p, order):
    """H(p, u(p)) and its total p-derivatives (order 0, 1, 2)."""
    u0, u1, u2 = u_derivs(p)
    h_val = -2 * (p - 1) * u0 ** 2 + (3 * (2 - p) ** 2 + 2 * p) * u0 + 3 * (2 - p) ** 2 - 2
    h_p = -2 * u0 ** 2 + (6 * p - 10) * u0 + 6 * p - 12
    h_u = -4 * (p - 1) * u0 + 3 * (2 - p) ** 2 + 2 * p
    if order == 0:
        return h_val
    if order == 1:
        return h_p + h_u * u1
    h_pp = 6 * u0 + 6
    h_pu = -4 * u0 + 6 * p - 10
    h_uu = -4 * (p - 1)
    return h_pp + 2 * h_pu * u1 + h_uu * u1 ** 2 + h_u * u2


def k_total(p, order):
    """K(p, u(p)) (order 0) or its total p-derivative (order 1)."""
    u0, u1, _ = u_derivs(p)
    return (p - 1) * u0 - 1 if order == 0 else u0 + (p - 1) * u1


def positive_on(func, lo, hi, depth=0):
    """True iff func(interval) has a positive lower end on every piece of a bisection of [lo, hi]; returns (ok, pieces)."""
    enclosure = func(iv.mpf([iv.mpf(lo.numerator) / lo.denominator, iv.mpf(hi.numerator) / hi.denominator]))
    if enclosure.a > 0:
        return True, 1
    if enclosure.b <= 0 or depth >= MAX_DEPTH:  # surely not positive here, or out of depth: stop at the FIRST failure
        print(f"FAIL at [{float(lo)}, {float(hi)}]: enclosure {enclosure}", file=sys.stderr, flush=True)
        return False, 1
    mid = (lo + hi) / 2
    ok_left, n_left = positive_on(func, lo, mid, depth + 1)
    if not ok_left:
        return False, n_left
    ok_right, n_right = positive_on(func, mid, hi, depth + 1)
    return ok_right, n_left + n_right


CHECKS = [
    ("dH/dp > 0", lambda p: h_total(p, 1), Fraction(4, 3), Fraction(403, 300)),
    ("H > 0", lambda p: h_total(p, 0), Fraction(403, 300), Fraction(199, 100)),
    ("d2H/dp2 > 0", lambda p: h_total(p, 2), Fraction(199, 100), Fraction(2)),
    ("K > 0", lambda p: k_total(p, 0), Fraction(4, 3), Fraction(199, 100)),
    ("-dK/dp > 0", lambda p: -k_total(p, 1), Fraction(199, 100), Fraction(2)),
]

CONTROLS = [  # must FAIL: H vanishes at 4/3 and 2, K vanishes at 2, H < 0 below 4/3
    ("control H > 0 on [4/3, 403/300]", lambda p: h_total(p, 0), Fraction(4, 3), Fraction(403, 300)),
    ("control H > 0 on [13/10, 4/3]", lambda p: h_total(p, 0), Fraction(13, 10), Fraction(4, 3)),
    ("control K > 0 on [199/100, 2]", lambda p: k_total(p, 0), Fraction(199, 100), Fraction(2)),
]


def main_saddle_signs():
    """Run the five checks (must pass) and three controls (must fail); exit 0 only if all behave."""
    all_ok = True
    for name, func, lo, hi in CHECKS:
        ok, pieces = positive_on(func, lo, hi)
        print(f"{name} on [{lo}, {hi}]: {'PROVED' if ok else 'NOT PROVED'} ({pieces} pieces)")
        all_ok &= ok
    for name, func, lo, hi in CONTROLS:
        ok, pieces = positive_on(func, lo, hi)
        print(f"{name}: {'FAILS as it must' if not ok else 'WRONGLY PASSED'} ({pieces} pieces)")
        all_ok &= not ok
    print("ALL OK" if all_ok else "SOMETHING WRONG")
    return 0 if all_ok else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test", action="store_true", help="same as a normal run: checks + must-fail controls")
    parser.parse_args()
    sys.exit(main_saddle_signs())


if __name__ == "__main__":
    main()
