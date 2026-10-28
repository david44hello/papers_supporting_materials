#!/usr/bin/env python3
# point_arb.py - the point proposition: Arb enclosure (200 bits) of Gamma - e at p = 3/2, s = 199/50, y = log(9/5), t = pi/2.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# Gamma(y, t) - e(t) = ((cosh y + cos t)/(1 + cos 2th))^q - cosh(s y/2)^(p/s) - tan(th) cos(qt),  q = p/2, th = pi/(2p), |t| <= pi;
# psi_arb takes r = e^y and t/pi.
# --run: the enclosure, and the check that it lies inside the paper's window -4.17314647396549e-4 + [-1e-18, 1e-18]. Also
#   Jaguzovic's point (log 2, pi/2) at p = 3/2: Gamma - e < 0 certified at s = 39777/10000, hence for every s > 3.9777 (Gamma
#   decreases in s), and its value at s = 199/50.
# --test: controls. Jaguzovic's point (log 2, pi/2) at s = 4 gives -1.3102e-3; at s = 5/2 (inside the range s <= p/(p-1) = 3 where
#   Gamma >= e is known) the point of the proposition is not negative; a window shifted by 1e-17 does not contain the enclosure.
import argparse
import sys

import flint

PREC_BITS = 200
CENTER = "-4.17314647396549e-4"
RADIUS = "1e-18"
SHIFTED_CENTER = "-4.17314647396548e-4"
JAG_VALUE, JAG_RADIUS = "-1.3102e-3", "5e-8"


def psi_arb(p, s, r, t_over_pi):
    q = p / 2
    th = flint.arb.pi() / (2 * p)
    y = flint.arb(r).log()
    t = flint.arb.pi() * t_over_pi
    first = ((y.cosh() + t.cos()) / (1 + (2 * th).cos())) ** q
    second = (s * y / 2).cosh() ** (p / s)
    return first - second - th.tan() * (q * t).cos()


def rational(num, den=1):
    return flint.arb(num) / den


def point_value(s):
    """Gamma - e at p = 3/2, y = log(9/5), t = pi/2."""
    return psi_arb(rational(3, 2), s, rational(9, 5), rational(1, 2))


def main_run():
    value = point_value(rational(199, 50))
    inside = flint.arb(CENTER, RADIUS).contains(value)
    print(f"POINT p = 3/2, s = 199/50, y = log(9/5), t = pi/2: Gamma - e = {value.str(30, radius=True)}")
    print(f"POINT enclosure inside {CENTER} + [-{RADIUS}, {RADIUS}]: {'PROVED' if inside else 'NOT PROVED'}; "
          f"certified negative: {value < 0}")
    jag_cut = psi_arb(rational(3, 2), rational(39777, 10000), rational(2), rational(1, 2))
    jag_398 = psi_arb(rational(3, 2), rational(199, 50), rational(2), rational(1, 2))
    ok_jag = jag_cut < 0 and jag_398 < 0
    print(f"JAGUZOVIC point (log 2, pi/2), p = 3/2: s = 39777/10000: Gamma - e = {jag_cut.str(12, radius=True)}, certified "
          f"negative: {jag_cut < 0}; s = 199/50: Gamma - e = {jag_398.str(12, radius=True)}")
    return 0 if inside and value < 0 and ok_jag else 1


def main_test():
    jag = psi_arb(rational(3, 2), rational(4), rational(2), rational(1, 2))
    ok_jag = jag < 0 and flint.arb(JAG_VALUE, JAG_RADIUS).contains(jag)
    print(f"CONTROL Jaguzovic point (log 2, pi/2) at (3/2, 4): {jag.str(12, radius=True)}: {'matches' if ok_jag else 'MISMATCH'} {JAG_VALUE}")
    true_side = point_value(rational(5, 2))
    ok_true = not true_side < 0
    print(f"CONTROL s = 5/2 at the same point: {true_side.str(12, radius=True)}: {'not negative, as it must' if ok_true else 'WRONGLY NEGATIVE'}")
    ok_shift = not flint.arb(SHIFTED_CENTER, RADIUS).contains(point_value(rational(199, 50)))
    print(f"CONTROL window shifted by 1e-17: {'does not contain the enclosure, as it must' if ok_shift else 'WRONGLY CONTAINS IT'}")
    verdict = ok_jag and ok_true and ok_shift
    print(f"TESTS {'PASS' if verdict else 'FAIL'}")
    return 0 if verdict else 1


def main():
    parser = argparse.ArgumentParser(description="the point proposition in Arb (200 bits)")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--run", action="store_true", help="the enclosure and the window check")
    mode.add_argument("--test", action="store_true", help="the controls")
    args = parser.parse_args()
    flint.ctx.prec = PREC_BITS
    print(f"RUN argv = {' '.join(sys.argv)} | python {sys.version.split()[0]} | python-flint {flint.__version__} | prec {flint.ctx.prec}")
    sys.exit(main_test() if args.test else main_run())


if __name__ == "__main__":
    main()
