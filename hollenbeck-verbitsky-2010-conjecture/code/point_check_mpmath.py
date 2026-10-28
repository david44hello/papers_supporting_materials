#!/usr/bin/env python3
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
"""point_check_mpmath.py - an independent interval check (mpmath iv, 50 digits) of the point proposition (p = 3/2, s = 3.98) and
of the six failure points s_+ of the bracket proposition, written from the paper's formulas only (its set-up).

The paper's set-up:  q = p/2,  th = pi/(2p),
    Gamma(y, t) = (cosh y + cos t)^q / (1 + cos 2th)^q - cosh(s y / 2)^(p/s),     e(t) = tan(th) cos(q t)   for |t| <= pi.
A claim "Gamma - e < 0" is CERTIFIED only when the upper end of the interval enclosure is < 0. Every input is an exact rational
(or log(9/5), pi/2), turned into a tight interval; nothing passes through floating point.
Usage: python3 point_check_mpmath.py --test | --run
"""
import argparse
import hashlib
import sys
from datetime import datetime
from fractions import Fraction
from pathlib import Path

import mpmath
from mpmath import iv

DIGITS = 50                    # interval working precision (decimal digits)
POINT_CENTER = "-4.17314647396549e-4"
POINT_RADIUS = "1e-18"
PAPER_WEAKEST_MARGIN = "-1.15e-6"   # paper, after the bracket proposition: from -1.15e-6 (at p = 7/5) to -5.7e-5 (at p = 9/5)
PAPER_STRONGEST_MARGIN = "-5.7e-5"

# Exact s_+ and failure points (y*, t*) as printed in logs/bracket_upper_arb.log, and the paper's s_- (table of the
# bracket proposition).
S_PLUS_POINTS = [
    # (p, s_plus, y_star, t_star, s_minus)
    ("7/5", "52989/10000", "110877/500000", "2144519/1000000", "26493/5000"),
    ("3/2", "1583/400", "49177/100000", "1768641/1000000", "9893/2500"),
    ("8/5", "15901/5000", "837049/1000000", "613161/500000", "31799/10000"),
    ("17/10", "1077/400", "298409/250000", "0", "26921/10000"),
    ("9/5", "23767/10000", "613873/500000", "0", "5941/2500"),
    ("19/10", "21591/10000", "625363/500000", "0", "5397/2500"),
]


def rational(text):
    """Exact rational string 'a/b' (or an integer) -> tight interval."""
    frac = Fraction(text)
    return iv.mpf(frac.numerator) / iv.mpf(frac.denominator)


def power(base, exponent):
    """base^exponent for a positive interval base."""
    if not base.a > 0:
        raise ValueError(f"power of a non-positive interval {base}")
    return iv.exp(exponent * iv.log(base))


def cosh(value):
    """cosh from exp (mpmath 1.2.1 iv has no cosh)."""
    return (iv.exp(value) + iv.exp(-value)) / 2


def gamma_minus_e(p_val, s_val, y_val, t_val):
    """Enclosure of Gamma(y, t) - e(t) for interval inputs, |t| <= pi (the paper's set-up)."""
    if not (t_val.b <= iv.pi.a and t_val.a >= -iv.pi.b):
        raise ValueError("t must lie in [-pi, pi] for e(t) = tan(th) cos(qt)")
    q_val = p_val / 2
    theta = iv.pi / (2 * p_val)
    first = power(cosh(y_val) + iv.cos(t_val), q_val) / power(1 + iv.cos(2 * theta), q_val)
    second = power(cosh(s_val * y_val / 2), p_val / s_val)
    return first - second - iv.tan(theta) * iv.cos(q_val * t_val)


def certified_negative(value):
    return bool(value.b < 0)


def inside(value, center, radius):
    """True when the whole enclosure lies in center + [-radius, radius]."""
    return bool(value.a >= center - radius) and bool(value.b <= center + radius)


def fmt(value):
    return f"[{mpmath.nstr(mpmath.mpf(value.a), 20)}, {mpmath.nstr(mpmath.mpf(value.b), 20)}]"


def point_enclosure(s_text):
    return gamma_minus_e(rational("3/2"), rational(s_text), iv.log(rational("9/5")), iv.pi / 2)


def point_closed_form():
    """The paper's closed form of the point proposition: (106/45)^(3/4) - X^(75/199) - sqrt3 sqrt(2 - sqrt2)/2."""
    big_x = (power(rational("9/5"), rational("199/100")) + power(rational("5/9"), rational("199/100"))) / 2
    sqrt2 = iv.sqrt(iv.mpf(2))
    return power(rational("106/45"), rational("3/4")) - power(big_x, rational("75/199")) - iv.sqrt(iv.mpf(3)) * iv.sqrt(2 - sqrt2) / 2


def check_point():
    value = point_enclosure("398/100")
    closed = point_closed_form()
    ok_window = inside(value, iv.mpf(POINT_CENTER), iv.mpf(POINT_RADIUS))
    ok_closed = bool((value - closed).a > -iv.mpf("1e-40")) and bool((value - closed).b < iv.mpf("1e-40"))
    print(f"POINT p = 3/2, s = 398/100, y = log(9/5), t = pi/2: Gamma - e in {fmt(value)} (width {mpmath.nstr(mpmath.mpf(value.b) - mpmath.mpf(value.a), 3)})")
    print(f"POINT inside {POINT_CENTER} + [-{POINT_RADIUS}, {POINT_RADIUS}]: {'PROVED' if ok_window else 'NOT PROVED'}; "
          f"equals the paper's closed form within 1e-40: {'YES' if ok_closed else 'NO'}")
    return ok_window and ok_closed


def check_one_s_plus(row):
    p_text, s_text, y_text, t_text, _ = row
    p_val, s_val = rational(p_text), rational(s_text)
    value = gamma_minus_e(p_val, s_val, rational(y_text), rational(t_text))
    below_cutoff = bool(s_val.b < (1 / iv.cos(iv.pi / (2 * p_val)) ** 2).a)
    ok = certified_negative(value) and below_cutoff
    print(f"SPLUS p = {p_text}, s+ = {s_text}, (y*, t*) = ({y_text}, {t_text}): Gamma - e in {fmt(value)}; "
          f"s+ < sec^2(pi/2p): {below_cutoff}; {'PROVED' if ok else 'NOT PROVED'}")
    return ok, value


def check_s_plus_margins(values):
    weakest = max(values, key=lambda val: mpmath.mpf(val.b))
    strongest = min(values, key=lambda val: mpmath.mpf(val.b))
    ok_weak = bool(weakest.b <= iv.mpf(PAPER_WEAKEST_MARGIN))
    ok_strong = bool(strongest.b <= iv.mpf(PAPER_STRONGEST_MARGIN))
    print(f"SPLUS paper's range: every upper end <= {PAPER_WEAKEST_MARGIN}: {ok_weak}; "
          f"most negative upper end <= {PAPER_STRONGEST_MARGIN}: {ok_strong}")
    return ok_weak and ok_strong


def main_run():
    results = [check_point()]
    s_plus = [check_one_s_plus(row) for row in S_PLUS_POINTS]
    results += [ok for ok, _ in s_plus]
    results.append(check_s_plus_margins([value for _, value in s_plus]))
    verdict = all(results)
    print(f"RESULT {'ALL PROVED' if verdict else 'NOT ALL PROVED'}: point enclosure + {len(S_PLUS_POINTS)} s+ points")
    return 0 if verdict else 1


def control_s_minus_fails():
    """At s_- Gamma >= e HOLDS (the bracket proposition), so the same failure points must NOT certify Gamma - e < 0."""
    fails = []
    for p_text, _, y_text, t_text, s_minus in S_PLUS_POINTS:
        value = gamma_minus_e(rational(p_text), rational(s_minus), rational(y_text), rational(t_text))
        fails.append(not certified_negative(value))
        print(f"CONTROL s- p = {p_text}, s = {s_minus}: Gamma - e in {fmt(value)}: "
              f"{'fails as it must' if fails[-1] else 'WRONGLY PROVED'}")
    return all(fails)


def control_true_point_fails():
    """At (p, s) = (3/2, 5/2), inside the proved range s <= p/(p-1) = 3, Gamma >= e holds: no point may certify."""
    value = gamma_minus_e(rational("3/2"), rational("5/2"), iv.log(rational("9/5")), iv.pi / 2)
    ok = not certified_negative(value)
    print(f"CONTROL (3/2, 5/2) at the same point: Gamma - e in {fmt(value)}: {'fails as it must' if ok else 'WRONGLY PROVED'}")
    return ok


def control_shifted_window_fails():
    """The point enclosure must NOT fit a window shifted by 1e-17."""
    value = point_enclosure("398/100")
    ok = not inside(value, iv.mpf("-4.17314647396548e-4"), iv.mpf(POINT_RADIUS))
    print(f"CONTROL point window shifted by 1e-17: {'fails as it must' if ok else 'WRONGLY PROVED'}")
    return ok


def control_jaguzovic_point():
    """Positive control: Jaguzovic's point (log 2, pi/2) at (3/2, 4) gives -1.3102e-3 (stated in the paper)."""
    value = gamma_minus_e(rational("3/2"), rational("4"), iv.log(iv.mpf(2)), iv.pi / 2)
    ok = certified_negative(value) and inside(value, iv.mpf("-1.3102e-3"), iv.mpf("5e-8"))
    print(f"CONTROL Jaguzovic point (3/2, 4): Gamma - e in {fmt(value)}: {'matches -1.3102e-3' if ok else 'MISMATCH'}")
    return ok


def main_test():
    results = [control_s_minus_fails(), control_true_point_fails(), control_shifted_window_fails(), control_jaguzovic_point()]
    verdict = all(results)
    print(f"TESTS {'PASS' if verdict else 'FAIL'}")
    return 0 if verdict else 1


def print_header(argv):
    digest = hashlib.md5(Path(__file__).read_bytes()).hexdigest()
    print(f"RUN {datetime.now().strftime('%Y%m%d_%H:%M:%S')} | {Path(__file__).name} md5 {digest} | python {sys.version.split()[0]} "
          f"| mpmath {mpmath.__version__} | iv.dps {DIGITS} | argv {' '.join(argv)}")


def main():
    parser = argparse.ArgumentParser(description="independent interval check of the point proposition and the six s+ points")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--test", action="store_true", help="negative and positive controls only")
    mode.add_argument("--run", action="store_true", help="the certificates (the point proposition and the six s+ points)")
    args = parser.parse_args()
    iv.dps = DIGITS
    mpmath.mp.dps = DIGITS
    print_header(sys.argv[1:])
    sys.exit(main_test() if args.test else main_run())


if __name__ == "__main__":
    main()
