#!/usr/bin/env python3
# rebuild_from_printed.py - do the numbers PRINTED in Section 5 of the paper give EXACTLY the data in the pair file?
# Section 5 prints b, a1, a2 and rho_1, ..., rho_10 exactly, and defines
#   L(t) = (t - 1)^5 prod_j (t - rho_j),  G(t) = t^2 + g1 t + g0 with int_b^{a_i} G(t) L(t) dt = 0 (i = 1, 2),
#   Q(z) = 18 int_b^z G(t) L(t) dt,  Q'(z) = 18 (z - 1)^5 G(z) prod_j (z - rho_j),
#   H(z) = Q(z) (1 - conj(a1) z)(1 - conj(a2) z) / ((z - a1)(z - a2)).
# This program reads those printed numbers from the paper's LaTeX source, solves the linear system for (g0, g1) exactly, rebuilds
# Q, Q' and H, and compares them (and b, a1, a2) with the pair file. Exact arithmetic over Q(i); it is independent of
# check_pair.py. Exit 0 iff everything is equal.
# Supporting file of the paper "Smale's mean value constant exceeds 1.1559" by Dave Goel (2026), Section 5.
# Version 0.10.
"""Usage: rebuild_from_printed.py PAPER_TEX PAIR_JSON | rebuild_from_printed.py --test"""
import json
import re
import sys
from fractions import Fraction

TFRAC = re.compile(r"([+-]?)\s*\\tfrac\{(\d+)\}\{(\d+)\}(\\,i)?")
NAMED = re.compile(r"(b|a_1|a_2|\\rho_\{?(\d+)\}?)\s*(?:&)?=\s*((?:[+-]?\s*\\tfrac\{\d+\}\{\d+\}(?:\\,i)?\s*){1,2})")
PAIR_FORM = re.compile(r"^(-?\d+(?:/\d+)?)(?: ([+-]) (\d+)\*I/(\d+))?$")


# ---------------------------------------------------------------- Gaussian rationals as (re, im) Fraction tuples
def gmul(xx, yy):
    return (xx[0] * yy[0] - xx[1] * yy[1], xx[0] * yy[1] + xx[1] * yy[0])


def gsub(xx, yy):
    return (xx[0] - yy[0], xx[1] - yy[1])


def gdiv(xx, yy):
    norm = yy[0] * yy[0] + yy[1] * yy[1]
    return gmul(xx, (yy[0] / norm, -yy[1] / norm))


def gconj(xx):
    return (xx[0], -xx[1])


ZERO, ONE = (Fraction(0), Fraction(0)), (Fraction(1), Fraction(0))


# ---------------------------------------------------------------- polynomials: ascending lists of Gaussian rationals
def padd(aa, bb):
    size = max(len(aa), len(bb))
    aa, bb = aa + [ZERO] * (size - len(aa)), bb + [ZERO] * (size - len(bb))
    return [(xx[0] + yy[0], xx[1] + yy[1]) for xx, yy in zip(aa, bb)]


def pmul(aa, bb):
    out = [ZERO] * (len(aa) + len(bb) - 1)
    for ia, ca in enumerate(aa):
        for ib, cb in enumerate(bb):
            prod = gmul(ca, cb)
            out[ia + ib] = (out[ia + ib][0] + prod[0], out[ia + ib][1] + prod[1])
    return out


def pscale(aa, factor):
    return [gmul(cc, factor) for cc in aa]


def pinteg(aa):
    """The antiderivative with constant term 0."""
    return [ZERO] + [(cc[0] / (kk + 1), cc[1] / (kk + 1)) for kk, cc in enumerate(aa)]


def peval(aa, point):
    acc = ZERO
    for cc in reversed(aa):
        acc = gmul(acc, point)
        acc = (acc[0] + cc[0], acc[1] + cc[1])
    return acc


def definite(aa, lower, upper):
    """int_lower^upper of the polynomial aa."""
    anti = pinteg(aa)
    return gsub(peval(anti, upper), peval(anti, lower))


def trim(aa):
    out = list(aa)
    while len(out) > 1 and out[-1] == ZERO:
        out.pop()
    return out


def divide(num, den):
    """Polynomial long division (den monic): (quotient, remainder)."""
    num, quot = list(num), [ZERO] * (len(num) - len(den) + 1)
    for kk in range(len(num) - len(den), -1, -1):
        coef = num[kk + len(den) - 1]
        quot[kk] = coef
        for jj, dd in enumerate(den):
            num[kk + jj] = gsub(num[kk + jj], gmul(coef, dd))
    return quot, num[:len(den) - 1]


# ---------------------------------------------------------------- reading the numbers
def parse_tex(path):
    """{name: value} for b, a_1, a_2, rho_1..rho_10, from the printed \\tfrac pairs (real part, then imaginary part with \\,i)."""
    text = open(path, encoding="utf-8").read()
    values = {}
    for match in NAMED.finditer(text):
        name = match.group(1) if match.group(2) is None else f"rho_{match.group(2)}"
        values[name] = parse_value(match.group(3))
    return values


def parse_value(chunk):
    real, imag = Fraction(0), Fraction(0)
    for sign, num, den, is_imag in TFRAC.findall(chunk):
        val = Fraction(int(num), int(den)) * (-1 if sign == "-" else 1)
        if is_imag:
            imag += val
        else:
            real += val
    return (real, imag)


def parse_pair_value(text):
    match = PAIR_FORM.match(text.strip())
    if match is None:
        raise ValueError(f"not a pair-file Gaussian rational: {text!r}")
    real, sign, num, den = match.groups()
    imag = Fraction(0) if sign is None else Fraction(int(num), int(den)) * (1 if sign == "+" else -1)
    return (Fraction(real), imag)


# ---------------------------------------------------------------- the rebuild
def l_poly(printed):
    poly = [ONE]
    for _ in range(5):
        poly = pmul(poly, [(Fraction(-1), Fraction(0)), ONE])
    for jj in range(1, 11):
        poly = pmul(poly, [gsub(ZERO, printed[f"rho_{jj}"]), ONE])
    return poly


def solve_g(printed, lpoly):
    """(g0, g1) from int_b^{a_i} (t^2 + g1 t + g0) L(t) dt = 0, i = 1, 2 (Cramer's rule; the determinant must not vanish)."""
    bb = printed["b"]
    rows = []
    for name in ("a_1", "a_2"):
        top = printed[name]
        c_0 = definite(lpoly, bb, top)
        c_1 = definite(pmul([ZERO, ONE], lpoly), bb, top)
        c_2 = definite(pmul([ZERO, ZERO, ONE], lpoly), bb, top)
        rows.append((c_0, c_1, gsub(ZERO, c_2)))                   # c_0 g0 + c_1 g1 = -c_2
    det = gsub(gmul(rows[0][0], rows[1][1]), gmul(rows[0][1], rows[1][0]))
    if det == ZERO:
        raise ArithmeticError("the linear system for (g0, g1) is singular: G is not unique")
    g_0 = gdiv(gsub(gmul(rows[0][2], rows[1][1]), gmul(rows[0][1], rows[1][2])), det)
    g_1 = gdiv(gsub(gmul(rows[0][0], rows[1][2]), gmul(rows[0][2], rows[1][0])), det)
    return g_0, g_1


def rebuild(printed):
    """(Q, Q', H) from the printed numbers."""
    lpoly = l_poly(printed)
    g_0, g_1 = solve_g(printed, lpoly)
    dq = pscale(pmul([g_0, g_1, ONE], lpoly), (Fraction(18), Fraction(0)))
    anti = pinteg(dq)
    qq = padd(anti, [gsub(ZERO, peval(anti, printed["b"]))])        # Q(b) = 0
    num, den = qq, [ONE]
    for name in ("a_1", "a_2"):
        num = pmul(num, [ONE, gsub(ZERO, gconj(printed[name]))])     # times (1 - conj(a) z)
        den = pmul(den, [gsub(ZERO, printed[name]), ONE])            # times (z - a)
    hh, rem = divide(num, den)
    if any(cc != ZERO for cc in rem):
        raise ArithmeticError("H is not a polynomial: (z - a1)(z - a2) does not divide Q (1 - conj(a1) z)(1 - conj(a2) z)")
    return trim(qq), trim(dq), trim(hh)


def compare(printed, pair_path, rebuilt):
    data = json.load(open(pair_path, encoding="utf-8"))
    qq, dq, hh = rebuilt
    return {
        "b": printed["b"] == parse_pair_value(data["b"]),
        "a1": printed["a_1"] == parse_pair_value(data["a1"]),
        "a2": printed["a_2"] == parse_pair_value(data["a2"]),
        "Q": qq == trim([parse_pair_value(x) for x in data["Q_ascending"]]),
        "Q'": dq == trim([parse_pair_value(x) for x in data["Qprime_ascending"]]),
        "H": hh == trim([parse_pair_value(x) for x in data["H_ascending"]]),
    }


def main_rebuild(tex_path, pair_path):
    printed = parse_tex(tex_path)
    expected = {"b", "a_1", "a_2"} | {f"rho_{jj}" for jj in range(1, 11)}
    if set(printed) != expected:
        sys.exit(f"read the numbers {sorted(printed)}; expected {sorted(expected)}")
    checks = compare(printed, pair_path, rebuild(printed))
    for name, ok in checks.items():
        print(f"printed numbers -> {name} equals the pair file's {name}: {'PASS' if ok else 'FAIL'}")
    verdict = all(checks.values())
    print(f"REBUILD from {tex_path}: {'PASS' if verdict else 'FAIL'}")
    return verdict


def run_tests():
    assert parse_value(r"-\tfrac{3}{4}+\tfrac{5}{2}\,i") == (Fraction(-3, 4), Fraction(5, 2))
    assert parse_pair_value("-3/4 + 5*I/2") == (Fraction(-3, 4), Fraction(5, 2)) and parse_pair_value("7") == (7, 0)
    assert divide([(Fraction(-1), 0), ZERO, ONE], [(Fraction(-1), 0), ONE]) == ([ONE, ONE], [ZERO])    # z^2 - 1 = (z-1)(z+1)
    assert definite([ZERO, (Fraction(2), Fraction(0))], ZERO, ONE) == ONE                             # int_0^1 2t dt = 1
    print("tests 4/4 OK")


def main():
    args = sys.argv[1:]
    if args == ["--test"]:
        run_tests()
        return
    if len(args) != 2:
        sys.exit(__doc__)
    sys.exit(0 if main_rebuild(args[0], args[1]) else 1)


if __name__ == "__main__":
    main()
