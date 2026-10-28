#!/usr/bin/env python3
# check_pair.py - Lemma 8.6 of the paper on one pair file of pairs/: the facts (D), (C'), (R), (S), and the value J, all EXACT.
#  (D)  |b|, |a_j| < 1, pairwise distinct, Q(b) = Q(a_j) = 0; also Q' = dQ/dz and H prod (z - a_j) = Q prod (1 - conj(a_j) z).
#  (C') Q' = Z R: Z collects the zeros of Q' on the circle named by the file (none for a Blaschke model), each divided out to its
#       exact order; R has no zero in the closed disk by Lemma 7.11 (Schur-Cohn, T-steps, every delta_j > 0).
#  (S)  H' has no zero in the closed disk (Lemma 7.11).
#  (R)  Res_w(P_c, P_c*) at formal degree n - 1, P_c(w) = sum_k h_k U_(k-1)(c) w^(k-1) from H - H(0): computed EXACTLY (H scaled
#       to Gaussian integers by a positive integer L, which multiplies the resultant by L^(2(n-1)) > 0): determinants modulo
#       primes p = 1 (mod 4) at the integer nodes c = 0, 1, .., 2(n-1)^2 + 2 for both square roots of -1, Chinese remaindering
#       with a Hadamard bound (so the values are exact), interpolation (degree <= 2(n-1)^2; the last 2 nodes are held back and
#       checked); imaginary part 0 checked. Then NO ZERO IN [-1, 1]: R(-1), R(1) != 0 and Descartes' rule of signs with
#       bisection on (1 + t)^N R((a + b t)/(1 + t)) (exact integers).
#  (J)  J = prod_j J(a_j, b), J(a, b) = 1 + (1 - |a|^2)(1 - |b|^2)/|a - b|^2, equals the file's J; B <= sqrt(J) < B + 10^-7 for
#       the table value B given on the command line (Table 2: sqrt(J) truncated to seven decimals).
#  Needs python-flint 0.9.0 (nmod_mat, fmpz_poly, fmpq_poly). One thread. Floats are used only to print values.
# Ancillary file of the paper "Smale's mean value constant exceeds 1.1559" by Dave Goel (2026), Lemma 8.6, Theorems 8.8 and 8.9.
# Version 0.20 (0.10 + --expect for the must-fail controls: the run is right only if EXACTLY the named facts fail, each for its
#  own reason - (R) only by a PROVED zero in [-1, 1] - and any error is "CONTROL WRONG"; the zero search reports its reason).
"""Usage: check_pair.py --test | check_pair.py PAIR_FILE --bound B [--expect FACTS]
   (e.g. pairs/pair_I_K2N18.json --bound 1.1559837; FACTS = a comma list of D, C', S, J, R: the facts that must FAIL)"""
import json
import re
import sys
import time
from dataclasses import dataclass
from fractions import Fraction
from math import lcm

from flint import fmpq, fmpq_poly, fmpz, fmpz_poly, nmod_mat

GAUSS = re.compile(r"^(-?\d+(?:/\d+)?)(?: ([+-]) (\d+)\*I/(\d+))?$")
PRIME_TOP = 1 << 62
HELD_BACK = 2                                   # extra interpolation nodes, checked against the interpolant
MAX_DEPTH = 80                                  # bisection depth of the Descartes search; beyond it: FAIL (undecided)
TRUNCATION = Fraction(1, 10 ** 7)
FACTS = {"D", "C'", "S", "J", "R"}               # the facts of Lemma 8.6 that --expect may name


@dataclass(frozen=True)
class Gauss:
    """An exact Gaussian rational re + i im."""
    re: Fraction
    im: Fraction

    def __add__(self, other):
        return Gauss(self.re + other.re, self.im + other.im)

    def __sub__(self, other):
        return Gauss(self.re - other.re, self.im - other.im)

    def __mul__(self, other):
        return Gauss(self.re * other.re - self.im * other.im, self.re * other.im + self.im * other.re)

    def scale(self, factor):
        return Gauss(self.re * factor, self.im * factor)

    def conj(self):
        return Gauss(self.re, -self.im)

    def norm(self):
        return self.re * self.re + self.im * self.im

    def is_zero(self):
        return self.re == 0 and self.im == 0


ZERO, ONE = Gauss(Fraction(0), Fraction(0)), Gauss(Fraction(1), Fraction(0))


def parse_gauss(text):
    """'p/q', 'p', 'p/q + r*I/s' or 'p/q - r*I/s' (the only forms in the pair files); anything else is an error."""
    match = GAUSS.match(str(text).strip())
    if match is None:
        raise ValueError(f"not an exact Gaussian rational in the pair-file format: {text!r}")
    real, sign, num, den = match.groups()
    imag = Fraction(0) if sign is None else Fraction(int(num), int(den)) * (1 if sign == "+" else -1)
    return Gauss(Fraction(real), imag)


# ---------------------------------------------------------------- polynomials over Q(i), ascending coefficient lists
def trim(coeffs):
    out = list(coeffs)
    while len(out) > 1 and out[-1].is_zero():
        out.pop()
    return out


def pmul(aa, bb):
    out = [ZERO] * (len(aa) + len(bb) - 1)
    for ia, ca in enumerate(aa):
        for ib, cb in enumerate(bb):
            out[ia + ib] = out[ia + ib] + ca * cb
    return trim(out)


def pderiv(aa):
    return trim([cc.scale(kk) for kk, cc in enumerate(aa)][1:] or [ZERO])


def peval(aa, point):
    acc = ZERO
    for cc in reversed(aa):
        acc = acc * point + cc
    return acc


def divide_linear(coeffs, root):
    """(quotient, remainder) of the division by (z - root)."""
    quotient, carry = [], ZERO
    for cc in reversed(coeffs):
        carry = carry * root + cc
        quotient.append(carry)
    remainder = quotient.pop()
    return quotient[::-1], remainder


# ---------------------------------------------------------------- Lemma 7.11 (Schur-Cohn)
def schur_cohn_closed_disk(coeffs):
    """(ok, steps): p_j = T p_(j-1) = conj(a_0) p - a_n p* at formal degree n - j, each p_j divided by its constant term
    delta_j > 0 (a positive factor changes no later sign). ok iff every delta_j > 0, i.e. no zero in the closed disk."""
    poly = trim(coeffs)
    if poly == [ZERO]:
        return False, 0
    nsteps = len(poly) - 1
    for step in range(1, nsteps + 1):
        formal = len(poly) - 1
        a_0, a_n = poly[0], poly[formal]
        delta = a_0.norm() - a_n.norm()
        if delta <= 0:
            return False, step
        star = [cc.conj() for cc in reversed(poly)]
        poly = [(a_0.conj() * poly[k] - a_n * star[k]).scale(1 / delta) for k in range(formal)]
    return True, nsteps


# ---------------------------------------------------------------- reading a pair file
def load_pair(path):
    data = json.loads(open(path, encoding="utf-8").read())
    zeros = [parse_gauss(data[key]) for key in ("a", "a1", "a2") if key in data]
    pair = {"Q": [parse_gauss(x) for x in data["Q_ascending"]], "dQ": [parse_gauss(x) for x in data["Qprime_ascending"]],
            "H": [parse_gauss(x) for x in data["H_ascending"]], "b": parse_gauss(data["b"]), "a": zeros,
            "J": Fraction(data["J"]), "points": circle_points(data), "orders": data.get("m"), "t": data.get("t")}
    if not zeros:
        raise ValueError(f"{path}: no zero a / a1, a2")
    return pair


def circle_points(data):
    """The zeros of Q' on the circle named by the file: its 'zeta' (one value or a list); none given but R_ascending given:
    the point 1 (the README's convention); neither: none (a Blaschke model, Z constant)."""
    if "zeta" in data:
        raw = data["zeta"] if isinstance(data["zeta"], list) else [data["zeta"]]
        return [parse_gauss(x) for x in raw]
    return [ONE] if "R_ascending" in data else []


# ---------------------------------------------------------------- (D), (C'), (S), (J)
def check_d(pair):
    pts = [pair["b"]] + pair["a"]
    inside = all(pt.norm() < 1 for pt in pts)
    distinct = len(set(pts)) == len(pts)
    vanish = all(peval(pair["Q"], pt).is_zero() for pt in pts)
    deriv = pderiv(pair["Q"]) == trim(pair["dQ"])
    num, den = list(pair["H"]), list(pair["Q"])
    for aa in pair["a"]:
        num, den = pmul(num, [ZERO - aa, ONE]), pmul(den, [ONE, ZERO - aa.conj()])
    h_ok = trim(num) == trim(den)
    return inside and distinct and vanish and deriv and h_ok, (inside, distinct, vanish, deriv, h_ok)


def strip_circle_zeros(pair):
    """(R, orders, points_ok): divide Q' by (z - zeta) as long as exact, for each named point; points exactly on the circle."""
    rr, orders = trim(pair["dQ"]), []
    for zeta in pair["points"]:
        order, rem = 0, ZERO
        while True:
            quot, rem = divide_linear(rr, zeta)
            if not rem.is_zero():
                break
            rr, order = trim(quot), order + 1
        orders.append(order)
    on_circle = all(pt.norm() == 1 for pt in pair["points"]) and len(set(pair["points"])) == len(pair["points"])
    return rr, orders, on_circle and all(order >= 1 for order in orders) and t_matches(pair)


def t_matches(pair):
    """Pair X: the second point is zeta_2 = (1 - t^2 + 2 t i)/(1 + t^2) exactly (the README)."""
    if pair["t"] is None:
        return True
    tt = Fraction(pair["t"])
    zeta2 = Gauss((1 - tt * tt) / (1 + tt * tt), 2 * tt / (1 + tt * tt))
    return zeta2 in pair["points"]


def check_c(pair):
    rr, orders, points_ok = strip_circle_zeros(pair)
    expected = pair["orders"]
    if expected is not None:
        expected = expected if isinstance(expected, list) else [expected]
        points_ok = points_ok and [int(x) for x in expected] == orders
    sc_ok, steps = schur_cohn_closed_disk(rr)
    return points_ok and sc_ok, (orders, points_ok, sc_ok, steps, len(rr) - 1)


def check_s(pair):
    return schur_cohn_closed_disk(pderiv(pair["H"]))


def j_value(pair):
    jj = Fraction(1)
    for aa in pair["a"]:
        jj *= 1 + (1 - aa.norm()) * (1 - pair["b"].norm()) / (aa - pair["b"]).norm()
    return jj


def check_j(pair, bound):
    jj = j_value(pair)
    return jj == pair["J"] and bound * bound <= jj < (bound + TRUNCATION) ** 2, jj


# ---------------------------------------------------------------- (R): the exact resultant
def scaled_h(pair):
    """Gaussian-integer coefficients (x_k, y_k) of L (H - H(0)), k = 1..n, with L = lcm of all denominators (L > 0)."""
    coeffs = pair["H"][1:]
    big_l = lcm(*[cc.re.denominator for cc in coeffs], *[cc.im.denominator for cc in coeffs])
    return [(int(cc.re * big_l), int(cc.im * big_l)) for cc in coeffs], big_l


def chebyshev_u(cc, mdeg, modulus=None):
    """U_0(c), .., U_mdeg(c) (exact integers, or modulo `modulus`)."""
    vals = [1, 2 * cc]
    for _ in range(mdeg - 1):
        vals.append(2 * cc * vals[-1] - vals[-2])
    vals = vals[:mdeg + 1]
    return [vv % modulus for vv in vals] if modulus else vals


def hadamard_bits(hint, mdeg, nodes):
    """Bits of a bound for |Re| and |Im| of the determinant at every node: every row of the Sylvester matrix holds all the
    A_j = h_(j+1) U_j(c) (or their conjugates) once, so |det| <= S^(m) with S = sum_j |h_(j+1)|^2 U_j(c)^2 (Hadamard)."""
    worst = 0
    for cc in nodes:
        uu = chebyshev_u(cc, mdeg)
        worst = max(worst, sum((xx * xx + yy * yy) * u_j * u_j for (xx, yy), u_j in zip(hint, uu)))
    return mdeg * worst.bit_length() + 2


def primes_1_mod_4(bits):
    """Primes p = 1 (mod 4) below 2^62, as many as needed for a product > 2^bits, each with a square root r of -1."""
    out, product, cand = [], 1, PRIME_TOP - 3
    while product.bit_length() <= bits:
        while not fmpz(cand).is_prime():
            cand -= 4
        out.append((cand, sqrt_minus_one(cand)))
        product *= cand
        cand -= 4
    return out


def sqrt_minus_one(prime):
    for base in range(2, 200):
        root = pow(base, (prime - 1) // 4, prime)
        if root * root % prime == prime - 1:
            return root
    raise ArithmeticError(f"no square root of -1 found modulo {prime}")


def sylvester_det_mod(hmod, hbar, mdeg, cc, prime):
    """det of the formal Sylvester matrix of P_c and P_c* at c = cc, modulo prime, for one embedding of i (hmod, hbar)."""
    uu = chebyshev_u(cc, mdeg, prime)
    pcoef = [hmod[j] * uu[j] % prime for j in range(mdeg + 1)]
    scoef = [hbar[mdeg - j] * uu[mdeg - j] % prime for j in range(mdeg + 1)]
    rows = []
    for coeffs in (pcoef, scoef):
        desc = coeffs[::-1]
        rows.extend([0] * shift + desc + [0] * (mdeg - 1 - shift) for shift in range(mdeg))
    return int(nmod_mat(rows, prime).det())


def resultant_values(hint, mdeg, nodes, primes):
    """Exact (Re, Im) of the determinant at each node, by CRT over the primes (both embeddings i -> r, i -> -r)."""
    re_acc, im_acc, modulus = [0] * len(nodes), [0] * len(nodes), 1
    for count, (prime, root) in enumerate(primes):
        dets = []                                                 # dets[e][node] for the embeddings i -> root, i -> -root
        for emb in (root, prime - root):
            hmod = [(xx + yy * emb) % prime for xx, yy in hint]
            hbar = [(xx - yy * emb) % prime for xx, yy in hint]
            dets.append([sylvester_det_mod(hmod, hbar, mdeg, cc, prime) for cc in nodes])
        inv2, inv2r, inv_mod = pow(2, -1, prime), pow(2 * root, -1, prime), pow(modulus, -1, prime)
        for idx in range(len(nodes)):
            v_1, v_2 = dets[0][idx], dets[1][idx]                 # Re D + r Im D and Re D - r Im D (mod prime)
            re_acc[idx] = crt_step(re_acc[idx], modulus, inv_mod, (v_1 + v_2) * inv2 % prime, prime)
            im_acc[idx] = crt_step(im_acc[idx], modulus, inv_mod, (v_1 - v_2) * inv2r % prime, prime)
        modulus *= prime
        if (count + 1) % 200 == 0:
            print(f"   ... {count + 1} of {len(primes)} primes", flush=True)
    return [symmetric(vv, modulus) for vv in re_acc], [symmetric(vv, modulus) for vv in im_acc]


def crt_step(acc, modulus, inv_mod, residue, prime):
    """The x = acc (mod modulus), x = residue (mod prime) with 0 <= x < modulus * prime (inv_mod = modulus^-1 mod prime)."""
    return acc + modulus * ((residue - acc) * inv_mod % prime)


def symmetric(value, modulus):
    return value - modulus if 2 * value > modulus else value


def interpolate(values):
    """The polynomial of degree <= N through (c, values[c]), c = 0..N, exactly: Newton forward differences, binomial basis."""
    diffs, top = list(values), len(values) - 1
    leading = []
    for _ in range(top + 1):
        leading.append(diffs[0])
        diffs = [diffs[k + 1] - diffs[k] for k in range(len(diffs) - 1)]
    total, falling, fact_n = fmpz_poly([0]), fmpz_poly([1]), fmpz(1)
    for kk in range(1, top + 1):
        fact_n *= kk
    ratio = fact_n                                                   # N!/k! for k = 0
    for kk, d_k in enumerate(leading):
        total += falling * (fmpz(d_k) * ratio)
        falling *= fmpz_poly([-kk, 1])
        if kk < top:
            ratio = ratio // (kk + 1)
    coeffs = total.coeffs()
    if any(cc % fact_n != 0 for cc in coeffs):
        raise ArithmeticError("interpolation: not an integer polynomial")
    return fmpz_poly([cc // fact_n for cc in coeffs])


# ---------------------------------------------------------------- (R): no zero in [-1, 1]
def sign_variations(poly):
    signs = [1 if cc > 0 else -1 for cc in poly.coeffs() if cc != 0]
    return sum(1 for s1, s2 in zip(signs, signs[1:]) if s1 != s2)


def descartes_count(rpoly, left, right):
    """Sign variations of (1 + t)^N R((left + right t)/(1 + t)): 0 => no root in (left, right); 1 => exactly one."""
    shifted = fmpq_poly(rpoly.coeffs())(fmpq_poly([right, left - right]))      # R(right + (left - right) s)
    numer = shifted.numer()
    deg = rpoly.degree()
    rev = fmpz_poly(list(reversed(numer.coeffs() + [0] * (deg + 1 - len(numer.coeffs())))))
    return sign_variations(rev(fmpz_poly([1, 1])))


ZERO_PROVED = ("a zero at -1 or 1", "a zero in (-1, 1) (one sign variation)", "a zero at a bisection point")


def no_root_in_interval(rpoly):
    """(ok, tests, reason): R(-1) != 0, R(1) != 0 and no root in (-1, 1), by bisection with Descartes' rule (exact).
    reason: "no zero", one of ZERO_PROVED, "R = 0", or "undecided (depth limit)"."""
    if rpoly.degree() < 0:
        return False, 0, "R = 0"
    if rpoly(-1) == 0 or rpoly(1) == 0:
        return False, 0, ZERO_PROVED[0]
    stack, tests = [(fmpq(-1), fmpq(1), 0)], 0
    while stack:
        left, right, depth = stack.pop()
        variations = descartes_count(rpoly, left, right)
        tests += 1
        if variations == 0:
            continue
        mid = (left + right) / 2
        if variations == 1:
            return False, tests, ZERO_PROVED[1]
        if fmpq_poly(rpoly.coeffs())(mid) == 0:
            return False, tests, ZERO_PROVED[2]
        if depth >= MAX_DEPTH:
            return False, tests, "undecided (depth limit)"
        stack.extend([(left, mid, depth + 1), (mid, right, depth + 1)])
    return True, tests, "no zero"


def check_r(pair):
    """(ok, info) for fact (R)."""
    hint, big_l = scaled_h(pair)
    mdeg = len(pair["Q"]) - 2                                     # formal degree n - 1 of P_c
    if len(hint) != mdeg + 1:
        raise ValueError("H and Q have different degrees")
    bound = 2 * mdeg * mdeg
    nodes = list(range(bound + 1 + HELD_BACK))
    primes = primes_1_mod_4(hadamard_bits(hint, mdeg, nodes))
    start = time.time()
    re_vals, im_vals = resultant_values(hint, mdeg, nodes, primes)
    rpoly = interpolate(re_vals[:bound + 1])
    held_ok = all(rpoly(cc) == re_vals[cc] for cc in nodes[bound + 1:])
    real_ok = all(vv == 0 for vv in im_vals)
    root_ok, tests, reason = no_root_in_interval(rpoly)
    info = {"formal degree": mdeg, "degree bound 2(n-1)^2": bound, "degree": rpoly.degree(), "primes": len(primes),
            "held-back nodes fit": held_ok, "imaginary part 0": real_ok, "Descartes tests": tests,
            "no zero in [-1, 1]": root_ok, "zero search": reason, "seconds": round(time.time() - start, 1)}
    return held_ok and real_ok and root_ok and rpoly.degree() <= bound, info


# ---------------------------------------------------------------- report
def fmt_gauss(val):
    if val.im == 0:
        return str(val.re)
    return f"({val.re} {'+' if val.im > 0 else '-'} {abs(val.im)} i)"


def main_check(path, bound_text):
    pair, bound = load_pair(path), Fraction(bound_text)
    d_ok, d_info = check_d(pair)
    print(f"(D)  |b|, |a_j| < 1; distinct; Q(b) = Q(a_j) = 0; Q' = dQ/dz; H matches Q: {d_info} -> {'PASS' if d_ok else 'FAIL'}", flush=True)
    c_ok, (orders, points_ok, sc_ok, steps, deg_r) = check_c(pair)
    zdesc = " ".join(f"(z - {fmt_gauss(pt)})^{od}" for pt, od in zip(pair["points"], orders)) or "a constant"
    print(f"(C') Z = {zdesc}; points on the circle, orders as in the file: {points_ok}; R (degree {deg_r}) has no zero in the "
          f"closed disk (Schur-Cohn, {steps} steps): {sc_ok} -> {'PASS' if c_ok else 'FAIL'}", flush=True)
    s_ok, s_steps = check_s(pair)
    print(f"(S)  H' has no zero in the closed disk (Schur-Cohn, {s_steps} steps): {'PASS' if s_ok else 'FAIL'}", flush=True)
    j_ok, jj = check_j(pair, bound)
    print(f"(J)  J = {jj} = the file's J; {bound_text} <= sqrt(J) < {bound_text} + 1e-7: {'PASS' if j_ok else 'FAIL'} "
          f"(sqrt(J) ~ {float(jj) ** 0.5:.10f})", flush=True)
    r_ok, r_info = check_r(pair)
    print(f"(R)  Res_w(P_c, P_c*) exact: {r_info} -> {'PASS' if r_ok else 'FAIL'}", flush=True)
    verdict = d_ok and c_ok and s_ok and j_ok and r_ok
    print(f"LEMMA 8.6 for {path} with k = {len(pair['a'])}, n = {len(pair['Q']) - 1}: {'PASS' if verdict else 'FAIL'}")
    return verdict, failed_facts({"D": d_ok, "C'": c_ok, "S": s_ok, "J": j_ok, "R": r_ok}, r_info)


def failed_facts(oks, r_info):
    """The set of failed facts; an (R) failure counts as "R" only if it is a PROVED zero in [-1, 1] of an exact, consistent
    resultant (held-back nodes fit, imaginary part 0, degree <= 2(n-1)^2) - otherwise it is "R (other)"."""
    failed = {name for name, ok in oks.items() if not ok}
    r_own = (r_info["held-back nodes fit"] and r_info["imaginary part 0"] and r_info["zero search"] in ZERO_PROVED
             and r_info["degree"] <= r_info["degree bound 2(n-1)^2"])
    return failed if "R" not in failed or r_own else (failed - {"R"}) | {"R (other)"}


def main_expect(path, bound_text, expected):
    """A must-fail control: True iff the facts that fail are EXACTLY `expected`; an error of any kind is CONTROL WRONG."""
    try:
        _, failed = main_check(path, bound_text)
    except Exception as err:                                      # noqa: BLE001 - every error must be reported, not passed
        print(f"CONTROL WRONG: {type(err).__name__}: {err}")
        return False
    names = lambda facts: ", ".join(sorted(facts)) or "none"     # noqa: E731
    if failed == expected:
        print(f"CONTROL: exactly ({names(expected)}) fail, as required")
        return True
    print(f"CONTROL WRONG: ({names(failed)}) fail; required: exactly ({names(expected)})")
    return False


def run_tests():
    gg = lambda re_part, im_part=0: Gauss(Fraction(re_part), Fraction(im_part))     # noqa: E731
    assert parse_gauss("-3/4 + 5*I/2") == gg(Fraction(-3, 4), Fraction(5, 2)) and parse_gauss("7") == gg(7)
    assert schur_cohn_closed_disk([gg(-2), gg(1)])[0] and not schur_cohn_closed_disk([gg(Fraction(-1, 2)), gg(1)])[0]
    assert not schur_cohn_closed_disk([gg(-1), gg(1)])[0] and not schur_cohn_closed_disk([gg(0, -1), gg(1)])[0]   # zeros 1, i
    assert divide_linear([gg(-1), gg(0), gg(1)], gg(1)) == ([gg(1), gg(1)], ZERO)                                  # z^2 - 1
    assert interpolate([cc * cc - 3 * cc + 5 for cc in range(5)]) == fmpz_poly([5, -3, 1])
    quad_in, quad_none, quad_out = fmpz_poly([-1, 0, 4]), fmpz_poly([1, 0, 1]), fmpz_poly([-4, 0, 1])
    assert not no_root_in_interval(quad_in)[0] and no_root_in_interval(quad_none)[0] and no_root_in_interval(quad_out)[0]
    assert not no_root_in_interval(fmpz_poly([-1, 0, 0, 1]))[0]                                                   # root at 1
    assert no_root_in_interval(quad_in)[2] == ZERO_PROVED[1] and no_root_in_interval(fmpz_poly([-1, 0, 0, 1]))[2] == ZERO_PROVED[0]
    consistent = {"held-back nodes fit": True, "imaginary part 0": True, "degree": 2, "degree bound 2(n-1)^2": 2}
    oks = {"D": True, "C'": True, "S": True, "J": True, "R": False}
    assert failed_facts(oks, {**consistent, "zero search": ZERO_PROVED[1]}) == {"R"}                             # own reason
    assert failed_facts(oks, {**consistent, "zero search": "undecided (depth limit)"}) == {"R (other)"}         # not a proof
    assert not main_expect("no_such_pair_file.json", "1.0", {"R"})                                               # error: WRONG
    good = {"Q": [ZERO, ONE, gg(Fraction(1, 8))], "H": [ZERO, ONE, gg(Fraction(1, 4))]}       # H = z + z^2/4: P_c = 1 + c w/2
    bad = {"Q": [ZERO, ONE, gg(Fraction(3, 8))], "H": [ZERO, ONE, gg(Fraction(3, 4))]}        # P_c = 1 + 3c w/2: zero at |w| < 1
    assert check_r(good)[0] and not check_r(bad)[0]
    hint, _ = scaled_h({"H": [ZERO, ONE, gg(Fraction(3, 4), Fraction(1, 2)), gg(Fraction(-1, 3))]})
    for cc in range(4):                                                                       # modular det = exact det
        exact = exact_sylvester_det(hint, 2, cc)
        primes = primes_1_mod_4(hadamard_bits(hint, 2, [cc]))
        assert resultant_values(hint, 2, [cc], primes) == ([exact[0]], [exact[1]]), cc
    print("tests 13/13 OK")                                                    # 13 assert statements (v0.10 said 10 for its 9)


def exact_sylvester_det(hint, mdeg, cc):
    """Test oracle: the same Sylvester determinant over Q(i) by Fraction Gaussian elimination (small sizes only)."""
    uu = chebyshev_u(cc, mdeg)
    pcoef = [Gauss(Fraction(xx * u_j), Fraction(yy * u_j)) for (xx, yy), u_j in zip(hint, uu)]
    scoef = [pcoef[mdeg - j].conj() for j in range(mdeg + 1)]
    rows = []
    for coeffs in (pcoef, scoef):
        rows.extend([ZERO] * shift + coeffs[::-1] + [ZERO] * (mdeg - 1 - shift) for shift in range(mdeg))
    det = ONE
    for col in range(2 * mdeg):
        piv = next((r for r in range(col, 2 * mdeg) if not rows[r][col].is_zero()), None)
        if piv is None:
            return 0, 0
        if piv != col:
            rows[col], rows[piv], det = rows[piv], rows[col], ZERO - det
        inv = Gauss(rows[col][col].re / rows[col][col].norm(), -rows[col][col].im / rows[col][col].norm())
        det = det * rows[col][col]
        for r in range(col + 1, 2 * mdeg):
            factor = rows[r][col] * inv
            rows[r] = [rows[r][k] - factor * rows[col][k] for k in range(2 * mdeg)]
    return int(det.re), int(det.im)


def main():
    args = sys.argv[1:]
    if args == ["--test"]:
        run_tests()
        return
    if len(args) == 5 and args[1] == "--bound" and args[3] == "--expect":
        expected = set(args[4].split(","))
        if not expected <= FACTS:
            sys.exit(f"--expect: unknown fact in {args[4]!r}; the facts are {', '.join(sorted(FACTS))}")
        sys.exit(0 if main_expect(args[0], args[2], expected) else 1)
    if len(args) != 3 or args[1] != "--bound":
        sys.exit(__doc__)
    sys.exit(0 if main_check(args[0], args[2])[0] else 1)


if __name__ == "__main__":
    main()
