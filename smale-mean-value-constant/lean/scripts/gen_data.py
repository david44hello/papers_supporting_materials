#!/usr/bin/env python3
"""gen_data.py — write Smale/Defs/Data.lean (the explicit data of paper 009, Section 5) from the paper and the data file.

The printed numbers b, a1, a2, rho_1..rho_10 are parsed from the frozen tex (never retyped). Q (19 coefficients) comes from
the data file pair_I_K2N18.json. g0, g1 are computed exactly as G = Q' / (18 (z-1)^5 prod_j (z - rho_j)), and the script
fails loudly unless the division is exact and G is monic of degree 2. It also checks that the file's Q' is the derivative
of its Q and that the file's J equals the paper's Lambda.
Usage: gen_data.py <tex> <pair json> <out .lean>
"""
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

GAUSS_JSON = re.compile(r"^(-?\d+(?:/\d+)?)(?: ([+-]) (\d+)\*I/(\d+))?$")
TEX_FRAC = r"(-?)\\tfrac\{(\d+)\}\{(\d+)\}"
TEX_GAUSS = re.compile(TEX_FRAC + r"\s*([+-])\s*\\tfrac\{(\d+)\}\{(\d+)\}\s*\\,i")


def parse_json_gauss(text):
    match = GAUSS_JSON.match(text.strip())
    if not match:
        sys.exit(f"FAIL: cannot parse Gaussian rational {text[:60]!r}")
    re_part = Fraction(match.group(1))
    if match.group(2) is None:
        return (re_part, Fraction(0))
    im_part = Fraction(int(match.group(3)), int(match.group(4)))
    return (re_part, -im_part if match.group(2) == "-" else im_part)


def parse_tex_gauss(match):
    sign_re, num_re, den_re, sign_im, num_im, den_im = match.groups()
    re_part = Fraction(int(num_re), int(den_re)) * (-1 if sign_re else 1)
    im_part = Fraction(int(num_im), int(den_im)) * (-1 if sign_im == "-" else 1)
    return (re_part, im_part)


def printed_data(tex):
    """b, a1, a2, rho_1..rho_10 from the lines `b=...` and `\\rho_j &= ...` of the proof of Theorem 1.1."""
    found = {}
    for name in ("b", "a_1", "a_2"):
        match = re.search(re.escape(name) + r"=" + TEX_GAUSS.pattern, tex)
        if not match:
            sys.exit(f"FAIL: {name} not found in the tex")
        found[name] = parse_tex_gauss(match)
    for j in range(1, 11):
        pattern = r"\\rho_\{?" + str(j) + r"\}? &= " + TEX_GAUSS.pattern
        match = re.search(pattern, tex)
        if not match:
            sys.exit(f"FAIL: rho_{j} not found in the tex")
        found[f"rho_{j}"] = parse_tex_gauss(match)
    return found


def gmul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def gsub(x, y):
    return (x[0] - y[0], x[1] - y[1])


def pmul(aa, bb):
    out = [(Fraction(0), Fraction(0))] * (len(aa) + len(bb) - 1)
    for i, x in enumerate(aa):
        for j, y in enumerate(bb):
            prod = gmul(x, y)
            out[i + j] = (out[i + j][0] + prod[0], out[i + j][1] + prod[1])
    return out


def pdivmod_monic(num, den):
    """Quotient and remainder of num / den, den monic (ascending coefficient lists)."""
    num, deg = list(num), len(den) - 1
    quot = [(Fraction(0), Fraction(0))] * (len(num) - deg)
    for k in range(len(num) - 1, deg - 1, -1):
        coef = num[k]
        quot[k - deg] = coef
        for i, d_i in enumerate(den):
            num[k - deg + i] = gsub(num[k - deg + i], gmul(coef, d_i))
    return quot, num[:deg]


def compute_g(dq, rho):
    one = (Fraction(1), Fraction(0))
    den = [(Fraction(18), Fraction(0))]
    for _ in range(5):
        den = pmul(den, [(Fraction(-1), Fraction(0)), one])
    for r in rho:
        den = pmul(den, [(-r[0], -r[1]), one])
    lead = den[-1]
    if lead != (Fraction(18), Fraction(0)):
        sys.exit("FAIL: unexpected leading coefficient")
    den_monic = [(c[0] / 18, c[1] / 18) for c in den]
    quot, rem = pdivmod_monic(dq, den_monic)
    quot = [(c[0] / 18, c[1] / 18) for c in quot]
    if any(c != (0, 0) for c in rem) or len(quot) != 3 or quot[2] != one:
        sys.exit("FAIL: Q' / (18 (z-1)^5 prod (z - rho_j)) is not an exact monic quadratic")
    return quot[0], quot[1]


def lean_q(x):
    return f"({x.numerator}" + (f"/{x.denominator}" if x.denominator != 1 else "") + " : ℚ)"


def lean_gq(z):
    return f"gq {lean_q(z[0])} {lean_q(z[1])}"


def check_file(data, q):
    dq = [parse_json_gauss(x) for x in data["Qprime_ascending"]]
    if dq != [(c[0] * k, c[1] * k) for k, c in enumerate(q)][1:]:
        sys.exit("FAIL: the file's Q' is not the derivative of its Q")
    return dq


def tex_source_tag(tex_path):
    """'v1.00 (md5 1583a3b9)' from the tex's first '% version' line and its bytes; fails loudly if no version line."""
    raw = tex_path.read_bytes()
    match = re.search(rb"^% version ([0-9.]+)", raw, re.MULTILINE)
    if not match:
        sys.exit(f"FAIL: no '% version' line in {tex_path}")
    return f"v{match.group(1).decode()} (md5 {hashlib.md5(raw).hexdigest()[:8]})"


def render(printed, q, g0, g1, lam, source_tag):
    rho_lines = ",\n    ".join(lean_gq(printed[f"rho_{j}"]) for j in range(1, 11))
    q_lines = ",\n  ".join(f"({lean_q(c[0])}, {lean_q(c[1])})" for c in q)
    return f"""/-
Smale/Defs/Data.lean — the explicit data of paper 009, Section 5 (tex l.293-324). GENERATED by
scripts/gen_data.py: b, a₁, a₂, ρ₁…ρ₁₀ parsed from the frozen tex {source_tag};
Q's 19 coefficients from pair_I_K2N18.json; g₀, g₁ computed exactly as G = Q'/(18(z-1)⁵∏(z-ρ_j)).
The paper DEFINES Q by Q(z) = 18∫_b^z G L and (g₀, g₁) as the unique solution of a linear system; that `Qdata`, `g0D`,
`g1D` are these is the claim `sec5_Q_def` / `sec5_G_unique` (Statements), not an assumption.
## version 0.21 - 20261027_2145 — public header; regenerated from the posted paper v1.30 (comments only; data identical).
## version 0.11 - 20261027_1550 — regenerated from paper v1.00 (line numbers only; data identical).
## version 0.01 - 20261027_1150 — first version (generated).
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial Complex

/-- The Gaussian rational `x + y i`. -/
noncomputable def gq (x y : ℚ) : ℂ := (x : ℂ) + (y : ℂ) * I

/-- `b` (tex l.295). -/
noncomputable def bD : ℂ := {lean_gq(printed["b"])}

/-- `a₁` (tex l.295). -/
noncomputable def a1D : ℂ := {lean_gq(printed["a_1"])}

/-- `a₂` (tex l.296). -/
noncomputable def a2D : ℂ := {lean_gq(printed["a_2"])}

/-- `ρ₁, …, ρ₁₀` (tex l.298-310), `rho j = ρ_(j+1)`. -/
noncomputable def rho : Fin 10 → ℂ :=
  ![{rho_lines}]

/-- `L(t) = (t - 1)⁵ ∏_j (t - ρ_j)` (tex l.311). -/
noncomputable def Lpoly : ℂ[X] := (X - 1) ^ 5 * ∏ j : Fin 10, (X - C (rho j))

/-- `g₀` (tex l.311-317). -/
noncomputable def g0D : ℂ := {lean_gq(g0)}

/-- `g₁` (tex l.311-317). -/
noncomputable def g1D : ℂ := {lean_gq(g1)}

/-- `G(t) = t² + g₁t + g₀` (tex l.311). -/
noncomputable def Gpoly : ℂ[X] := X ^ 2 + C g1D * X + C g0D

/-- The coefficients of `Q`, ascending, as (real part, imaginary part) (data file, tex l.324). -/
def QcoeffData : List (ℚ × ℚ) := [
  {q_lines}]

/-- `Q` (tex l.318). -/
noncomputable def Qdata : ℂ[X] :=
  ∑ k ∈ Finset.range 19, C (gq (QcoeffData.getD k (0, 0)).1 (QcoeffData.getD k (0, 0)).2) * X ^ k

/-- `V(z) = 18 G(z) ∏_j (z - ρ_j)` (tex l.321). -/
noncomputable def Vdata : ℂ[X] := 18 * Gpoly * ∏ j : Fin 10, (X - C (rho j))

/-- `H(z) = Q(z)(1 - ā₁z)(1 - ā₂z)/((z - a₁)(z - a₂))` (tex l.322). -/
noncomputable def Hdata : ℂ[X] := Hpoly Qdata [a1D, a2D]

/-- `Λ` (tex l.102-103). -/
def LambdaQ : ℚ := {lam.numerator} /
  {lam.denominator}

end Smale
"""


def main_gen(tex_path: Path, pair_path: Path, out_path: Path) -> None:
    tex = tex_path.read_text()
    printed = printed_data(tex)
    data = json.loads(pair_path.read_text())
    q = [parse_json_gauss(x) for x in data["Q_ascending"]]
    if len(q) != 19 or q[-1] != (1, 0):
        sys.exit("FAIL: Q is not monic of degree 18")
    dq = check_file(data, q)
    for key, name in (("b", "b"), ("a1", "a_1"), ("a2", "a_2")):
        if parse_json_gauss(data[key].replace(" + ", " + ").strip()) != printed[name]:
            sys.exit(f"FAIL: the file's {key} differs from the printed {name}")
    g0, g1 = compute_g(dq, [printed[f"rho_{j}"] for j in range(1, 11)])
    lam_tex = re.search(r"\\Lambda=\\frac\{(\d+)\}\s*\{(\d+)\}", tex)
    lam = Fraction(int(lam_tex.group(1)), int(lam_tex.group(2)))
    if Fraction(data["J"]) != lam:
        sys.exit("FAIL: the file's J differs from the printed Lambda")
    out_path.write_text(render(printed, q, g0, g1, lam, tex_source_tag(tex_path)))
    print(f"wrote {out_path}: g0, g1 denominators {len(str(g0[0].denominator))}, {len(str(g1[0].denominator))} digits")


def main():
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main_gen(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]))


if __name__ == "__main__":
    main()
