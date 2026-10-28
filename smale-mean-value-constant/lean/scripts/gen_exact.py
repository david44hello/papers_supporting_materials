#!/usr/bin/env python3
"""gen_exact.py — write Smale/Proofs/DataGQ.lean: the data of paper 009 as computable Gaussian-rational values (GQ), each
linked to Smale/Defs/Data.lean by `rfl`, plus the coefficient list of H (computed here, checked in Lean by a kernel
identity, never trusted).
Usage: gen_exact.py <tex> <pair json> <out .lean>
       gen_exact.py --test
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
import gen_data  # noqa: E402

ZERO = (Fraction(0), Fraction(0))
ONE = (Fraction(1), Fraction(0))


def gmul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def gneg(a):
    return (-a[0], -a[1])


def gconj(a):
    return (a[0], -a[1])


def padd(p, q):
    size = max(len(p), len(q))
    get = lambda r, k: r[k] if k < len(r) else ZERO  # noqa: E731
    return [(get(p, k)[0] + get(q, k)[0], get(p, k)[1] + get(q, k)[1]) for k in range(size)]


def pmul(p, q):
    out = [ZERO] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i + j] = padd([out[i + j]], [gmul(x, y)])[0]
    return out


def pdiv_monic(p, d):
    """Quotient and remainder of p by the monic d."""
    p = list(p)
    quot = [ZERO] * (len(p) - len(d) + 1)
    for k in range(len(p) - len(d), -1, -1):
        coef = p[k + len(d) - 1]
        quot[k] = coef
        for i, x in enumerate(d):
            p[k + i] = (p[k + i][0] - (coef[0] * x[0] - coef[1] * x[1]), p[k + i][1] - (coef[0] * x[1] + coef[1] * x[0]))
    return quot, p[: len(d) - 1]


def compute_h(q, a1, a2):
    """H = Q (1 - ā₁z)(1 - ā₂z) / ((z - a₁)(z - a₂)); fails loudly unless the division is exact."""
    zeros = pmul([gneg(a1), ONE], [gneg(a2), ONE])
    refl = pmul([ONE, gneg(gconj(a1))], [ONE, gneg(gconj(a2))])
    quot, rem = pdiv_monic(pmul(q, refl), zeros)
    if any(c != ZERO for c in rem):
        sys.exit("FAIL: (z - a1)(z - a2) does not divide Q(1 - conj(a1) z)(1 - conj(a2) z)")
    return quot


def lean_gq(z):
    return f"⟨{gen_data.lean_q(z[0])}, {gen_data.lean_q(z[1])}⟩"


def render(printed, h, g0, g1):
    rho_lines = ",\n  ".join(lean_gq(printed[f"rho_{j}"]) for j in range(1, 11))
    h_lines = ",\n  ".join(lean_gq(c) for c in h)
    return f"""/-
Smale/Proofs/DataGQ.lean — the data of Section 5 as computable Gaussian rationals (`GQ`), each equal by `rfl` to its
definition in Smale/Defs/Data.lean, and the coefficients of `H` (computed by
scripts/gen_exact.py; Lean checks them by a kernel identity, see Smale/Proofs/DataPoly.lean).
GENERATED — do not edit by hand.
## version 0.11 - 20261027_2145 — public header (comments only).
## version 0.01 - 20261027_1715 — first version.
-/
import Smale.Proofs.GQPoly

namespace Smale.Exact

open Polynomial Complex

def bGQ : GQ := {lean_gq(printed["b"])}
def a1GQ : GQ := {lean_gq(printed["a_1"])}
def a2GQ : GQ := {lean_gq(printed["a_2"])}

/-- `ρ₁, …, ρ₁₀`. -/
def rhoGQ : List GQ := [
  {rho_lines}]

def g0GQ : GQ := {lean_gq(g0)}
def g1GQ : GQ := {lean_gq(g1)}

/-- The coefficients of `H`, ascending (degree 18). -/
def hGQ : GP := [
  {h_lines}]

theorem bD_eq : bD = bGQ.toC := rfl
theorem a1D_eq : a1D = a1GQ.toC := rfl
theorem a2D_eq : a2D = a2GQ.toC := rfl
theorem g0D_eq : g0D = g0GQ.toC := rfl
theorem g1D_eq : g1D = g1GQ.toC := rfl

theorem rho_eq (j : Fin 10) : rho j = (rhoGQ.getD j GQ.zero).toC := by
  fin_cases j <;> rfl

end Smale.Exact
"""


def main_gen(tex_path: Path, pair_path: Path, out_path: Path) -> None:
    tex = tex_path.read_text()
    printed = gen_data.printed_data(tex)
    data = json.loads(pair_path.read_text())
    q = [gen_data.parse_json_gauss(x) for x in data["Q_ascending"]]
    dq = gen_data.check_file(data, q)
    g0, g1 = gen_data.compute_g(dq, [printed[f"rho_{j}"] for j in range(1, 11)])
    h = compute_h(q, printed["a_1"], printed["a_2"])
    if len(h) != 19 or h[-1] == ZERO:
        sys.exit("FAIL: H is not of degree 18")
    out_path.write_text(render(printed, h, g0, g1))
    print(f"wrote {out_path}: H degree {len(h) - 1}")


def run_tests():
    a = (Fraction(1, 2), Fraction(1, 3))
    q = pmul(pmul([gneg(a), ONE], [(Fraction(2), Fraction(0)), ONE]), [gneg(a), ONE])
    h = compute_h(q, a, (Fraction(-2), Fraction(0)))
    assert len(h) == 4, h
    assert pmul(h, pmul([gneg(a), ONE], [(Fraction(2), Fraction(0)), ONE])) == pmul(
        q, pmul([ONE, gneg(gconj(a))], [ONE, (Fraction(2), Fraction(0))])), "identity"
    print("tests PASS")


def main():
    if sys.argv[1:] == ["--test"]:
        run_tests()
        return
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    sys.set_int_max_str_digits(0)
    main_gen(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]))


if __name__ == "__main__":
    main()
