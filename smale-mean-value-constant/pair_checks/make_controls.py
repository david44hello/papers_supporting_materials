#!/usr/bin/env python3
# make_controls.py - MUST-FAIL controls for check_pair.py, made from the public pair files. Each control changes ONE input, and
#  the facts that depend on that input fail with it; run each with check_pair.py --expect <exactly these facts>:
#  ctl_R_pair_I_Hs.json    pair I with H(z) replaced by H(s z), s = 1250009/1250000 (s - 1 = 7.2e-6, just past the univalence
#                          margin of pair I): (R) fails by a proved zero in [-1, 1]; (D) "H matches Q" fails, as H changed.  --expect D,R
#  ctl_S_pair_XVII_Hs.json pair XVII with H(z) replaced by H(3z/2): H' gets a zero in the closed disk, so (S) fails; (D) "H matches
#                          Q" and (R) (P_c is made from H) fail with it.                                                   --expect D,S,R
#  ctl_D_pair_XVII_a.json  pair XVII with the zero a moved by 2^-30: (D) fails (Q(a) != 0 and "H matches Q"); (J) fails, as J is
#                          made from a.                                                                                    --expect D,J
#  ctl_C_pair_XVII_m4.json pair XVII claiming the order m = 4 at 1 (the true order is 3): (C') fails.                    --expect C'
#  (J) controls need no file: run pair XVII with --bound 1.1143767 (too high) or --bound 1.1143765 (not the truncation). --expect J
# Ancillary file of the paper "Smale's mean value constant exceeds 1.1559" by Dave Goel (2026), Lemma 8.6; see README.txt.
# Version 0.20 (0.10 + the header names, for each control, EXACTLY the facts that fail; 0.10 said "each breaks exactly one fact").
"""Usage: make_controls.py PAIRS_DIR OUT_DIR"""
import json
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_pair import Gauss, parse_gauss  # noqa: E402

S_PAIR_I = Fraction(1250009, 1250000)
S_PAIR_XVII = Fraction(3, 2)
SHIFT_A = Fraction(1, 2 ** 30)


def fmt(val):
    """The pair-file format: 'p/q' or 'p/q + r*I/s' / 'p/q - r*I/s'."""
    if val.im == 0:
        return str(val.re)
    return f"{val.re} {'+' if val.im > 0 else '-'} {abs(val.im).numerator}*I/{abs(val.im).denominator}"


def scaled_h(data, scale):
    """H(s z): the coefficient of z^k is multiplied by s^k."""
    out = dict(data)
    out["H_ascending"] = [fmt(parse_gauss(cc).scale(scale ** kk)) for kk, cc in enumerate(data["H_ascending"])]
    return out


def moved_a(data):
    out = dict(data)
    aa = parse_gauss(data["a"])
    out["a"] = fmt(Gauss(aa.re + SHIFT_A, aa.im))
    return out


def claimed_order(data, order):
    out = dict(data)
    out["m"] = order
    return out


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    pairs, outdir = Path(sys.argv[1]), Path(sys.argv[2])
    outdir.mkdir(parents=True, exist_ok=True)
    pair_1 = json.loads((pairs / "pair_I_K2N18.json").read_text())
    pair_17 = json.loads((pairs / "pair_XVII_T6.json").read_text())
    controls = {"ctl_R_pair_I_Hs.json": scaled_h(pair_1, S_PAIR_I), "ctl_S_pair_XVII_Hs.json": scaled_h(pair_17, S_PAIR_XVII),
                "ctl_D_pair_XVII_a.json": moved_a(pair_17), "ctl_C_pair_XVII_m4.json": claimed_order(pair_17, 4)}
    for name, data in controls.items():
        (outdir / name).write_text(json.dumps(data, indent=1) + "\n")
        print(f"wrote {outdir / name}")


if __name__ == "__main__":
    main()
