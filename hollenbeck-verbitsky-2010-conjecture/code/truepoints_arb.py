#!/usr/bin/env python3
# truepoints_arb.py - the lower bounds s_- of the bracket proposition: Gamma >= e HOLDS at s_- for each exact p (Arb certificate).
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# For each pair p:s_-, certify_cell(p, p, s_-) of certify_arb.py proves Psi = Gamma - e >= 0 on all (y, t) (its parts A, B, C),
# hence Gamma >= e at every s <= s_- (power means): the conjecture holds there, s0(p) >= s_-.
# With badcells_arb.py --points (s0(p) < s_+) this brackets s0(p).
# Usage: python3 truepoints_arb.py 7/5:52986/10000 3/2:39572/10000 8/5:31799/10000 17/10:26921/10000 9/5:23764/10000
#            19/10:21588/10000 --radius 1/5 --ymax 3 --max-boxes 3000000
import argparse
import sys
import time
from fractions import Fraction

import flint
from flint import ctx

from certify_arb import CertFail, certify_cell, touching_box_ok


def touching_radius(p, s, radius):
    """Largest radius / 2^k (k <= 6) for which part (A) holds at the one-point cell [p, p]."""
    for shrink in (1, 2, 4, 8, 16, 32, 64):
        if touching_box_ok(p, p, s, radius / shrink, radius / shrink)[0]:
            return radius / shrink
    raise CertFail(f"(A) fails at p = {p}, s = {s} for every radius down to {radius / 64}")


def main_truepoints(pairs, radius, ymax, max_boxes):
    for p, s in pairs:
        start = time.time()
        rad = touching_radius(p, s, radius)
        nb, wb, nc, wc = certify_cell(p, p, s, rad, rad, ymax, max_boxes)
        print(f"TRUEPOINT p = {p} ({float(p):.4f}): Gamma >= e HOLDS at s_true = {s} ({float(s):.6f}): PROVED  (A) radius {rad}; (B) {nb} boxes, "
              f"min lb {float(wb):.2e}; (C) {nc} boxes, min lb {float(wc):.2e}; {time.time() - start:.0f} s", flush=True)


def parse_pair(text):
    p_text, s_text = text.split(":")
    return Fraction(p_text), Fraction(s_text)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("pairs", nargs="+", type=parse_pair, help="p:s_true, e.g. 3/2:3956/1000")
    parser.add_argument("--radius", type=Fraction, required=True)
    parser.add_argument("--ymax", type=Fraction, required=True)
    parser.add_argument("--max-boxes", type=int, required=True)
    args = parser.parse_args()
    print(f"RUN argv = {' '.join(sys.argv)} | python {sys.version.split()[0]} | python-flint {flint.__version__} | prec {ctx.prec}", flush=True)
    main_truepoints(args.pairs, args.radius, args.ymax, args.max_boxes)


if __name__ == "__main__":
    main()
