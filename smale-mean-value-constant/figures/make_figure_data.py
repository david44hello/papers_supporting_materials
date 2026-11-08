#!/usr/bin/env python3
# make_figure_data.py - data for Figures 2 and 3 of the paper: the margin of P_c as c varies, and the curve H(circle).
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
# Numerical illustration only; the proof does not use this file. Reads the public data file of the pair.
# Usage: make_figure_data.py --pair <pair.json> --outdir <dir>   |   make_figure_data.py --test --pair <pair.json>
import argparse
import json
from pathlib import Path

import mpmath as mp
import sympy

DECIMAL_DIGITS = 60
MARGIN_GRID_COARSE = 800
MARGIN_GRID_FINE_FROM = 0.90
MARGIN_GRID_FINE = 200
CIRCLE_GRID = 5760
CIRCLE_GRID_NEAR_ONE = 600
CIRCLE_NEAR_ONE_DECADES = 5
EXPECTED_MARGIN_NEAR_09231 = 7.03e-6
EXPECTED_MARGIN_AT_ONE = 1.141e-5
TEST_TOLERANCE = 0.01e-5
ZERO_TOP_COEFFICIENT = mp.mpf(10) ** (-40)
REFINE_LEVELS = 3
REFINE_POINTS = 12


def read_coefficients(pair_path):
    """The coefficients h_0, ..., h_n of H, as mpmath complex numbers."""
    data = json.loads(Path(pair_path).read_text())
    coefficients = []
    for text in data["H_ascending"]:
        value = sympy.sympify(text)
        real_part, imag_part = value.as_real_imag()
        coefficients.append(mp.mpc(mp.mpf(str(sympy.N(real_part, DECIMAL_DIGITS + 10))),
                                   mp.mpf(str(sympy.N(imag_part, DECIMAL_DIGITS + 10)))))
    return coefficients


def chebyshev_u_values(index_top, cosine):
    """U_0(c), ..., U_index_top(c), by the three-term recursion."""
    values = [mp.mpf(1), 2 * cosine]
    while len(values) <= index_top:
        values.append(2 * cosine * values[-1] - values[-2])
    return values[:index_top + 1]


def dieudonne_coefficients(coefficients, cosine):
    """P_c(w) = sum_{l>=1} h_l U_{l-1}(c) w^(l-1), ascending powers of w."""
    u_values = chebyshev_u_values(len(coefficients) - 2, cosine)
    return [coefficients[index] * u_values[index - 1] for index in range(1, len(coefficients))]


def margin_at(coefficients, cosine):
    """Smallest |w| - 1 over the zeros w of P_c."""
    ascending = dieudonne_coefficients(coefficients, mp.mpf(cosine))
    while abs(ascending[-1]) < ZERO_TOP_COEFFICIENT:  # U_{l-1}(c) can vanish: P_c then has lower degree (e.g. c = 0)
        ascending.pop()
    roots = mp.polyroots(list(reversed(ascending)), maxsteps=2000, extraprec=800)
    return min(abs(root) for root in roots) - 1


def margin_grid():
    """Values of c in [0, 1], finer towards the closest approach and c = 1. P_{-c}(w) = P_c(-w) gives the other half."""
    coarse = [index / MARGIN_GRID_COARSE for index in range(MARGIN_GRID_COARSE + 1)]
    fine = [MARGIN_GRID_FINE_FROM + (1 - MARGIN_GRID_FINE_FROM) * index / MARGIN_GRID_FINE
            for index in range(MARGIN_GRID_FINE + 1)]
    return sorted(set(coarse + fine + [0.9231]))


def local_minima(samples):
    """Indices of the interior samples below both neighbours, in a list sorted by c."""
    return [index for index in range(1, len(samples) - 1)
            if samples[index][1] < samples[index - 1][1] and samples[index][1] < samples[index + 1][1]]


def refine_dips(coefficients, samples):
    """Sample more finely around every local minimum, so that no dip is drawn too shallow."""
    for _ in range(REFINE_LEVELS):
        ordered = sorted(samples.items())
        for index in local_minima(ordered):
            left, right = ordered[index - 1][0], ordered[index + 1][0]
            for step in range(1, REFINE_POINTS):
                cosine = left + (right - left) * step / REFINE_POINTS
                samples[cosine] = margin_at(coefficients, cosine)
    return samples


def write_margin_curve(coefficients, out_path):
    samples = {cosine: margin_at(coefficients, cosine) for cosine in margin_grid()}
    samples = refine_dips(coefficients, samples)
    lines = ["c margin"]
    for cosine, margin in sorted(samples.items()):
        lines.append(f"{cosine:.8f} {mp.nstr(margin, 8)}")
    out_path.write_text("\n".join(lines) + "\n")


def evaluate(coefficients, point):
    return mp.polyval(list(reversed(coefficients)), point)


def write_circle_image(coefficients, out_path):
    """The curve H(e^{i theta}), scaled so that its largest modulus is 1."""
    near_one = [mp.mpf(10) ** (-mp.mpf(index) / CIRCLE_GRID_NEAR_ONE * CIRCLE_NEAR_ONE_DECADES) for index in range(CIRCLE_GRID_NEAR_ONE)]
    turns = sorted({2 * mp.mpf(index) / CIRCLE_GRID for index in range(CIRCLE_GRID + 1)}
                   | {turn for small in near_one for turn in (small / 10, 2 - small / 10)})
    points = [evaluate(coefficients, mp.expjpi(turn)) for turn in turns]
    scale = max(abs(point) for point in points)
    lines = ["x y"]
    for point in points:
        lines.append(f"{mp.nstr(point.real / scale, 6)} {mp.nstr(point.imag / scale, 6)}")
    out_path.write_text("\n".join(lines) + "\n")


def run_tests(pair_path):
    """The two margins printed in the paper."""
    coefficients = read_coefficients(pair_path)
    near = margin_at(coefficients, 0.9231)
    top = margin_at(coefficients, 1.0)
    print(f"margin at c = 0.9231: {mp.nstr(near, 6)} (paper: within about 7.03e-6)")
    print(f"margin at c = 1:      {mp.nstr(top, 6)} (paper: 1.00001141...)")
    assert abs(near - EXPECTED_MARGIN_NEAR_09231) < TEST_TOLERANCE, "margin near 0.9231 differs from the paper"
    assert abs(top - EXPECTED_MARGIN_AT_ONE) < TEST_TOLERANCE, "margin at 1 differs from the paper"
    print("PASS")


def main_make_figure_data(pair_path, outdir):
    coefficients = read_coefficients(pair_path)
    outdir.mkdir(exist_ok=True)
    write_circle_image(coefficients, outdir / "H_circle.dat")
    write_margin_curve(coefficients, outdir / "margin_curve.dat")


def main():
    parser = argparse.ArgumentParser(description="Figure data for the 9-page Smale paper.")
    parser.add_argument("--pair", required=True)
    parser.add_argument("--outdir")
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    mp.mp.dps = DECIMAL_DIGITS
    if args.test:
        run_tests(args.pair)
        return
    main_make_figure_data(args.pair, Path(args.outdir))


if __name__ == "__main__":
    main()
