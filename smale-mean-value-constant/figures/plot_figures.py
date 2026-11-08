#!/usr/bin/env python3
# plot_figures.py - draws fig_margin.pdf and fig_image.pdf for the paper from the files of make_figure_data.py.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
# Usage: plot_figures.py --dir <figures dir>   |   plot_figures.py --test --dir <figures dir>
import argparse
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

FONT_SIZE = 9
MARGIN_SIZE_INCHES = (5.4, 1.35)
MARGIN_TICKS = (1e-5, 1e-3, 1e-1)
IMAGE_SIZE_INCHES = (2.3, 2.3)
LOWEST_C = 0.92312
LOWEST_MARGIN = 7.03e-6
EXPECTED_MIN_ROWS = 1000


def read_pairs(path):
    """The two numeric columns of a data file, skipping its one header line."""
    rows = [line.split() for line in path.read_text().splitlines()[1:]]
    return [float(row[0]) for row in rows], [float(row[1]) for row in rows]


def set_style():
    plt.rcParams.update({"font.family": "serif", "font.serif": ["cmr10"], "axes.formatter.use_mathtext": True,
                         "mathtext.fontset": "cm", "font.size": FONT_SIZE, "path.simplify": False,
                         "axes.linewidth": 0.6, "lines.linewidth": 0.8, "pdf.fonttype": 42})


def plot_margin(figures_dir):
    """Log-scale curve of (smallest |w|) - 1 over the zeros w of P_c, for c in [0, 1]."""
    cosines, margins = read_pairs(figures_dir / "margin_curve.dat")
    figure, axes = plt.subplots(figsize=MARGIN_SIZE_INCHES)
    axes.semilogy(cosines, margins, color="black")
    axes.set_xlim(0, 1)
    axes.set_xlabel(r"$c$")
    axes.set_ylabel(r"margin of $P_c$")
    axes.set_ylim(4e-6, 0.1)
    axes.set_yticks(MARGIN_TICKS)
    axes.minorticks_off()
    figure.tight_layout(pad=0.3)
    figure.savefig(figures_dir / "fig_margin.pdf")
    plt.close(figure)


def plot_image(figures_dir):
    """The simple closed curve H(unit circle), with the region it bounds, H(D), shaded."""
    xs, ys = read_pairs(figures_dir / "H_circle.dat")
    figure, axes = plt.subplots(figsize=IMAGE_SIZE_INCHES)
    axes.fill(xs, ys, color="0.88")
    axes.plot(xs, ys, color="black")
    axes.plot([0], [0], marker="o", markersize=2.5, color="black")  # H(b) = 0 stays at the origin: the data are only scaled
    axes.set_aspect("equal")
    axes.set_axis_off()
    figure.tight_layout(pad=0.1)
    figure.savefig(figures_dir / "fig_image.pdf")
    plt.close(figure)


def run_tests(figures_dir):
    """The inputs exist, are long enough, and agree with the two printed margins."""
    cosines, margins = read_pairs(figures_dir / "margin_curve.dat")
    assert len(cosines) >= EXPECTED_MIN_ROWS, "margin curve too short"
    lowest = min(margins)
    assert abs(lowest - LOWEST_MARGIN) < 0.01e-6, f"lowest margin {lowest} differs from the paper"
    assert abs(cosines[margins.index(lowest)] - LOWEST_C) < 1e-3, "the lowest point has moved"
    print("PASS")


def main_plot_figures(figures_dir):
    set_style()
    plot_margin(figures_dir)
    plot_image(figures_dir)


def main():
    parser = argparse.ArgumentParser(description="Figures of the 9-page Smale paper.")
    parser.add_argument("--dir", required=True)
    parser.add_argument("--test", action="store_true")
    args = parser.parse_args()
    if args.test:
        run_tests(Path(args.dir))
        return
    main_plot_figures(Path(args.dir))


if __name__ == "__main__":
    main()
