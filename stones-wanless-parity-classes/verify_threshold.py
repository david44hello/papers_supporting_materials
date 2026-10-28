#!/usr/bin/env python3
"""Exact finite inequalities for the parity-class theorem."""
# version 0.10 — 2026-10-28: exact integer/rational certificate for orders 23 through 63, with controls.
# Author: Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

import argparse
from fractions import Fraction
from math import factorial, isqrt


def fischer_product(dimension, power):
    """P(dimension,power) in Alpoge's determinant coefficient identity."""
    result = 1
    for step in range(1, power + 1):
        for offset in range(dimension):
            result *= step + offset
    return result


def ceil_root(integer):
    root = isqrt(integer)
    return root + (root * root != integer)


def coefficient_majorant(dimension, power):
    left = power // 2
    product = fischer_product(dimension, left)
    product *= fischer_product(dimension, power - left)
    return ceil_root(product)


def signed_count_majorant(order):
    denominator = factorial(order - 1)
    row_bound = Fraction(coefficient_majorant(order, order - 1), denominator)
    if order % 2:
        parity_bound = Fraction(coefficient_majorant(order - 1, order - 1), denominator)
    else:
        parity_bound = Fraction(coefficient_majorant(order, order), denominator * factorial(order))
    return 2 * row_bound + parity_bound


def reduced_count_minorant(order):
    product = Fraction(1, factorial(order) * factorial(order - 1))
    for degree in range(1, order + 1):
        vdw = Fraction(factorial(order) * degree ** order, order ** order)
        if degree == 1:
            schrijver = Fraction(1)
        else:
            schrijver = Fraction((degree - 1) ** (degree - 1), degree ** (degree - 2)) ** order
        product *= max(vdw, schrijver)
    return product


def certificate(order):
    upper = signed_count_majorant(order)
    lower = reduced_count_minorant(order)
    ratio = upper / lower
    scaled_ceiling = (10 ** 6 * ratio.numerator + ratio.denominator - 1) // ratio.denominator
    return upper < lower, scaled_ceiling


def main_test():
    for dimension in range(1, 8):
        for power in range(8):
            alternative = 1
            for offset in range(dimension):
                alternative *= factorial(power + offset) // factorial(offset)
            assert fischer_product(dimension, power) == alternative
    for integer in range(101):
        root = ceil_root(integer)
        assert root * root >= integer
        assert root == 0 or (root - 1) ** 2 < integer
    assert reduced_count_minorant(2) == 1
    assert certificate(22)[0] is False  # Negative control: this bound does not prove order 22.
    assert certificate(23)[0] is True
    print("controls PASS: product identity, root rounding, order 2, failing order 22, passing order 23")


def main_verify(first, last):
    failed = []
    for order in range(first, last + 1):
        holds, scaled = certificate(order)
        print(f"{order} {scaled} {'PASS' if holds else 'FAIL'}", flush=True)
        if not holds:
            failed.append(order)
    if failed:
        raise SystemExit(f"inequality unproved at orders {failed}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--first", type=int)
    parser.add_argument("--last", type=int)
    args = parser.parse_args()
    if args.test:
        main_test()
    elif args.first is not None and args.last is not None and 2 <= args.first <= args.last:
        main_verify(args.first, args.last)
    else:
        parser.error("choose --test or explicit --first and --last with 2 <= first <= last")


if __name__ == "__main__":
    main()
