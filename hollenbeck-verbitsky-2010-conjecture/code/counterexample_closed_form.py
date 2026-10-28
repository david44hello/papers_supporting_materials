#!/usr/bin/env python3
# counterexample_closed_form.py - the explicit counterexample: floating-point (mpmath, 40 digits) evaluation of the closed form
#   int G = (1/2pi) (h0 K1 delta^(-e1) + K0), O(delta) terms dropped: K1, K0, the threshold ln(1/delta), int G at four delta.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
# Numerical, not certified. a, bb, c = q al_A, q al_B, q al_C (as in counterexample_beta_arb.py); e1 = a + bb - 1; h0 = 2^(-c).
# Usage: python3 counterexample_closed_form.py
from mpmath import mp, mpf, pi, cos, cosh, sin, beta, quad, log, exp


def parameters():
    """The explicit counterexample at p = 3/2, s = 3.98: t* = 1.79, eps = 0.0102, y2 = 0.4865."""
    p, s = mpf(3) / 2, mpf(398) / 100
    q = p / 2
    tstar, eps, y2 = mpf(179) / 100, mpf(102) / 10000, mpf(4865) / 10000
    b = pi / p + eps / q
    al_a, al_b = (tstar + pi / p) / pi, (b - tstar) / pi
    return {"p": p, "s": s, "q": q, "tstar": tstar, "y2": y2, "b": b,
            "a": q * al_a, "bb": q * al_b, "c": q * (2 - al_a - al_b)}


def gamma(par, y, t):
    p, s, q = par["p"], par["s"], par["q"]
    return ((cosh(y) + cos(t)) / (1 + cos(pi / p))) ** q - cosh(s * y / 2) ** (p / s)


def closed_form_constants(par):
    """K1, K0, H0, e1 of the closed form."""
    a, bb, c = par["a"], par["bb"], par["c"]
    e1, h0 = a + bb - 1, mpf(2) ** (-c)
    smooth = lambda x: (2 * sin(x / 2) / x) ** (-a - bb) * (2 * cos(x / 2)) ** (-c)
    i1 = quad(lambda x: x ** (-a - bb) * (smooth(x) - h0), [0, mpf(1) / 2, 1])
    i2 = quad(lambda x: (2 * sin(x / 2)) ** (-a - bb) * (2 * cos(x / 2)) ** (-c), [1, 2, 3, pi])
    g_short, g_b = gamma(par, par["y2"], par["tstar"]), gamma(par, 0, par["b"])
    k1 = g_short * beta(1 - a, 1 - bb) + g_b * beta(1 - bb, e1)
    k0 = g_b * (i1 + i2 - h0 / e1)
    return {"e1": e1, "h0": h0, "i1": i1, "i2": i2, "k1": k1, "k0": k0, "g_short": g_short, "g_b": g_b}


def main_closedform_check():
    mp.dps = 40
    par = parameters()
    con = closed_form_constants(par)
    print(f"q al = {mp.nstr(par['a'], 7)} {mp.nstr(par['bb'], 7)} {mp.nstr(par['c'], 7)}; e1 = {mp.nstr(con['e1'], 12)}")
    print(f"Gamma(y2, t*) = {mp.nstr(con['g_short'], 15)}; Gamma(0, b) = {mp.nstr(con['g_b'], 15)}; "
          f"Gamma(0, -2pi/3) = {mp.nstr(gamma(par, 0, -2 * pi / 3), 3)}")
    print(f"K1 terms: short arc Gamma(y2, t*) B(1-a, 1-bb) = {mp.nstr(con['g_short'] * beta(1 - par['a'], 1 - par['bb']), 8)}; "
          f"arc past the contact point Gamma(0, b) B(1-bb, e1) = {mp.nstr(con['g_b'] * beta(1 - par['bb'], con['e1']), 8)}; "
          f"Gamma(y2, t*) - e(t*) = {mp.nstr(con['g_short'] - mp.tan(pi / (2 * par['p'])) * cos(par['q'] * par['tstar']), 8)}")
    print(f"I1 = {mp.nstr(con['i1'], 15)}; I2 = {mp.nstr(con['i2'], 15)}; K1 = {mp.nstr(con['k1'], 15)}; K0 = {mp.nstr(con['k0'], 15)}")
    print(f"threshold ln(1/delta) = {mp.nstr(log(-con['k0'] / (con['h0'] * con['k1'])) / con['e1'], 12)}")
    for big_l in (2000, 2200, 2500, 3000):
        total = (con["h0"] * con["k1"] * exp(con["e1"] * big_l) + con["k0"]) / (2 * pi)
        print(f"ln(1/delta) = {big_l}: int G = {mp.nstr(total, 13)}")


def main():
    main_closedform_check()


if __name__ == "__main__":
    main()
