#!/usr/bin/env python3
# arb_dual.py - forward-mode dual numbers over python-flint arb balls: value and gradient enclosures (used by certify_arb.py).
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# A Dual holds an arb enclosure of f over a box and arb enclosures of the partial derivatives over the SAME box (each operation applies
# the chain rule with arb arithmetic, so every enclosure is rigorous). mean_value_lower(f, box) = lower end of
#   f(mid) + sum_i df/dx_i(box) * [box_i - mid_i]      (mean value theorem; valid when f is C^1 on the box).
# Usage: python3 arb_dual.py   (self-test)
from flint import arb


class NonPositiveBase(Exception):
    """Raised when a Dual power has a base not certainly > 0 (callers fall back to a naive bound)."""


class Dual:
    __slots__ = ("val", "grad")

    def __init__(self, val, grad):
        self.val, self.grad = val, grad

    @staticmethod
    def lift(other, nvar):
        return other if isinstance(other, Dual) else Dual(other if isinstance(other, arb) else arb(other), [arb(0)] * nvar)

    def _chain(self, val, deriv):
        return Dual(val, [deriv * gg for gg in self.grad])

    def __add__(self, other):
        other = Dual.lift(other, len(self.grad))
        return Dual(self.val + other.val, [aa + bb for aa, bb in zip(self.grad, other.grad)])

    __radd__ = __add__

    def __neg__(self):
        return Dual(-self.val, [-gg for gg in self.grad])

    def __sub__(self, other):
        return self + (-Dual.lift(other, len(self.grad)))

    def __rsub__(self, other):
        return Dual.lift(other, len(self.grad)) - self

    def __mul__(self, other):
        other = Dual.lift(other, len(self.grad))
        return Dual(self.val * other.val, [self.val * bb + other.val * aa for aa, bb in zip(self.grad, other.grad)])

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Dual.lift(other, len(self.grad))
        return self * other.recip()

    def __rtruediv__(self, other):
        return Dual.lift(other, len(self.grad)) * self.recip()

    def recip(self):
        inv = 1 / self.val
        return self._chain(inv, -inv * inv)

    def exp(self):
        ev = self.val.exp()
        return self._chain(ev, ev)

    def log(self):
        return self._chain(self.val.log(), 1 / self.val)

    def __pow__(self, other):                  # positive base only: x^e = exp(e log x)
        if not self.val > 0:
            raise NonPositiveBase("Dual pow needs a positive base")
        return (Dual.lift(other, len(self.grad)) * self.log()).exp()

    def cosh(self):
        return self._chain(self.val.cosh(), self.val.sinh())

    def sinh(self):
        return self._chain(self.val.sinh(), self.val.cosh())

    def cos(self):
        return self._chain(self.val.cos(), -self.val.sin())

    def sin(self):
        return self._chain(self.val.sin(), self.val.cos())

    def tan(self):
        tv = self.val.tan()
        return self._chain(tv, 1 + tv * tv)


def variables(balls):
    nvar = len(balls)
    return [Dual(ball, [arb(1) if jj == ii else arb(0) for jj in range(nvar)]) for ii, ball in enumerate(balls)]


def mean_value_lower(fn, box_balls, mid_balls):
    """Rigorous lower bound of fn over the box: fn(mid) + grad(box) . (box - mid). fn takes Duals (or arbs) and returns a Dual."""
    over_box = fn(*variables(box_balls))
    at_mid = fn(*variables(mid_balls)).val
    total = at_mid
    for gg, ball, mid in zip(over_box.grad, box_balls, mid_balls):
        total = total + gg * (ball - mid)
    return max(total.lower(), over_box.val.lower()), over_box.val


def run_tests():
    if not __debug__:
        raise SystemExit("tests need asserts: do not run with python -O")
    xx = arb("0.3") + arb(0).union(arb("0.01"))         # ball around [0.3, 0.31]
    yy = arb("1.2")
    fx, fy = variables([xx, yy])
    res = (fx * fy).cosh() / (fx + 2) + (fy ** fx).tan() - fx.sin() * fy.exp().log()
    # finite-difference check of the gradient at a point
    import math
    def plain(a, b):
        return math.cosh(a * b) / (a + 2) + math.tan(b ** a) - math.sin(a) * b
    xp, yp = variables([arb("0.3"), arb("1.2")])
    g = ((xp * yp).cosh() / (xp + 2) + (yp ** xp).tan() - xp.sin() * yp.exp().log()).grad
    h = 1e-6
    fdx = (plain(0.3 + h, 1.2) - plain(0.3 - h, 1.2)) / (2 * h)
    fdy = (plain(0.3, 1.2 + h) - plain(0.3, 1.2 - h)) / (2 * h)
    assert abs(float(g[0].mid()) - fdx) < 1e-6 and abs(float(g[1].mid()) - fdy) < 1e-6, (g, fdx, fdy)
    assert res.val.contains(arb(plain(0.3, 1.2))), "box enclosure misses a point value"
    lo, _naive = mean_value_lower(lambda a, b: (a * b).cosh(), [xx, yy], [arb("0.305"), yy])
    assert lo <= math.cosh(0.3 * 1.2) + 1e-12
    print("dual tests passed: gradients match finite differences; mean-value bound below the true minimum")


if __name__ == "__main__":
    run_tests()
