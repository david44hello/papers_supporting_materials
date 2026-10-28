#!/usr/bin/env python3
# counterexample_quadrature_arb.py - the explicit counterexample: Arb enclosure of int_T G(z, w) dtheta/2pi for the closed-form
#   three-slit function of the paper, by quadrature in the logarithm of the distance to each end point.
# Author: Dave Goel
# Copyright (C) Dave Goel 2026--now. All rights reserved.
# Version 1.00 (2026-10-27). Supporting material for "The Hollenbeck-Verbitsky (2010) conjecture is false".
#
# THE FUNCTION. Rays tau_1 = -pi/p, tau_2 = t*, tau_3 = b; al_A = (t* + pi/p)/pi, al_B = (b - t*)/pi, al_C = 2 - al_A - al_B;
#   th_A = -delta/2, th_B = delta/2, th_C = pi. Pi(zeta) = (1 - zeta e^(-i th_A))^(-al_A/2) (1 - zeta e^(-i th_B))^(-al_B/2) (1 + zeta)^(-al_C/2)
#   (principal branches), Y(zeta) = y2 [delta/(2 pi) + (1/(pi i)) log((1 - zeta e^(-i th_B)) / (1 - zeta e^(-i th_A)))] (Herglotz of
#   y2 * indicator of the arc (th_A, th_B)), z = e^(i gam/2) Pi e^(Y/2), w = zeta e^(i gam/2) Pi e^(-Y/2), f = z + conj(w) on T.
#   g = zw = e^(i gam) zeta Pi^2 is starlike onto C minus radial slits at tau_1, tau_2, tau_3 (gam puts arc (th_C, th_A) on tau_1).
#   On T: |z/w| = e^y (y = y2 on the arc (th_A, th_B), 0 elsewhere) and arg(zw) = tau_j on arc j, so (paper normalisation, averaged
#   power mean, A = 1/(2 cos(pi/2p))): int_T G(z, w) dtheta/2pi = sum_j Gamma(y_j, tau_j) J_j, J_j = int_arc_j |g|^q dtheta/2pi,
#   |g| = prod_j |2 sin((theta - th_j)/2)|^(-al_j). int G < 0 <=> f violates HV at (p, s). Here b = pi/p + eps/q.
"""Usage: python3 counterexample_quadrature_arb.py --verify P_NUM P_DEN S_NUM S_DEN TSTAR EPS Y2 LOGDELTA PREC
          python3 counterexample_quadrature_arb.py --selfcheck   (mpmath, moderate delta, closed formulas vs direct integral of G)
          python3 counterexample_quadrature_arb.py --test        (the self-check, plus controls: ln(1/delta) = 50 holds, 2500 violates)
   The runs in logs/: --verify 3 2 398 100 1.79 0.0102 0.4865 L 128 for L = ln(1/delta) = 2000, 2200, 2500, 3000."""
import sys

import flint
import mpmath as mp
from flint import acb, arb

V_MARGIN = 1500                                              # integrate v down to ln(scale) - V_MARGIN; the rest is the tail bound
V_PIECE = 25                                                 # acb.integral pieces in v (long ranges make huge complex boxes: nan)


def parameters(pp, ss, tstar, eps, logdelta):
    """Exact (arb) parameters of the counterexample family: rays -pi/p, t*, pi/p + eps/q."""
    pi = arb.pi()
    return parameters_rays(pp, (-pi / pp, tstar, pi / pp + eps / (pp / 2)), logdelta)


def parameters_rays(pp, taus, logdelta):
    """Exact (arb) parameters for rays tau_1 < tau_2 < tau_3 < tau_1 + 2 pi."""
    pi = arb.pi()
    al_a, al_b = (taus[1] - taus[0]) / pi, (taus[2] - taus[1]) / pi
    delta = (-logdelta).exp()
    return dict(q=pp / 2, taus=tuple(taus), als=(al_a, al_b, 2 - al_a - al_b), ths=(-delta / 2, delta / 2, pi), delta=delta)


def gamma_arb(yy, tt, pp, ss):
    qq = pp / 2
    return ((yy.cosh() + tt.cos()) ** qq / (1 + (arb.pi() / pp).cos()) ** qq - (ss * yy / 2).cosh() ** (pp / ss))


def offsets(prm, base, sign, end_idx, half):
    """(c_j, sigma_j) with theta - th_j = c_j + sign * x on the half-arc from base, c_j = base - th_j UNWRAPPED (so the neck offsets
    +-delta keep full relative precision), sigma_j = the constant sign of sin((c_j + sign x)/2) there; None for the end factor."""
    out = []
    for jj, th in enumerate(prm["ths"]):
        if jj == end_idx:
            out.append(None)                                 # end factor is exactly 2 sin(x/2) either way (no pi - x/2 cancellation)
            continue
        cc = base - th
        probe = ((cc + sign * half / 2) / 2).sin()
        if probe.lower() > 0:
            out.append((cc, 1))
        elif probe.upper() < 0:
            out.append((cc, -1))
        else:
            raise SystemExit(f"sign of sin not determined on the half-arc: c = {cc}")
    return out


def integrand_v(vv, analytic, prm, offs, sign):
    """e^v * |g|^q / 2 pi at theta = base + sign e^v (acb, analytic-checked branch of log)."""
    xx = vv.exp()
    total = acb(0)
    for off, al in zip(offs, prm["als"]):
        fac = 2 * (xx / 2).sin() if off is None else off[1] * 2 * ((acb(off[0]) + sign * xx) / 2).sin()
        total += -prm["q"] * al * fac.log(analytic=analytic)
    return (total + vv).exp() / (2 * arb.pi())


def tail_bound(prm, offs, sign, end_idx, x0):
    """Upper bound of int_0^x0 |g|^q dx / 2 pi on a half-arc: the end factor (2 sin(x/2))^(-a) <= (0.99 x)^(-a) for x <= x0 << 1;
    every other factor is bounded by its value at the lower end of its enclosure over x in [0, x0]."""
    ball = arb(0).union(x0)
    bound = arb(1)
    for jj, (off, al) in enumerate(zip(offs, prm["als"])):
        if jj == end_idx:
            continue
        fac = off[1] * 2 * ((off[0] + sign * ball) / 2).sin()
        if not fac.lower() > 0:
            raise SystemExit(f"tail factor not positive: {fac}")
        bound *= arb(fac.lower()) ** (-prm["q"] * al)
    apow = prm["q"] * prm["als"][end_idx]
    return bound * arb("0.99") ** (-apow) * x0 ** (1 - apow) / (1 - apow) / (2 * arb.pi())


def half_integral(prm, base, sign, length, end_idx, prec):
    """Enclosure of int over theta = base + sign*x, x in (0, length), of |g|^q dtheta / 2 pi. The scale of the end point is delta
    at th_A, th_B (the neck) and 1 at th_C; v runs from ln(scale) - V_MARGIN to ln(length)."""
    offs = offsets(prm, base, sign, end_idx, length)
    scale = prm["delta"] if end_idx < 2 else arb(1)
    v_lo = scale.log() - V_MARGIN
    flint.ctx.prec = prec
    v_hi = length.log()
    npieces = max(1, int(float((v_hi - v_lo).upper()) / V_PIECE) + 1)
    cuts = [v_lo + (v_hi - v_lo) * kk / npieces for kk in range(npieces + 1)]
    main = sum((acb.integral(lambda vv, an: integrand_v(vv, an, prm, offs, sign), acb(aa), acb(bb)).real
                for aa, bb in zip(cuts[:-1], cuts[1:])), arb(0))
    if not main.is_finite():
        raise SystemExit(f"non-finite integral on the half-arc from end {end_idx} (sign {sign})")
    tail = tail_bound(prm, offs, sign, end_idx, v_lo.exp())
    return main + arb(0).union(tail)


def arc_integrals(prm, prec):
    """J_1 (arc th_C -> th_A, ray tau_1), J_2 (th_A -> th_B, ray tau_2), J_3 (th_B -> th_C, ray tau_3)."""
    th_a, th_b, th_c = prm["ths"]
    arcs = [(th_c - 2 * arb.pi(), th_a, 2, 0), (th_a, th_b, 0, 1), (th_b, th_c, 1, 2)]
    out = []
    for lo, hi, idx_lo, idx_hi in arcs:
        half = (hi - lo) / 2
        out.append(half_integral(prm, lo, 1, half, idx_lo, prec) + half_integral(prm, hi, -1, half, idx_hi, prec))
    return out


def verify(pp, ss, tstar, eps, y2, logdelta, prec):
    flint.ctx.prec = prec
    prm = parameters(pp, ss, tstar, eps, logdelta)
    js = arc_integrals(prm, prec)
    ys = (arb(0), y2, arb(0))
    gams = [gamma_arb(yy, tt, pp, ss) for yy, tt in zip(ys, prm["taus"])]
    total = sum((gg * jj for gg, jj in zip(gams, js)), arb(0))
    mass = sum(js, arb(0))
    print(f"p={pp.mid()} s={ss.mid()} t*={tstar.mid()} eps={eps.mid()} y2={y2.mid()} ln(1/delta)={logdelta.mid()} prec={prec}")
    for kk in range(3):
        print(f"  ray tau_{kk+1} = {prm['taus'][kk].str(10)}: Gamma = {gams[kk].str(12)}  J = {js[kk].str(12)}")
    print(f"  int G(z,w) dtheta/2pi = {total.str(15)}   (mass {mass.str(10)})")
    verdict = "VIOLATES HV (rigorous: upper end < 0)" if total.upper() < 0 else ("HOLDS here" if total.lower() > 0 else "UNDECIDED")
    print(f"  VERDICT: {verdict}; ratio int G / mass = {(total / mass).str(6)}", flush=True)
    return total


def main_explicit(argv):
    if argv == ["--test"]:
        return run_tests()
    if argv == ["--selfcheck"]:
        return 0 if selfcheck() else 1
    if argv and argv[0] == "--verify":
        pp = arb(int(argv[1])) / int(argv[2])
        ss = arb(int(argv[3])) / int(argv[4])
        tstar, eps, y2, logdelta = (arb(val) for val in argv[5:9])
        verify(pp, ss, tstar, eps, y2, logdelta, int(argv[9]))
        return 0
    raise SystemExit(__doc__)


# ---------------------------------------------------------------- end-to-end check of the closed formulas (mpmath, floats)

def closed_form_zw(zeta, prm_f):
    """z, w from the closed formulas (mpmath complex)."""
    th_a, th_b, th_c = prm_f["ths"]
    al_a, al_b, al_c = prm_f["als"]
    prod = ((1 - zeta * mp.exp(-1j * th_a)) ** (-al_a / 2) * (1 - zeta * mp.exp(-1j * th_b)) ** (-al_b / 2)
            * (1 - zeta * mp.exp(-1j * th_c)) ** (-al_c / 2))
    yy = prm_f["y2"] * (prm_f["delta"] / (2 * mp.pi) + mp.log((1 - zeta * mp.exp(-1j * th_b)) / (1 - zeta * mp.exp(-1j * th_a))) / (mp.pi * 1j))
    rot = mp.exp(1j * prm_f["gam"] / 2)
    return rot * prod * mp.exp(yy / 2), zeta * rot * prod * mp.exp(-yy / 2)


def g_paper(zz, ww, pp, ss):
    aa = 1 / (2 * mp.cos(mp.pi / (2 * pp)))
    return aa ** pp * abs(zz + mp.conj(ww)) ** pp - ((abs(zz) ** ss + abs(ww) ** ss) / 2) ** (pp / ss)


def float_family(taus, logdelta, y2):
    """mpmath parameters of the family for given rays (gam fixed so the arc (th_C, th_A) lies on tau_1)."""
    delta = mp.exp(-logdelta)
    al_a, al_b = (taus[1] - taus[0]) / mp.pi, (taus[2] - taus[1]) / mp.pi
    prm_f = dict(ths=(-delta / 2, delta / 2, mp.pi), als=(al_a, al_b, 2 - al_a - al_b), y2=y2, delta=delta, gam=mp.mpf(0))
    zz, ww = closed_form_zw(mp.exp(-2j), prm_f)                 # theta = -2 lies on the arc (th_C, th_A) when delta < 4
    prm_f["gam"] = taus[0] - mp.arg(zz * ww)
    return prm_f


def direct_boundary_integral(func, prm_f, v_min):
    """int_T func(theta) dtheta / 2 pi, |zeta| = 1 exactly; each arc split at its midpoint, theta = end +- e^v, v >= v_min."""
    th_a, th_b, th_c = prm_f["ths"]
    total = mp.mpf(0)
    for lo, hi in ((th_c - 2 * mp.pi, th_a), (th_a, th_b), (th_b, th_c)):
        half = (hi - lo) / 2
        for base, sign in ((lo, 1), (hi, -1)):
            total += mp.quad(lambda vv: func(base + sign * mp.exp(vv)) * mp.exp(vv), [v_min, mp.log(half) - 4, mp.log(half)])
    return total / (2 * mp.pi)


def selfcheck_identity():
    """Closed formulas vs the identity G = |g|^q Gamma(y, arg g), ON |zeta| = 1, at balanced test rays (q al_j = 1/2: light tails).
    dps 60 keeps 1 - zeta e^(-i th_j) accurate to 1e-12 relative down to x = e^-110 (the tail beyond is < e^-55)."""
    mp.mp.dps = 60
    pp, ss, y2 = mp.mpf(3) / 2, mp.mpf("3.98"), mp.mpf("0.4865")
    taus = (mp.mpf(-2), mp.mpf(-2) + 2 * mp.pi / 3, mp.mpf(-2) + 4 * mp.pi / 3)
    prm_f = float_family(taus, mp.mpf(2), y2)
    ok = abs(closed_form_zw(mp.mpf(0), prm_f)[1]) == 0
    args = [mp.arg(mp.fprod(closed_form_zw(mp.exp(1j * mp.mpf(th)), prm_f))) for th in ("-2.5", "0", "2.5")]
    ok &= all(abs(mp.arg(mp.exp(1j * (aa - tt)))) < 1e-20 for aa, tt in zip(args, taus))
    direct = direct_boundary_integral(lambda th: g_paper(*closed_form_zw(mp.exp(1j * th), prm_f), pp, ss), prm_f, -110)
    flint.ctx.prec = 160
    prm = parameters_rays(arb(3) / 2, [arb(-2), arb(-2) + 2 * arb.pi() / 3, arb(-2) + 4 * arb.pi() / 3], arb(2))
    js = arc_integrals(prm, 160)
    gams = [gamma_arb(yy, tt, arb(3) / 2, arb(398) / 100) for yy, tt in zip((arb(0), arb("0.4865"), arb(0)), prm["taus"])]
    formula = sum((gg * jj for gg, jj in zip(gams, js)), arb(0))
    diff = abs(direct - mp.mpf(formula.mid().str(40, radius=False)))
    print(f"  identity: w(0) = 0 and arg(zw) = tau_j on the arcs: {ok}; direct int G on |zeta|=1 = {mp.nstr(direct, 15)}; "
          f"sum Gamma_j J_j (Arb) = {formula.str(15)}; |diff| = {mp.nstr(diff, 3)}")
    return ok and diff < 1e-20


def selfcheck_arcs():
    """Arb arc integrals vs an independent mpmath (tanh-sinh) evaluation of the same integrals at the REAL exponents (q al_A = 0.93)."""
    mp.mp.dps = 40
    taus = (-mp.pi / mp.mpf(1.5), mp.mpf("1.79"), mp.pi / mp.mpf(1.5) + mp.mpf("0.0102") / mp.mpf(0.75))
    prm_f = float_family(taus, mp.mpf(30), mp.mpf(0))
    th_a, th_b, th_c = prm_f["ths"]
    js_mp = []
    for lo, hi, ends in ((th_c - 2 * mp.pi, th_a, (2, 0)), (th_a, th_b, (0, 1)), (th_b, th_c, (1, 2))):
        half = (hi - lo) / 2
        acc = mp.mpf(0)
        for base, sign, end in ((lo, 1, ends[0]), (hi, -1, ends[1])):
            scale = prm_f["delta"] if end < 2 else mp.mpf(1)
            vlo = mp.log(scale) - 1500
            pts = [vlo + (mp.log(half) - vlo) * kk / 60 for kk in range(61)]
            acc += mp.quad(lambda vv: modg_q(base + sign * mp.exp(vv), prm_f, base, sign, end, mp.exp(vv)) * mp.exp(vv), pts)
        js_mp.append(acc / (2 * mp.pi))
    flint.ctx.prec = 160
    prm = parameters(arb(3) / 2, arb(398) / 100, arb("1.79"), arb("0.0102"), arb(30))
    js = arc_integrals(prm, 160)
    rel = max(abs(jm - mp.mpf(ja.mid().str(40, radius=False))) / jm for jm, ja in zip(js_mp, js))
    print(f"  arcs (ln 1/delta = 30): mpmath J = {[mp.nstr(jj, 12) for jj in js_mp]}; Arb J = {[jj.str(12) for jj in js]}; "
          f"max rel diff {mp.nstr(rel, 3)}")
    return rel < 1e-15


def modg_q(theta, prm_f, base, sign, end, xx):
    """|g|^q at theta; the end factor is 2 sin(x/2) exactly (no cancellation)."""
    val = mp.mpf(1)
    for jj, (th, al) in enumerate(zip(prm_f["ths"], prm_f["als"])):
        fac = 2 * mp.sin(xx / 2) if jj == end else abs(2 * mp.sin((theta - th) / 2))
        val *= fac ** (-mp.mpf(3) / 4 * al)
    return val


def selfcheck():
    ok = selfcheck_identity() & selfcheck_arcs()
    print("SELFCHECK PASS" if ok else "SELFCHECK FAIL", flush=True)
    return ok


def run_tests():
    """Self-check of the closed formulas, plus controls: small delta-range (ln 1/delta = 50) must NOT violate; ln 1/delta = 2500 must."""
    ok = selfcheck()
    args = dict(pp=arb(3) / 2, ss=arb(398) / 100, tstar=arb("1.79"), eps=arb("0.0102"), y2=arb("0.4865"), prec=128)
    holds = verify(logdelta=arb(50), **args)
    fails = verify(logdelta=arb(2500), **args)
    ok &= holds.lower() > 0 and fails.upper() < 0
    print("ALL TESTS PASS" if ok else "TEST FAILURE", flush=True)
    return 0 if ok else 1


def main():
    sys.exit(main_explicit(sys.argv[1:]))


if __name__ == "__main__":
    main()
