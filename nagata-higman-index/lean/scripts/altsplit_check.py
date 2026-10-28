#!/usr/bin/env python3
# altsplit_check.py — exact check of youngSystemC_exists / AltSplit.
"""Exact rational check, on Young's seminormal form, of every clause of `AltSplit` for every self-conjugate
shape with N <= 9, plus the cited Frobenius values. Conventions follow the Lean files:
entries 0..N-1, cells (row, col) 0-indexed, content = col - row, cycle type WITH fixed points (Perm.partition).

For lam = lam' the intertwiner Gamma (Gamma rho(s) = -rho(s) Gamma) is monomial in the Young basis,
Gamma e_T = g_T e_{T^t}, because it anticommutes with every J_k and content vectors determine tableaux.
Gamma^2 = c I (c rational). Over C, V+- = the (+-sqrt c)-eigenspaces, and tr(rho(s)|V+) - tr(rho(s)|V-) =
tr(rho(s) Gamma)/sqrt(c). So Frobenius 'chi+ = chi- off h(lam)' <=> tr(rho(s) Gamma) = 0 off h(lam): exact in Q.
Irreducible + non-isomorphic <=> dim End_{A_N}(S^lam) = 2 <=> (2/N!) sum_{s even} chi(s)^2 = 2 (Maschke, Schur).
"""
from fractions import Fraction as Q
from itertools import permutations
from math import factorial, prod
import sys


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for first in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def conjugate(lam):
    return tuple(sum(1 for part in lam if part > col) for col in range(lam[0])) if lam else ()


def diagonal_hooks(lam):
    conj = conjugate(lam)
    return sorted((lam[i] + conj[i] - 2 * i - 1 for i in range(len(lam)) if lam[i] > i), reverse=True)


def syt_list(lam):
    """All standard tableaux, as tuples pos[k] = (row, col)."""
    cells_total = sum(lam)
    result = []

    def grow(rowlens, pos):
        k = len(pos)
        if k == cells_total:
            result.append(tuple(pos))
            return
        for row in range(len(lam)):
            col = rowlens[row]
            if col < lam[row] and (row == 0 or rowlens[row - 1] > col):
                rowlens[row] += 1
                pos.append((row, col))
                grow(rowlens, pos)
                pos.pop()
                rowlens[row] -= 1

    grow([0] * len(lam), [])
    return result


def content(tab, k):
    return tab[k][1] - tab[k][0]


class Seminormal:
    """Young's seminormal form: rho(s_k) e_U = (1/r) e_U + a e_{s_k U}, r = c_U(k+1) - c_U(k),
    a = 1 if r > 0 else 1 - 1/r^2 (product of the two off-diagonal entries = 1 - 1/r^2)."""

    def __init__(self, lam):
        self.lam = lam
        self.n = sum(lam)
        self.tabs = syt_list(lam)
        self.index = {tab: i for i, tab in enumerate(self.tabs)}
        self.dim = len(self.tabs)

    def swap_tab(self, tab, k):
        pos = list(tab)
        pos[k], pos[k + 1] = pos[k + 1], pos[k]
        new = tuple(pos)
        return new if new in self.index else None

    def apply_s(self, k, vec):
        """rho(s_k) applied to a coordinate vector (dict index -> Fraction)."""
        out = {}
        for idx, coef in vec.items():
            tab = self.tabs[idx]
            r = content(tab, k + 1) - content(tab, k)
            out[idx] = out.get(idx, 0) + coef * Q(1, r)
            other = self.swap_tab(tab, k)
            if other is not None:
                off = Q(1) if r > 0 else 1 - Q(1, r * r)
                j = self.index[other]
                out[j] = out.get(j, 0) + coef * off
        return {key: val for key, val in out.items() if val != 0}

    def apply_word(self, word, vec):
        """rho(s_{w0} s_{w1} ... ) vec: apply the rightmost letter first."""
        for k in reversed(word):
            vec = self.apply_s(k, vec)
        return vec


def word_of_perm(perm):
    """A word in adjacent transpositions s_k = (k k+1) with product (right to left) equal to perm (bubble sort)."""
    arr = list(perm)
    word = []
    n = len(arr)
    # perm = s_{w0} ... s_{wm}; we find it by sorting arr with adjacent swaps of positions.
    swaps = []
    for i in range(n):
        for j in range(n - 1 - i):
            if arr[j] > arr[j + 1]:
                arr[j], arr[j + 1] = arr[j + 1], arr[j]
                swaps.append(j)
    # arr = perm o s_{swaps[0]} o ... o s_{swaps[-1]} sorted => perm = s_last ... s_first  (as maps on positions)
    word = list(reversed(swaps))
    return word


def compose(p, q):
    """(p q)(i) = p(q(i)), right to left."""
    return tuple(p[q[i]] for i in range(len(q)))


def perm_of_word(word, n):
    result = tuple(range(n))
    for k in word:  # s_{w0} s_{w1} ...
        sk = list(range(n))
        sk[k], sk[k + 1] = sk[k + 1], sk[k]
        result = compose(result, tuple(sk))
    return result


def cycle_type_with_fixed(perm):
    seen = set()
    parts = []
    for start in range(len(perm)):
        if start in seen:
            continue
        length = 0
        cur = start
        while cur not in seen:
            seen.add(cur)
            cur = perm[cur]
            length += 1
        parts.append(length)
    return sorted(parts, reverse=True)


def rep_of_type(mu):
    """Permutation of cycle type mu: cycles on consecutive blocks (0 1 .. a-1)(a ..)..."""
    n = sum(mu)
    perm = list(range(n))
    start = 0
    for part in mu:
        for i in range(part):
            perm[start + i] = start + (i + 1) % part
        start += part
    return tuple(perm)


def class_size(mu):
    n = sum(mu)
    denom = 1
    for part in set(mu):
        mult = mu.count(part)
        denom *= part ** mult * factorial(mult)
    return factorial(n) // denom


def sign_of_type(mu):
    return (-1) ** sum(part - 1 for part in mu)


def check_coxeter_and_jm(sn):
    n = sn.n
    for idx in range(sn.dim):
        e = {idx: Q(1)}
        for k in range(n - 1):
            assert sn.apply_word([k, k], e) == e, "s_k^2"
            if k + 2 <= n - 1:
                assert sn.apply_word([k, k + 1] * 3, e) == e, "braid"
            for j in range(k + 2, n - 1):
                assert sn.apply_word([k, j], e) == sn.apply_word([j, k], e), "far commute"
        tab = sn.tabs[idx]
        for k in range(n):
            total = {}
            for i in range(k):
                word = word_of_perm(transposition(i, k, n))
                assert perm_of_word(word, n) == transposition(i, k, n)
                for key, val in sn.apply_word(word, e).items():
                    total[key] = total.get(key, 0) + val
            total = {key: val for key, val in total.items() if val != 0}
            expect = {idx: Q(content(tab, k))} if content(tab, k) != 0 else {}
            assert total == expect, ("J_k eigen", sn.lam, tab, k, total)


def transposition(i, j, n):
    perm = list(range(n))
    perm[i], perm[j] = perm[j], perm[i]
    return tuple(perm)


def solve_gamma(sn):
    """Monomial Gamma e_T = g_T e_{T^t}; fix g_{T0} = 1 and propagate through Gamma s_k = -s_k Gamma."""
    transpose = {tab: tuple((c, r) for (r, c) in tab) for tab in sn.tabs}
    gvals = {0: Q(1)}
    frontier = [0]
    while frontier:
        idx = frontier.pop()
        tab = sn.tabs[idx]
        for k in range(sn.n - 1):
            other = sn.swap_tab(tab, k)
            if other is None:
                continue
            j = sn.index[other]
            # coefficient of e_{other^t} in Gamma s_k e_T  vs  -s_k Gamma e_T:
            # Gamma s_k e_T = (1/r) g_T e_{T^t} + a_T g_{other} e_{other^t}
            # -s_k Gamma e_T = -g_T s_k e_{T^t} = -g_T [ (1/r') e_{T^t} + a_{T^t} e_{(T^t) swapped} ]
            r_t = content(tab, k + 1) - content(tab, k)
            a_t = Q(1) if r_t > 0 else 1 - Q(1, r_t * r_t)
            tt = transpose[tab]
            r_tt = content(tt, k + 1) - content(tt, k)
            a_tt = Q(1) if r_tt > 0 else 1 - Q(1, r_tt * r_tt)
            value = -gvals[idx] * a_tt / a_t
            if j in gvals:
                assert gvals[j] == value, "Gamma inconsistent"
            else:
                gvals[j] = value
                frontier.append(j)
    assert len(gvals) == sn.dim, "SYT graph not connected?"
    gamma_cols = {idx: {sn.index[transpose[sn.tabs[idx]]]: gvals[idx]} for idx in range(sn.dim)}
    return gamma_cols


def apply_gamma(gamma_cols, vec):
    out = {}
    for idx, coef in vec.items():
        for j, val in gamma_cols[idx].items():
            out[j] = out.get(j, 0) + coef * val
    return {key: val for key, val in out.items() if val != 0}


def verify_gamma(sn, gamma_cols):
    for idx in range(sn.dim):
        e = {idx: Q(1)}
        for k in range(sn.n - 1):
            left = apply_gamma(gamma_cols, sn.apply_s(k, e))
            right = {key: -val for key, val in sn.apply_s(k, apply_gamma(gamma_cols, e)).items()}
            assert left == right, "Gamma relation fails"
    sq = [apply_gamma(gamma_cols, apply_gamma(gamma_cols, {idx: Q(1)})) for idx in range(sn.dim)]
    cval = sq[0][0]
    assert all(sq[idx] == {idx: cval} for idx in range(sn.dim)), "Gamma^2 not scalar"
    trace_gamma = sum(gamma_cols[idx].get(idx, 0) for idx in range(sn.dim))
    return cval, trace_gamma


def trace_rho_times(sn, word, right_op=None):
    """tr(rho(word) * R), R = right_op (None = identity)."""
    total = Q(0)
    for idx in range(sn.dim):
        vec = {idx: Q(1)}
        if right_op is not None:
            vec = right_op(vec)
        vec = sn.apply_word(word, vec)
        total += vec.get(idx, 0)
    return total


def check_shape(lam):
    n = sum(lam)
    sn = Seminormal(lam)
    report = {"lam": lam, "N": n, "dim": sn.dim}
    check_coxeter_and_jm(sn)
    gamma_cols = solve_gamma(sn)
    cval, trace_gamma = verify_gamma(sn, gamma_cols)
    report["c=Gamma^2"] = cval
    report["trGamma"] = trace_gamma  # = sqrt(c)(dim V+ - dim V-) -> must be 0 (both dims d/2, nonzero)
    hooks = diagonal_hooks(lam)
    report["h(lam)"] = hooks
    dlen = len(hooks)
    eps = (-1) ** ((n - dlen) // 2)
    sum_even_chi_sq = Q(0)
    frob_rows = []
    for mu in partitions(n):
        mu = list(mu)
        perm = rep_of_type(mu)
        assert cycle_type_with_fixed(perm) == mu
        word = word_of_perm(perm)
        assert perm_of_word(word, n) == perm
        chi = trace_rho_times(sn, word)
        if sign_of_type(mu) == 1:
            sum_even_chi_sq += class_size(mu) * chi * chi
            psi = trace_rho_times(sn, word, lambda v: apply_gamma(gamma_cols, v))
            is_h = (mu == hooks)
            ok = (psi != 0) == is_h
            value_ok = None
            if is_h:
                # (chi+ - chi-)^2 = psi^2 / c must equal eps * prod h
                value_ok = (psi * psi / cval == eps * prod(hooks))
            frob_rows.append((tuple(mu), chi, psi, is_h, ok, value_ok))
        else:
            psi = trace_rho_times(sn, word, lambda v: apply_gamma(gamma_cols, v))
            assert psi == 0, "psi nonzero on odd class"
    end_dim = 2 * sum_even_chi_sq / factorial(n)
    report["dim End_AN"] = end_dim
    report["frob"] = frob_rows
    report["all_frob_ok"] = all(row[4] for row in frob_rows) and all(
        row[5] for row in frob_rows if row[3])
    return report


def main():
    shapes = [lam for n in range(0, 10) for lam in partitions(n) if conjugate(lam) == lam]
    print("self-conjugate shapes N<=9:", shapes)
    for lam in shapes:
        if sum(lam) < 2:
            sn = Seminormal(lam)
            print(f"lam={lam} N={sum(lam)}: dim={sn.dim} -> AltSplit impossible (needs two nonzero complementary "
                  f"subspaces); the guard 2 <= N is ESSENTIAL")
            continue
        rep = check_shape(lam)
        print(f"lam={lam} N={rep['N']} dim={rep['dim']} h={rep['h(lam)']} Gamma^2={rep['c=Gamma^2']} "
              f"trGamma={rep['trGamma']} dimEnd_AN={rep['dim End_AN']} frobOK={rep['all_frob_ok']}")
        for mu, chi, psi, is_h, ok, value_ok in rep["frob"]:
            flag = "  <-- h(lam)" if is_h else ""
            print(f"    even type {mu}: chi={chi} psi=tr(rho Gamma)={psi} ok={ok} valueOK={value_ok}{flag}")
        assert rep["all_frob_ok"] and rep["dim End_AN"] == 2 and rep["trGamma"] == 0
    print("ALL OK")


if __name__ == "__main__":
    main()
