#!/usr/bin/env python3
"""census_n6.py - exact census: which n-element posets containing X attain F_C - F_O = t^2 (1+t)^(n-3).

X = {a,b < c < g,h}. P contains X iff some c has an incomparable pair below it and an incomparable pair above it.
Face polynomials (all nonempty faces, t^dim) of O(P) = O_empty(P) and C(P) = O_P(P) come from
fourier_identity_check.py (exact rationals via pycddlib; imported, not edited).
Two independent routes to the posets containing X, cross-checked against each other:
  (1) all posets up to isomorphism, filtered by contains_x;
  (2) X plus one element f (down-set an ideal D of X, up-set a filter U of X, D < U elementwise), deduped.
Run with the venv python:  nice -n 19 venv/bin/python census_n6.py N   |   --test
"""
import itertools
import sys
import time

from fourier_identity_check import (canon, chain_order_ineqs, face_vector, order_ideals, padd, pneg,
                                    poset_classes, ptrim)

X_LABELS = "abcgh"
X_REL = {(0, 2), (1, 2), (2, 3), (2, 4), (0, 3), (0, 4), (1, 3), (1, 4)}   # a=0 b=1 c=2 g=3 h=4


# ---------------------------------------------------------------- poset helpers
def comparable(rel, p, q):
    return (p, q) in rel or (q, p) in rel


def has_incomparable_pair(rel, elems):
    return any(not comparable(rel, p, q) for p, q in itertools.combinations(elems, 2))


def contains_x(n, rel):
    """Induced copy of X: a,b < c < g,h with a||b and g||h (the other relations follow by transitivity)."""
    for mid in range(n):
        below = [p for p in range(n) if (p, mid) in rel]
        above = [r for r in range(n) if (mid, r) in rel]
        if has_incomparable_pair(rel, below) and has_incomparable_pair(rel, above):
            return True
    return False


def covers(rel):
    return sorted((p, r) for p, r in rel if not any((p, k) in rel and (k, r) in rel for k, _ in rel))


def minimal_elems(n, rel):
    return [q for q in range(n) if not any(r == q for _, r in rel)]


def maximal_elems(n, rel):
    return [p for p in range(n) if not any(q == p for q, _ in rel)]


def antichain_count(n, rel):
    return sum(1 for size in range(n + 1) for sub in itertools.combinations(range(n), size)
               if not any(comparable(rel, p, q) for p, q in itertools.combinations(sub, 2)))


def maximal_chain_count(n, rel):
    """Maximal chains = paths in the cover graph from a minimal to a maximal element."""
    cov = covers(rel)
    memo = {}

    def from_elem(p):
        if p not in memo:
            ups = [r for q, r in cov if q == p]
            memo[p] = 1 if not ups else sum(from_elem(r) for r in ups)
        return memo[p]
    return sum(from_elem(p) for p in minimal_elems(n, rel))


def with_new_bottom(n, rel):
    """P plus a new element n below everything (the step P_m -> P_{m+1} of Prop. prop:sharp)."""
    return set(rel) | {(n, p) for p in range(n)}


# ---------------------------------------------------------------- route (2): one-element extensions of X
def filters(n, rel):
    for mask in range(1 << n):
        up = frozenset(i for i in range(n) if mask >> i & 1)
        if all(r in up for (p, r) in rel if p in up):
            yield up


def x_extensions():
    """Every 6-element poset containing X is X plus one element f = 5; f's strict down-set D must be an order ideal,
    its strict up-set U a filter, disjoint, with every element of D below every element of U."""
    out = []
    for down in order_ideals(5, X_REL):
        for up in filters(5, X_REL):
            if not down & up and all((d, u) in X_REL for d in down for u in up):
                out.append(X_REL | {(d, 5) for d in down} | {(5, u) for u in up})
    return out


def classes_of(n, rels):
    seen = {}
    for rel in rels:
        seen.setdefault(canon(n, rel), rel)
    return seen


# ---------------------------------------------------------------- face polynomials
def face_polys(n, rel):
    """(F_O, F_C) as coefficient lists: O(P) = O_empty(P), C(P) = O_P(P)."""
    f_o = face_vector(chain_order_ineqs(list(range(n)), rel, frozenset()), n)
    f_c = face_vector(chain_order_ineqs(list(range(n)), rel, frozenset(range(n))), n)
    return f_o, f_c


def bound_poly(n):
    """t^2 (1+t)^(n-3)."""
    return [0, 0] + [len(list(itertools.combinations(range(n - 3), k))) for k in range(n - 2)]


def sanity_check(n, rel, f_o, f_c):
    """Classical counts, independent of cdd: vertices of O = order ideals, of C = antichains (equal numbers);
    facets of O = covers + minimal + maximal elements; facets of C = n + maximal chains."""
    n_ideals = sum(1 for _ in order_ideals(n, rel))
    assert f_o[0] == n_ideals == antichain_count(n, rel) == f_c[0], (rel, f_o, f_c)
    assert f_o[n - 1] == len(covers(rel)) + len(minimal_elems(n, rel)) + len(maximal_elems(n, rel)), (rel, f_o)
    assert f_c[n - 1] == n + maximal_chain_count(n, rel), (rel, f_c)


def poly_str(coeffs):
    terms = [(k, c) for k, c in enumerate(coeffs) if c]
    if not terms:
        return "0"
    out = []
    for k, c in terms:
        mono = "" if k == 0 else ("t" if k == 1 else f"t^{k}")
        coef = str(c) if (abs(c) != 1 or k == 0) else ("-" if c < 0 else "")
        out.append(f"{coef}{mono}")
    return " + ".join(out).replace("+ -", "- ")


# ---------------------------------------------------------------- the census
def census_records(n):
    """One record per isomorphism class of n-element posets containing X."""
    all_classes = poset_classes(n)
    with_x = [rel for rel in all_classes if contains_x(n, rel)]
    target, records = bound_poly(n), []
    p_n = X_REL
    for m in range(5, n):
        p_n = with_new_bottom(m, p_n)
    p_n_canon = canon(n, p_n)
    for rel in with_x:
        f_o, f_c = face_polys(n, rel)
        sanity_check(n, rel, f_o, f_c)
        diff = ptrim(padd(f_c, pneg(f_o)))
        records.append(dict(rel=rel, canon=canon(n, rel), f_o=f_o, f_c=f_c, diff=diff,
                            attains=diff == ptrim(target), is_pn=canon(n, rel) == p_n_canon))
    return len(all_classes), records


def label_records_by_x(records):
    """n = 6 only: attach an X-labelled representative (a,b,c,g,h + extra f) from route (2) to each record."""
    ext = classes_of(6, x_extensions())
    assert set(ext) == {rec['canon'] for rec in records}, "route (1) and route (2) disagree on posets containing X"
    for rec in records:
        rec['xrep'] = ext[rec['canon']]
    return len(ext)


def describe_x_rep(rel):
    names = X_LABELS + "f"
    cov = ", ".join(f"{names[p]}<{names[r]}" for p, r in covers(rel))
    down = "".join(names[p] for p in range(5) if (p, 5) in rel) or "-"
    up = "".join(names[r] for r in range(5) if (5, r) in rel) or "-"
    return cov, down, up


def main_census(n):
    start = time.time()
    n_classes, records = census_records(n)
    n_ext = label_records_by_x(records) if n == 6 else None
    n_attain = sum(rec['attains'] for rec in records)
    print(f"n={n}: posets up to isomorphism = {n_classes}")
    print(f"n={n}: containing X = {len(records)}" + (f"  (route 2, X + one element: {n_ext})" if n_ext else ""))
    print(f"n={n}: attaining F_C - F_O = {poly_str(bound_poly(n))}: {n_attain}")
    print(f"n={n}: P_{n} attains: {[rec['attains'] for rec in records if rec['is_pn']]}")
    print_table(n, records)
    print(f"runtime {time.time() - start:.1f}s")
    return records


def print_table(n, records):
    records.sort(key=lambda rec: (not rec['attains'], rec['diff']))
    print("| # | covers (X-labels a,b<c<g,h; extra f) | f > | f < | F_C - F_O | attains | P_n | f(O) | f(C) |")
    print("|---|---|---|---|---|---|---|---|---|")
    for idx, rec in enumerate(records, 1):
        cov, down, up = describe_x_rep(rec['xrep']) if 'xrep' in rec else (str(covers(rec['rel'])), "", "")
        print(f"| {idx} | {cov} | {down} | {up} | {poly_str(rec['diff'])} | {'YES' if rec['attains'] else 'no'} "
              f"| {'P_' + str(n) if rec['is_pn'] else ''} | {rec['f_o']} | {rec['f_c']} |")


# ---------------------------------------------------------------- self tests
def run_tests():
    chain = {(0, 1)}
    f_o, f_c = face_polys(2, chain)
    assert f_o == f_c == [3, 3, 1], (f_o, f_c)                       # 3 + 3t + t^2 for both
    f_o, f_c = face_polys(5, X_REL)
    assert ptrim(padd(f_c, pneg(f_o))) == [0, 0, 1, 2, 1], (f_o, f_c)  # t^2 + 2t^3 + t^4
    sanity_check(5, X_REL, f_o, f_c)
    assert contains_x(5, X_REL)
    assert bound_poly(5) == [0, 0, 1, 2, 1] and bound_poly(6) == [0, 0, 1, 3, 3, 1]
    assert [len(poset_classes(k)) for k in range(1, 6)] == [1, 2, 5, 16, 63]   # OEIS A000112
    assert not any(contains_x(4, rel) for rel in poset_classes(4))
    assert sum(contains_x(5, rel) for rel in poset_classes(5)) == 1           # only X itself
    assert maximal_chain_count(5, X_REL) == 4 and antichain_count(5, X_REL) == 8
    assert canon(6, with_new_bottom(5, X_REL)) != canon(6, X_REL | {(p, 5) for p in range(5)})  # P_6 != X + top
    print("ALL TESTS PASS")


def main():
    if sys.argv[1:] == ['--test']:
        run_tests()
        return
    if len(sys.argv) != 2:
        sys.exit("usage: census_n6.py N | --test")
    main_census(int(sys.argv[1]))


if __name__ == "__main__":
    main()
