#!/usr/bin/env python3
"""check_census_plan.py - cross-check for the 006 n=6 census in Lean.
Run from the repository root (needs pycddlib 2.1.8): python3 scripts/census/check_census_plan.py
"""
import itertools
import sys

from census_n6 import X_REL, contains_x, face_polys, bound_poly  # noqa: E402
from fourier_identity_check import canon  # noqa: E402

BELOW = [[0, 1], [0, 1], [], [0], [], [0, 1], [0, 1, 2, 3, 4], [0, 1],
         [], [0], [], [0], [0, 1, 2], [], [0, 1, 2], []]
ABOVE = [[], [3], [3, 4], [3, 4], [0, 1, 2, 3, 4], [2, 3, 4], [], [3, 4],
         [], [], [3], [3], [3], [0, 2, 3, 4], [], [2, 3, 4]]
N = 6


def census_rel(i):
    return set(X_REL) | {(d, 5) for d in BELOW[i]} | {(5, u) for u in ABOVE[i]}


def le(rel, p, q):
    return p == q or (p, q) in rel


def rows_order(rel):
    """Order polytope rows as (coefficient dict, rhs)."""
    rows = [({p: -1}, 0) for p in range(N)] + [({p: 1}, 1) for p in range(N)]
    rows += [({p: 1, q: -1}, 0) for (p, q) in sorted(rel)]
    return rows


def chains(rel):
    out = []
    for size in range(1, N + 1):
        for sub in itertools.combinations(range(N), size):
            if all(le(rel, p, q) or le(rel, q, p) for p, q in itertools.combinations(sub, 2)):
                out.append(sub)
    return out


def rows_chain(rel):
    rows = [({p: -1}, 0) for p in range(N)]
    rows += [({p: 1 for p in k}, 1) for k in chains(rel)]
    return rows


def vertices(rows):
    """0/1 points satisfying all rows, as 6-bit masks."""
    out = []
    for mask in range(1 << N):
        if all(sum(c * (mask >> p & 1) for p, c in a.items()) <= b for a, b in rows):
            out.append(mask)
    return out


def tight_sets(rows, verts):
    """Row i -> bitmask over vertex positions where row i is tight."""
    out = []
    for a, b in rows:
        bits = 0
        for pos, mask in enumerate(verts):
            if sum(c * (mask >> p & 1) for p, c in a.items()) == b:
                bits |= 1 << pos
        out.append(bits)
    return out


def closed_family(rows, verts):
    full = (1 << len(verts)) - 1
    tights = tight_sets(rows, verts)
    fam = {full}
    frontier = [full]
    while frontier:
        new = []
        for s in frontier:
            for t in tights:
                u = s & t
                if u and u not in fam:
                    fam.add(u)
                    new.append(u)
        frontier = new
    # every member is closed: closure(s) = AND of tight sets containing s
    for s in fam:
        cl = full
        for t in tights:
            if s & t == s:
                cl &= t
        assert cl == s, "a generated set is not closed"
    return fam


def dims_by_chains(fam):
    """d_low = longest strict chain down to a singleton-closed set; d_up = longest chain up to the full set."""
    members = sorted(fam, key=lambda s: bin(s).count("1"))
    low, up = {}, {}
    for s in members:
        subs = [low[g] for g in members if g != s and g & s == g and g in low]
        low[s] = 1 + max(subs) if subs else 0
    for s in reversed(members):
        sups = [up[h] for h in members if h != s and h & s == s and h in up]
        up[s] = 1 + max(sups) if sups else 0
    return low, up


def fvector(rows):
    verts = vertices(rows)
    fam = closed_family(rows, verts)
    low, up = dims_by_chains(fam)
    for s in fam:
        assert low[s] + up[s] == N, f"not graded at {s}: {low[s]} + {up[s]}"
    fv = [0] * (N + 1)
    for s in fam:
        fv[low[s]] += 1
    return fv, len(verts), len(rows), len(fam)


def invariant(rel):
    return tuple(sorted((sum(1 for q in range(N) if (q, p) in rel), sum(1 for q in range(N) if (p, q) in rel))
                        for p in range(N)))


def main():
    canons = set()
    gap = bound_poly(N)
    attain = []
    for i in range(16):
        rel = census_rel(i)
        assert contains_x(N, rel)
        canons.add(canon(N, rel))
        f_o_cdd, f_c_cdd = face_polys(N, rel)
        f_o, nv_o, nr_o, nf_o = fvector(rows_order(rel))
        f_c, nv_c, nr_c, nf_c = fvector(rows_chain(rel))
        assert list(f_o) == list(f_o_cdd)[:N + 1], (i, f_o, f_o_cdd)
        assert list(f_c) == list(f_c_cdd)[:N + 1], (i, f_c, f_c_cdd)
        diff = [c - o for c, o in zip(f_c, f_o)]
        ok = diff == gap + [0] * (len(diff) - len(gap))
        if ok:
            attain.append(i + 1)
        print(f"row {i + 1:2d}: O {f_o} (verts {nv_o}, rows {nr_o}, faces {nf_o}) "
              f"C {f_c} (verts {nv_c}, rows {nr_c}, faces {nf_c}) diff {diff} {'ATTAINS' if ok else ''}")
    assert len(canons) == 16
    print("distinct classes:", len(canons), " attaining rows:", attain)
    invs = [invariant(census_rel(i)) for i in range(16)]
    print("(below,above)-degree invariant separates all 16:", len(set(invs)) == 16)


if __name__ == "__main__":
    main()
