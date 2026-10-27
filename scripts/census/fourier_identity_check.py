#!/usr/bin/env python3
"""fourier_identity_check.py - exact check of Fourier's Lemma 4.1 (arXiv:2609.23629v1) on all small posets.

For every poset P (up to isomorphism), order ideal I, and q minimal in P \\ I, checks
    F_{O_{I+q}(P)} - F_{O_I(P)} = F_B + F_R - F_S - F_T        (face polynomials, all nonempty faces)
with B = O_I(P \\ q), and F_S, F_T, F_R read off lifted polytopes over B (no subdivision is built):
    Gamma_S = {L(u) <= z <= M},  Gamma_T = {-M <= z <= U(u)},  Gamma_R = {-M <= z <= U(u) - L(u)},
    F_X = F_{Gamma_X} - (1 + t) F_B.
Also checks Prop 3.1 (O_I(P), O_{I+q}(P) equal the fibre polytopes over B) by comparing exact vertex sets.
Run with the venv python (has pycddlib):  nice -n 19 venv/bin/python fourier_identity_check.py NMAX   |   --test
"""
import itertools
import sys
import time
from fractions import Fraction

import cdd

LIFT_M = Fraction(3)   # any constant > 1 = max of L and U on B


# ---------------------------------------------------------------- posets
def posets_labeled(n):
    """All naturally labelled posets on 0..n-1 (relation i<j only for i<j index), as strict-relation sets."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        rel = {pairs[k] for k in range(len(pairs)) if mask >> k & 1}
        if all((i, l) in rel for (i, j) in rel for (k, l) in rel if j == k):
            yield rel


def canon(n, rel):
    return min(tuple(sorted((perm[i], perm[j]) for i, j in rel)) for perm in itertools.permutations(range(n)))


def poset_classes(n):
    """One representative strict-relation set per isomorphism class (every poset has a natural labelling)."""
    seen = {}
    for rel in posets_labeled(n):
        seen.setdefault(canon(n, rel), rel)
    return list(seen.values())


def order_ideals(n, rel):
    for mask in range(1 << n):
        ideal = frozenset(i for i in range(n) if mask >> i & 1)
        if all(p in ideal for (p, r) in rel if r in ideal):
            yield ideal


def minimal_outside(n, rel, ideal):
    return [q for q in range(n) if q not in ideal and all(p in ideal for (p, r) in rel if r == q)]


def chains(rel, subset):
    """Nonempty chains contained in subset."""
    elems = sorted(subset)
    out = []
    for size in range(1, len(elems) + 1):
        for combo in itertools.combinations(elems, size):
            if all((combo[a], combo[b]) in rel or (combo[b], combo[a]) in rel
                   for a in range(size) for b in range(a + 1, size)):
                out.append(combo)
    return out


# ---------------------------------------------------------------- inequality systems (coeffs . x <= bound)
def chain_order_ineqs(elems, rel, ideal):
    """The five inequality families of O_I(P) on the element list elems (coordinate k <-> elems[k])."""
    pos = {e: k for k, e in enumerate(elems)}
    order_part = [r for r in elems if r not in ideal]

    def vec(terms):
        out = [0] * len(elems)
        for e, c in terms:
            out[pos[e]] += c
        return out
    ineqs = [(vec([(p, -1)]), 0) for p in elems if p in ideal]
    ineqs += [(vec([(r, -1)]), 0) for r in order_part] + [(vec([(r, 1)]), 1) for r in order_part]
    ineqs += [(vec([(r, 1), (r2, -1)]), 0) for r in order_part for r2 in order_part if (r, r2) in rel]
    for chain in chains(rel, [e for e in elems if e in ideal]):
        ineqs.append((vec([(p, 1) for p in chain]), 1))
        for r in order_part:
            if all((p, r) in rel for p in chain):
                ineqs.append((vec([(p, 1) for p in chain] + [(r, -1)]), 0))
    return ineqs


def lower_terms(rel, ideal, q, base_elems):
    """Coefficient vectors (in base coordinates) of the chain sums l_K, K a chain in I below q; empty chain included."""
    pos = {e: k for k, e in enumerate(base_elems)}
    below = [p for p in ideal if (p, q) in rel]
    vecs = [[0] * len(base_elems)]
    for chain in chains(rel, below):
        vec = [0] * len(base_elems)
        for p in chain:
            vec[pos[p]] = 1
        vecs.append(vec)
    return vecs


def upper_terms(rel, q, base_elems):
    """(coefficient vector, constant) of the affine terms y_r (r > q) and the constant 1 whose minimum is U."""
    pos = {e: k for k, e in enumerate(base_elems)}
    terms = [([0] * len(base_elems), 1)]
    for r in base_elems:
        if (q, r) in rel:
            vec = [0] * len(base_elems)
            vec[pos[r]] = 1
            terms.append((vec, 0))
    return terms


def lifted(base_ineqs, extra):
    """Base inequalities with z-coefficient 0, plus extra inequalities already in (u, z) coordinates."""
    return [(coeffs + [0], bound) for coeffs, bound in base_ineqs] + extra


def gamma_S(base_ineqs, lows):
    return lifted(base_ineqs, [([0] * len(lows[0]) + [1], LIFT_M)] + [(lv + [-1], 0) for lv in lows])


def gamma_T(base_ineqs, ups):
    nb = len(ups[0][0])
    return lifted(base_ineqs, [([0] * nb + [-1], LIFT_M)] + [([-c for c in uv] + [1], uc) for uv, uc in ups])


def gamma_R(base_ineqs, lows, ups):
    nb = len(ups[0][0])
    extra = [([0] * nb + [-1], LIFT_M)]
    extra += [([a - c for a, c in zip(lv, uv)] + [1], uc) for lv in lows for uv, uc in ups]
    return lifted(base_ineqs, extra)


def fibre_O(base_ineqs, lows, ups):
    """Prop 3.1: {(u,z): L(u) <= z <= U(u)}."""
    nb = len(ups[0][0])
    return lifted(base_ineqs, [(lv + [-1], 0) for lv in lows] + [([-c for c in uv] + [1], uc) for uv, uc in ups])


def fibre_C(base_ineqs, lows, ups):
    """Prop 3.1: {(u,z): 0 <= z <= U(u) - L(u)}."""
    nb = len(ups[0][0])
    extra = [([0] * nb + [-1], 0)]
    extra += [([a - c for a, c in zip(lv, uv)] + [1], uc) for lv in lows for uv, uc in ups]
    return lifted(base_ineqs, extra)


# ---------------------------------------------------------------- exact polytope combinatorics
def rank(rows):
    mat = [[Fraction(x) for x in r] for r in rows]
    rk, ncol = 0, (len(mat[0]) if mat else 0)
    for col in range(ncol):
        piv = next((i for i in range(rk, len(mat)) if mat[i][col] != 0), None)
        if piv is None:
            continue
        mat[rk], mat[piv] = mat[piv], mat[rk]
        for i in range(len(mat)):
            if i != rk and mat[i][col] != 0:
                fac = mat[i][col] / mat[rk][col]
                mat[i] = [a - fac * b for a, b in zip(mat[i], mat[rk])]
        rk += 1
    return rk


def vertices(ineqs):
    """Exact vertex list of the bounded polytope {coeffs . x <= bound} via cddlib (rational arithmetic)."""
    mat = cdd.Matrix([[bound] + [-c for c in coeffs] for coeffs, bound in ineqs], number_type='fraction')
    mat.rep_type = cdd.RepType.INEQUALITY
    gens = cdd.Polyhedron(mat).get_generators()
    assert not gens.lin_set, "polyhedron has a lineality space"
    verts = set()
    for row in gens:
        assert row[0] == 1, ("unbounded polyhedron", row)
        verts.add(tuple(Fraction(x) for x in row[1:]))
    return sorted(verts)


def facet_masks(ineqs, verts):
    """Facets = inclusion-maximal proper nonempty tight sets of the defining inequalities (bitmasks over verts)."""
    full = (1 << len(verts)) - 1
    tight = set()
    for coeffs, bound in ineqs:
        mask = 0
        for i, v in enumerate(verts):
            val = sum(c * x for c, x in zip(coeffs, v))
            assert val <= bound, "cdd vertex violates an inequality"
            if val == bound:
                mask |= 1 << i
        if mask and mask != full:
            tight.add(mask)
    return [m for m in tight if not any(m != o and m & o == m for o in tight)]


def face_vector(ineqs, dim):
    """f-vector (f_0..f_dim, polytope itself included) of the full-dimensional polytope {coeffs . x <= bound}."""
    if dim == 0:
        return [1]
    counts = [len(level) for level in face_lattice(ineqs, dim)[1]]
    assert sum((-1) ** k * c for k, c in enumerate(counts)) == 1, ("Euler relation fails", counts)
    return counts


def face_lattice(ineqs, dim):
    """(vertices, levels): levels[k] = set of k-faces as vertex bitmasks, k = 0..dim (dim >= 1, full-dimensional)."""
    verts = vertices(ineqs)
    assert rank([[a - b for a, b in zip(v, verts[0])] for v in verts[1:]]) == dim, "not full-dimensional"
    facets = facet_masks(ineqs, verts)
    levels = [set(facets)]
    while len(levels) < dim:
        levels.insert(0, next_level(levels[0], facets))
    assert levels[0] == {1 << i for i in range(len(verts))}, "0-faces are not exactly the cdd vertices"
    return verts, levels + [{(1 << len(verts)) - 1}]


def next_level(level, facets):
    """Faces one dimension lower: the facets of each face G are the inclusion-maximal G & F, F a facet not containing G."""
    out = set()
    for face in level:
        cands = {face & fm for fm in facets if face & fm and face & fm != face}
        out |= {cc for cc in cands if not any(cc != dd and cc & dd == cc for dd in cands)}
    return out


# ---------------------------------------------------------------- polynomial helpers (coefficient lists)
def padd(*polys):
    out = [0] * max(len(p) for p in polys)
    for p in polys:
        for k, c in enumerate(p):
            out[k] += c
    return out


def pneg(poly):
    return [-c for c in poly]


def ptrim(poly):
    out = list(poly)
    while out and out[-1] == 0:
        out.pop()
    return out


def one_plus_t(poly):
    return padd(poly + [0], [0] + poly)


def subdivision_poly(gamma_f, base_f):
    """F_X = F_{Gamma_X} - (1 + t) F_B."""
    return ptrim(padd(gamma_f, pneg(one_plus_t(base_f))))


# ---------------------------------------------------------------- the check
def check_triple(n, rel, ideal, q, f_O):
    """Returns (ok, record) for one (P, I, q)."""
    base_elems = [e for e in range(n) if e != q]
    base = chain_order_ineqs(base_elems, rel, ideal)
    lows, ups = lower_terms(rel, ideal, q, base_elems), upper_terms(rel, q, base_elems)
    f_B = face_vector(base, n - 1)
    f_S = subdivision_poly(face_vector(gamma_S(base, lows), n), f_B)
    f_T = subdivision_poly(face_vector(gamma_T(base, ups), n), f_B)
    f_R = subdivision_poly(face_vector(gamma_R(base, lows, ups), n), f_B)
    lhs = ptrim(padd(f_O[ideal | {q}], pneg(f_O[ideal])))
    rhs = ptrim(padd(f_B, f_R, pneg(f_S), pneg(f_T)))
    prop31 = fibre_vertices_match(n, rel, ideal, q, base, lows, ups)
    euler = all(sum((-1) ** k * c for k, c in enumerate(f)) == 1 and min(f) >= 0 for f in (f_S, f_T, f_R))
    record = dict(rel=sorted(rel), ideal=sorted(ideal), q=q, lhs=lhs, rhs=rhs, f_B=f_B, f_S=f_S, f_T=f_T, f_R=f_R,
                  f_O_I=f_O[ideal], f_O_Iq=f_O[ideal | {q}], prop31=prop31, subdiv_euler=euler)
    return lhs == rhs and prop31 and euler, record


def fibre_vertices_match(n, rel, ideal, q, base, lows, ups):
    """Prop 3.1 check: vertex sets of O_I(P), O_{I+q}(P) (q-coordinate moved last) equal those of the fibre polytopes."""
    order = [e for e in range(n) if e != q] + [q]
    for ide, fibre in ((ideal, fibre_O(base, lows, ups)), (ideal | {q}, fibre_C(base, lows, ups))):
        if vertices(chain_order_ineqs(order, rel, ide)) != vertices(fibre):
            return False
    return True


def graph_cells(ineqs, dim, z_away):
    """Cells of the subdivision read off a lifted polytope: faces with no vertex at z = z_away, projected to u."""
    verts, levels = face_lattice(ineqs, dim)
    cells = set()
    for level in levels:
        for mask in level:
            pts = [verts[i] for i in range(len(verts)) if mask >> i & 1]
            if all(pt[-1] != z_away for pt in pts):
                cells.add(frozenset(pt[:-1] for pt in pts))
    return cells


def hrep(cell):
    """cdd H-representation (with equality rows in lin_set) of conv(cell)."""
    mat = cdd.Matrix([[1] + list(pt) for pt in cell], number_type='fraction')
    mat.rep_type = cdd.RepType.GENERATOR
    return cdd.Polyhedron(mat).get_inequalities()


def intersection_vertices(h_one, h_two):
    """Exact vertex set of the intersection of two H-represented polytopes (empty set if disjoint)."""
    mat = cdd.Matrix([list(h_one[i]) for i in range(h_one.row_size)], number_type='fraction')
    mat.lin_set = h_one.lin_set
    mat.rep_type = cdd.RepType.INEQUALITY
    for i in range(h_two.row_size):
        mat.extend([list(h_two[i])], linear=i in h_two.lin_set)
    gens = cdd.Polyhedron(mat).get_generators()
    assert all(row[0] == 1 for row in gens) and not gens.lin_set
    return frozenset(tuple(Fraction(x) for x in row[1:]) for row in gens)


def check_refinement(n, rel, ideal, q):
    """Step 3 check: the common refinement S v T (all nonempty intersections of a cell of S with a cell of T)
    equals, cell for cell (exact vertex sets), the affinity subdivision of U - L read off Gamma_R."""
    base_elems = [e for e in range(n) if e != q]
    base = chain_order_ineqs(base_elems, rel, ideal)
    lows, ups = lower_terms(rel, ideal, q, base_elems), upper_terms(rel, q, base_elems)
    cells_S = graph_cells(gamma_S(base, lows), n, LIFT_M)
    cells_T = graph_cells(gamma_T(base, ups), n, -LIFT_M)
    cells_R = graph_cells(gamma_R(base, lows, ups), n, -LIFT_M)
    h_T = [hrep(cell) for cell in cells_T]
    meet = set()
    for cell in cells_S:
        h_cell = hrep(cell)
        meet |= {vs for vs in (intersection_vertices(h_cell, ht) for ht in h_T) if vs}
    return meet == cells_R, (len(cells_S), len(cells_T), len(cells_R), len(meet))


def main_refine(nmax):
    """Run check_refinement on every triple where both S and T are nontrivial (else S v T is S or T trivially)."""
    nfail = 0
    for n in range(2, nmax + 1):
        start, nchecked = time.time(), 0
        for rel in poset_classes(n):
            for ok, rec in check_poset(n, rel):
                if rec['f_S'] != rec['f_B'] and rec['f_T'] != rec['f_B']:
                    nchecked += 1
                    same, sizes = check_refinement(n, rel, frozenset(rec['ideal']), rec['q'])
                    nfail += not same
                    print(f"  refine {'OK' if same else 'FAIL'} P={rec['rel']} I={rec['ideal']} q={rec['q']} "
                          f"#cells S,T,R,SvT={sizes}", flush=True)
        print(f"n={n}: S v T = R checked on {nchecked} triples, {time.time() - start:.1f}s", flush=True)
    print("REFINEMENT FAILURES:", nfail)
    return nfail


def check_poset(n, rel):
    f_O = {ideal: face_vector(chain_order_ineqs(list(range(n)), rel, ideal), n) for ideal in order_ideals(n, rel)}
    results = []
    for ideal in f_O:
        for q in minimal_outside(n, rel, ideal):
            results.append(check_triple(n, rel, ideal, q, f_O))
    return results


def main_check(nmax):
    total_fail, first_fail = 0, None
    for n in range(1, nmax + 1):
        start = time.time()
        classes = poset_classes(n)
        ntriples = nfail = 0
        for rel in classes:
            for ok, rec in check_poset(n, rel):
                ntriples += 1
                if not ok:
                    nfail += 1
                    first_fail = first_fail or rec
                    print("FAIL", rec, flush=True)
        total_fail += nfail
        print(f"n={n}: {len(classes)} posets, {ntriples} (P,I,q) triples, {nfail} failures, "
              f"{time.time() - start:.1f}s", flush=True)
    print("TOTAL FAILURES:", total_fail)
    if first_fail:
        print("FIRST FAILURE:", first_fail)
    return total_fail


# ---------------------------------------------------------------- self tests
def run_tests():
    chain = {(0, 1)}
    assert face_vector(chain_order_ineqs([0, 1], chain, frozenset()), 2) == [3, 3, 1]
    assert face_vector(chain_order_ineqs([0, 1], chain, frozenset({0, 1})), 2) == [3, 3, 1]
    # X poset: a,b < c < g,h  (a=0, b=1, c=2, g=3, h=4)
    rel_x = {(0, 2), (1, 2), (2, 3), (2, 4), (0, 3), (0, 4), (1, 3), (1, 4)}
    assert face_vector(chain_order_ineqs(list(range(5)), rel_x, frozenset()), 5) == [8, 24, 34, 24, 8, 1]
    assert face_vector(chain_order_ineqs(list(range(5)), rel_x, frozenset(range(5))), 5) == [8, 24, 35, 26, 9, 1]
    test_hand_chain()
    test_hand_wedge()
    test_cdd_against_01_points(4)
    print("ALL TESTS PASS")


def test_hand_chain():
    """a<b, I={a}, q=b: B=[0,1], L=x_a, U=1; S, T, R trivial => F_S=F_T=F_R=2+t; both sides 0."""
    ok, rec = check_triple(2, {(0, 1)}, frozenset({0}), 1,
                           {frozenset({0}): [3, 3, 1], frozenset({0, 1}): [3, 3, 1]})
    assert ok and rec['f_S'] == rec['f_T'] == rec['f_R'] == [2, 1] and rec['lhs'] == rec['rhs'] == [], rec


def test_hand_wedge():
    """a,b < q, I={a,b}: B=[0,1]^2, L=max(x_a,x_b) splits B along the diagonal => F_S = 4+5t+2t^2,
    Gamma_S = 8 vertices, 13 edges, 7 facets (2 lower, 1 top, 4 sides); U=1 => F_T = 4+4t+t^2; R = S."""
    rel = {(0, 2), (1, 2)}
    base = chain_order_ineqs([0, 1], rel, frozenset({0, 1}))
    lows = lower_terms(rel, frozenset({0, 1}), 2, [0, 1])
    assert face_vector(gamma_S(base, lows), 3) == [8, 13, 7, 1]
    f_O = {ide: face_vector(chain_order_ineqs([0, 1, 2], rel, ide), 3) for ide in order_ideals(3, rel)}
    ok, rec = check_triple(3, rel, frozenset({0, 1}), 2, f_O)
    assert ok and rec['f_S'] == [4, 5, 2] and rec['f_T'] == [4, 4, 1] and rec['f_R'] == [4, 5, 2], rec
    assert rec['f_O_I'] == rec['f_O_Iq'] == [5, 8, 5, 1], rec
    assert check_refinement(3, rel, frozenset({0, 1}), 2) == (True, (11, 9, 11, 11))


def test_cdd_against_01_points(nmax):
    """O_I(P) has 0/1 vertices: cdd's vertex set must equal the 0/1 points that are vertices (tight rank n)."""
    for n in range(1, nmax + 1):
        for rel in poset_classes(n):
            for ideal in order_ideals(n, rel):
                ineqs = chain_order_ineqs(list(range(n)), rel, ideal)
                pts = [p for p in itertools.product((0, 1), repeat=n)
                       if all(sum(a * x for a, x in zip(c, p)) <= b for c, b in ineqs)]
                v01 = sorted(tuple(Fraction(x) for x in p) for p in pts
                             if rank([c for c, b in ineqs if sum(a * x for a, x in zip(c, p)) == b]) == n)
                assert vertices(ineqs) == v01, (rel, ideal)


def main():
    if sys.argv[1:] == ['--test']:
        run_tests()
        return
    if len(sys.argv) == 3 and sys.argv[1] == '--refine':
        sys.exit(1 if main_refine(int(sys.argv[2])) else 0)
    if len(sys.argv) != 2:
        sys.exit("usage: fourier_identity_check.py NMAX | --refine NMAX | --test")
    start = time.time()
    fails = main_check(int(sys.argv[1]))
    print(f"total runtime {time.time() - start:.1f}s")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
