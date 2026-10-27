#!/usr/bin/env python3
"""gen_fvectors.py - generate the Lean f-vector files of the 006 n=6 census.
Data per polytope: vertex supports (6-bit masks, ascending) and the closed vertex sets over vertex POSITIONS with dims
(longest chain down). Every fact is re-checked in Lean by `censusCheck` (FaceCount.lean); Python only proposes.
Run from the repository root (needs pycddlib 2.1.8): python3 scripts/census/gen_fvectors.py
"""
import sys

from check_census_plan import census_rel, rows_order, rows_chain, vertices, closed_family, dims_by_chains, fvector  # noqa

from pathlib import Path
OUT = str(Path(__file__).resolve().parents[2] / "HibiLi" / "Census")  # the repository's HibiLi/Census
STAMP = "20261026_1812"


def data(i, kind):
    rel = census_rel(i)
    rows = rows_order(rel) if kind == "O" else rows_chain(rel)
    verts = vertices(rows)
    fam = closed_family(rows, verts)
    low, up = dims_by_chains(fam)
    assert all(low[s] + up[s] == 6 for s in fam)
    pairs = sorted((s, low[s]) for s in fam)
    fv = [sum(1 for s in fam if low[s] == k) for k in range(7)]
    assert fv == fvector(rows)[0]
    return verts, pairs, fv


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def lean_pairs(ps):
    return "[" + ", ".join(f"({a}, {b})" for a, b in ps) + "]"


def ftable(fvs_o, fvs_c):
    def vec(fvs):
        return "![" + ",\n    ".join(lean_list(fv) for fv in fvs) + "]"
    return f'''/-
HibiLi/Census/FTable.lean — the f-vectors (f_0, ..., f_6) of the 32 census polytopes (CENSUS_n6.md columns f(O), f(C)).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
These lists are DATA only; FVectorsO.lean / FVectorsC.lean prove that they are the face numbers.
-/
import Mathlib

namespace HibiLi.Census

/-- `f_k` of the order polytope of census row `i + 1`, `k = 0..6`. -/
def censusFO : Fin 16 → List ℕ :=
  {vec(fvs_o)}

/-- `f_k` of the chain polytope of census row `i + 1`, `k = 0..6`. -/
def censusFC : Fin 16 → List ℕ :=
  {vec(fvs_c)}

end HibiLi.Census
'''


def fvectors(kind, items):
    poly = "orderPolytope" if kind == "O" else "chainPolytope"
    rows = "orderRows" if kind == "O" else "chainRows"
    table = "censusFO" if kind == "O" else "censusFC"
    name = "order" if kind == "O" else "chain"
    out = [f'''/-
HibiLi/Census/FVectors{kind}.lean — the face numbers of the 16 census {name} polytopes, kernel-checked.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
For each row: the vertex supports and the closed vertex sets with their dimensions (DATA), the computation
`censusCheck` (FaceCount.lean) run by the kernel, and the face numbers by `fNum_eq_of_check`.
-/
import HibiLi.Census.FaceCount
import HibiLi.Census.PosetRows
import HibiLi.Census.FTable

namespace HibiLi.Census
''']
    for i, (verts, pairs, fv) in enumerate(items):
        out.append(f'''
/-- Census row {i + 1}, {name} polytope: vertex supports. -/
def vs{kind}{i} : List ℕ := {lean_list(verts)}

/-- Census row {i + 1}, {name} polytope: closed vertex sets (bitmask over positions in `vs{kind}{i}`) and dimensions. -/
def fam{kind}{i} : List (ℕ × ℕ) := {lean_pairs(pairs)}

set_option maxRecDepth 100000 in
theorem check{kind}{i} : censusCheck 6 ({rows} (censusLe {i})) vs{kind}{i} fam{kind}{i} = true := by
  decide +kernel

theorem fNum{kind}{i} (k : ℕ) (hk : k ≤ 6) : fNum ({poly} (censusPoset {i})) k = ({table} {i}).getD k 0 := by
  have h := fNum_eq_of_check _ _ _ ({rows}_hull {i}) ({rows}_adim {i}) check{kind}{i} k
  rw [{poly}_census]
  refine h.trans ?_
  interval_cases k <;> decide +kernel
''')
    out.append("\nend HibiLi.Census\n")
    return "".join(out)


def main():
    items_o = [data(i, "O") for i in range(16)]
    items_c = [data(i, "C") for i in range(16)]
    with open(f"{OUT}/FTable.lean", "w") as fh:
        fh.write(ftable([it[2] for it in items_o], [it[2] for it in items_c]))
    with open(f"{OUT}/FVectorsO.lean", "w") as fh:
        fh.write(fvectors("O", items_o))
    with open(f"{OUT}/FVectorsC.lean", "w") as fh:
        fh.write(fvectors("C", items_c))
    print("written; max fam sizes O/C:", max(len(it[1]) for it in items_o), max(len(it[1]) for it in items_c))


if __name__ == "__main__":
    main()
