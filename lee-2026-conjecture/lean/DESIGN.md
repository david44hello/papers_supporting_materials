# LeeDiamLean — design
## version 0.91 - 20261028_1318 — paper v1.50 (statements unchanged).
## version 0.81 - 20261028_1254 — paper v1.40 (statements unchanged).
## version 0.71 - 20261028_1229 — paper v1.30 (+ row def_6_1_rank_lt).
## version 0.61 - 20261028_1204 — paper v1.20 (statements unchanged).

Paper: Dave Goel, "The Lee (2026) conjecture on the diameters of order and chain polytopes fails in both directions",
short version v1.50 (statements final): P4_short_v1.50.tex (main), sec_chain.tex (Section 4), sec_reverse.tex
(Sections 5-6). Rules: every claim of the paper is PROVED; results of OTHER papers may be cited statements in
LeeDiam/Cited/ (true, no stronger than the source). The source policy of scripts/check.sh holds (no proof holes,
no banned constructs, axioms only in LeeDiam/Cited/).

## 1. Trust surface (LeeDiam/Defs, LeeDiam/Cited)
1. Polytopes (the paper's conventions): `orderPolytope P = {x ∈ [0,1]^P : p ≤ q → x q ≤ x p}` (vertices = ideals,
   as the paper says; the footnote's x ↦ 1-x to Stanley's filter version is a claim that is proved),
   `chainPolytope P` = `{x ≥ 0 : Σ_{p ∈ K} x_p ≤ 1 for every chain K}`. `IsFace` = nonempty exposed face.
2. Graph of a polytope: vertices = points v with {v} a face; u ~ v iff u ≠ v and `segment ℝ u v` is a face.
   Diameters are stated with `ediam` (⊤ if disconnected), never `diam` alone (diam = 0 when disconnected would make
   an upper bound empty).
3. Combinatorial side (proof tool, not trust surface): `idealGraph P` (ideals; nested + connected difference) and
   `antichainGraph P` (antichains; connected difference); "connected" = nonempty + comparability graph connected.
4. Link: vertices of O(P) = indicator vectors of ideals, of C(P) = of antichains (PROVED); edges = Theorem 2.1 (CITED,
   two statements: [IT95]/[HL19] for ideals, [Chv75] via [Sta86] for antichains); one proved graph isomorphism moves
   every distance statement from the combinatorial graphs to the polytope graphs.

## 2. Claims
One Lean theorem per claim of the paper, numbered results and in-text claims, in LeeDiam/Paper/Statements.lean
(Sections 1-7). The proofs are in the other modules (LeeDiam/Bridge, LeeDiam/Sec1 ... LeeDiam/Sec7). What is not
formalized (results of other papers, context sentences) and every proof whose Lean route differs from the paper's are
listed in AUDIT_NOTES.md.

## 3. Checks
`scripts/check.sh --final <core>`: build, source policy, audit (`scripts/audit.py`: every row PROVED or
PROVED-FROM-CITED, OPEN 0, VIOLATION 0; AUDIT.md), statement-type diff (`scripts/stmt_diff.py`: every `X_proved`
has the type of the claim `X`). Then a kernel replay of the frozen tree.

## 4. Decisions
- D1 Vendor: the polytope files of a companion formalization are copied to LeeDiam/Vendor/HibiLi (import paths and
  lint changed only): IsFace, chainPolytope, setVector, the 0/1 vertex lemmas.
- D2 The paper's O(P) = {x ∈ [0,1]^P : p ≤ q → x_q ≤ x_p} (Lee's convention, ideal vertices); the vertex
  description "vertices of O(P) = indicators of ideals" is PROVED from the vendored lemmas on the dual order.
- D3 Graph of a polytope: vertices = points v with {v} a face; u ~ v iff u ≠ v and segment u v is a face. ediam.
- D4 Cited: TWO statements, `Cited.adjacency_ideals` ([IT95], [HL19]) and `Cited.adjacency_antichains` ([Chv75] +
  [Sta86]); together they are Theorem 2.1 of the paper (= [Lee26, Theorem 4]); `Cited.lee26_thm4` is the theorem
  that combines them.
- D5 B_k on Fin k × Fin 3 and P_n on an inductive type; both orders = reflexive-transitive closure of the paper's
  generating relations (Definitions 1.2, 6.1); antisymmetry from a level function. The cover pairs are exactly the
  generating relations (Figures 1 and 2: `fig_1_hasse`, `fig_2_hasse`).
