/-
LeeDiam/Cited/Lee26.lean — the cited statements of paper 004 (short v1.50): Theorem 2.1 (l. 141-144), the adjacency
criterion for the graphs of O(P) and C(P), as TWO statements, one per source:
  (1) ideals:     Ikebe-Tamura [IT95] and Hibi-Li [HL19];
  (2) antichains: Chvatal [Chv75] (stable-set polytopes), applied to C(P) = the stable-set polytope of the
                  comparability graph (Stanley [Sta86]).
The paper adds "see [Lee26, Theorem 4]"; [Lee26] (J. Lee, arXiv:2610.07413) is a PREPRINT, not refereed.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

SOURCES, refereed:
  [IT95] Y. T. Ikebe and A. Tamura, Ideal polytopes and face structures of some combinatorial optimization problems,
         Math. Programming 71 (1995), 1-15.
  [HL19] T. Hibi and N. Li, Cutting convex polytopes by hyperplanes, Mathematics 7(5) (2019), Article 381
         (arXiv:1402.3805).
  [Chv75] V. Chvatal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), 138-154.
  [HLSS17] T. Hibi, N. Li, Y. Sahara, A. Shikama, Discrete Math. 340 (2017), 991-994 (arXiv:1508.00187), Lemma 1.1,
         restates both criteria with a reference to Hibi-Li: "(a) Given poset ideals I and J with I ≠ J, the segment
         combining ρ(I) with ρ(J) is an edge of O(P) if and only if I ⊂ J and J \ I is connected in P. (b) Given
         antichains A and B with A ≠ B, the segment combining ρ(A) with ρ(B) is an edge of C(P) if and only if
         (A \ B) ∪ (B \ A) is connected in P." ([HLSS17] uses the same O(P) as here: 0 ≤ a_i ≤ 1, a_i ≥ a_j if
         x_i ≤ x_j; its (a) is meant up to interchanging I and J.)
WORDING QUOTED from the preprint [Lee26, Theorem 4] (arXiv:2610.07413v1, the version the paper cites):
  "Theorem 4 ([HL19]). Let I ≠ J be ideals of P, and let A ≠ B be antichains of P. Then [ρ(I), ρ(J)] is an edge of O(P)
  if and only if, after possibly interchanging I and J, (E_O) I ⊆ J and J \ I is connected; and [ρ(A), ρ(B)] is an edge
  of C(P) if and only if (E_C) A△B is connected."
  "The second part of Theorem 4 is the special case G = G(P) of the theorem of [Chv75] that two stable sets A, B of a
  graph G give adjacent vertices of its stable-set polytope if and only if A△B induces a connected subgraph of G."
CONVENTIONS (= Lee's and [HLSS17]'s): ρ(W) = indicator vector (`HibiLi.setVector`); O(P) = {0 ≤ x ≤ 1, x_i ≥ x_j
whenever a_i ⪯ a_j} (`LeeDiam.orderPolytope`); C(P) = {x ≥ 0, Σ_K x ≤ 1 for every chain K} (`LeeDiam.chainPolytope`);
"edge" = face of dimension 1, a segment joining two distinct vertices (`HibiLi.IsFace` of the segment); "connected"
(for I ≠ J nested and for A ≠ B the sets J \ I and A △ B are nonempty) = `LeeDiam.IsConnSet`.
STATUS: true, and no stronger than the sources ([IT95], [HL19], [Chv75] + [Sta86]; restated in [HLSS17] and [Lee26]).
-/
import LeeDiam.Defs.Basic
import LeeDiam.Vendor.HibiLi.Example21.VertexBijection

namespace LeeDiam.Cited

/-- Theorem 2.1 of paper 004, first part ([IT95], [HL19]; restated in [HLSS17, Lemma 1.1(a)] and [Lee26, Theorem 4]):
two distinct ideals give an edge of `O(P)` iff, after possibly interchanging them, `I ⊆ J` and `J \ I` is connected. -/
axiom adjacency_ideals : ∀ (P : Type) [Fintype P] [PartialOrder P],
    ∀ I J : Set P, IsIdeal I → IsIdeal J → I ≠ J →
      (HibiLi.IsFace (orderPolytope P) (segment ℝ (HibiLi.setVector I) (HibiLi.setVector J)) ↔
        (I ⊆ J ∧ IsConnSet (J \ I)) ∨ (J ⊆ I ∧ IsConnSet (I \ J)))

/-- Theorem 2.1 of paper 004, second part ([Chv75] for the stable-set polytope of the comparability graph, which is
`C(P)` by [Sta86]; restated in [HLSS17, Lemma 1.1(b)] and [Lee26, Theorem 4]): two distinct antichains give an edge
of `C(P)` iff `A △ B` is connected. -/
axiom adjacency_antichains : ∀ (P : Type) [Fintype P] [PartialOrder P],
    ∀ A B : Set P, IsAntichainSet A → IsAntichainSet B → A ≠ B →
      (HibiLi.IsFace (chainPolytope P) (segment ℝ (HibiLi.setVector A) (HibiLi.setVector B)) ↔
        IsConnSet (symmDiff A B))

/-- Theorem 2.1 of paper 004 = [Lee26, Theorem 4], both parts together (a theorem: the conjunction of the two cited
statements above). -/
theorem lee26_thm4 : ∀ (P : Type) [Fintype P] [PartialOrder P],
    (∀ I J : Set P, IsIdeal I → IsIdeal J → I ≠ J →
      (HibiLi.IsFace (orderPolytope P) (segment ℝ (HibiLi.setVector I) (HibiLi.setVector J)) ↔
        (I ⊆ J ∧ IsConnSet (J \ I)) ∨ (J ⊆ I ∧ IsConnSet (I \ J)))) ∧
    (∀ A B : Set P, IsAntichainSet A → IsAntichainSet B → A ≠ B →
      (HibiLi.IsFace (chainPolytope P) (segment ℝ (HibiLi.setVector A) (HibiLi.setVector B)) ↔
        IsConnSet (symmDiff A B))) := by
  intro P _ _
  exact ⟨adjacency_ideals P, adjacency_antichains P⟩

end LeeDiam.Cited
