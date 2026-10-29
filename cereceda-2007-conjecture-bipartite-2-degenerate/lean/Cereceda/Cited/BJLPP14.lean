/-
Cereceda/Cited/BJLPP14.lean — the cited statements [BJLPP14, Theorems 8 and 10], used for the claim that semi-false graphs lie in
class (iii) and for "a bipartite distance-hereditary graph ... is chordal bipartite, hence semi-false, and lies in (iii)"
(short v3.90 l. 157-162, 176-179; OAT graphs land in (iii) through Theorem 10, l. 179-192).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

SOURCE (REFEREED): M. Bonamy, M. Johnson, I. Lignos, V. Patel, D. Paulusma, Reconfiguration graphs for vertex
colourings of chordal and chordal bipartite graphs, J. Comb. Optim. 27 (2014); theorem numbers and lines ("l.") from
the HAL open version lirmm-00782882 (plain-text copy, txt).
- Separator (l. 171-172), verbatim: "A separator of a graph G = (V, E) is a set S ⊂ V such that G − S has more
  connected components than G" = `IsSeparator`.
- k-colour-dense (l. 193-207), verbatim: "For a fixed positive integer k, we say that a k-colourable graph G on n
  vertices is k-colour-dense if either (i) G is the disjoint union of cliques, each of which has at most k vertices, or
  (ii) G has a separator S, and G−S has components D and D′ with vertices u ∈ D and v ∈ D′ such that (a) |D| = 1 or
  |D ∪ S| ≤ k, (b) S ⊆ N (v), and (c) identifying u and v in G results in a k-colour-dense graph G′." =
  `IsColourDense k` (Defs/ColourDense.lean).
- Chordal bipartite (l. 391-392), verbatim: "A chordal bipartite graph is a bipartite graph with no induced cycle of
  length more than 4." = `IsChordalBipartite` (Defs/Intro.lean: bipartite, and every cycle of length at least 6 has a
  chord; the same class, as the cycles of a bipartite graph have even length).
- Semi-false (l. 394-399), verbatim: "Let us call a graph semi-false if it can be constructed from a set of one or more
  isolated vertices by a sequence of the following two operations, namely adding a pendant vertex and adding a
  semi-false twin. Here, a pendant vertex in a graph is a vertex of degree one, and a vertex u is a semi-false twin of
  another vertex v if N (u) ⊆ N (v)." = `IsSemiFalse` (Defs/Classes.lean) on a NONEMPTY vertex type ("one or more").
- Theorem 8 (l. 414-415), verbatim: "Theorem 8. The class of semi-false graphs is a proper superclass of the class of
  chordal bipartite graphs."
- Theorem 10 (l. 460), verbatim: "Theorem 10. Every semi-false graph is 2-colour-dense."
FORM: Theorem 10 exactly, and the inclusion half of Theorem 8 (weaker than "proper superclass"), for these definitions,
on a nonempty finite vertex type.
-/
import Cereceda.Defs.Classes
import Cereceda.Defs.ColourDense

namespace Cereceda.Cited

/-- [BJLPP14, Theorem 8], the inclusion half: every chordal bipartite graph (on one or more vertices) is semi-false. -/
axiom bjlpp14_thm8 : ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V),
    IsChordalBipartite G → IsSemiFalse G

/-- [BJLPP14, Theorem 10]: every semi-false graph (on one or more vertices) is `2`-colour-dense. -/
axiom bjlpp14_thm10 : ∀ {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V),
    IsSemiFalse G → IsColourDense 2 G

end Cereceda.Cited
