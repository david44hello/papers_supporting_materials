/-
HibiLi/Cited/CJK.lean — cited result: the dual graph of a polytopal subdivision is connected (Casabella–Joswig–Kastner).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Subdivision

namespace HibiLi.Cited

/-- **Casabella, Joswig, Kastner** [CJK], *Subdivisions of hypersimplices: with a view toward finite metric spaces*,
Experimental Mathematics 34(4) (2025), 808–823, DOI 10.1080/10586458.2024.2418831; arXiv:2402.17665v1.
The paper cites it as [CJK, Lemma 2]: published Lemma 2 = arXiv v1 Lemma 3 (printed p. 4).  The published numbering
was checked against the open-access journal text on 2026-10-26; the passages below are from arXiv v1.

Source, verbatim (arXiv v1):
* p. 4, Lemma 3: "Let S be a subdivision of a polytope P. Then the dual graph G∨(S) is simple and connected, i.e.,
  G∨(S) is a connected graph without loops or multiple edges."
* p. 4, dual graph: "The dual graph G∨(C) of a pure polyhedral complex C is the abstract graph whose nodes are the
  maximal cells. There is an edge between two nodes for each codimension one face shared by the corresponding
  maximal cells."
* p. 2, setting and definition: "Furthermore, we require that A affinely spans the entire space, i.e., we have
  dim conv(A) = d. A finite set of polytopes, S, (and all their faces) form a polyhedral subdivision of A if the
  polytopes in S meet face to face and cover conv(A)."

Translation (definitions in HibiLi/Defs/Subdivision.lean): a finite set of nonempty polytopes, closed under nonempty
faces, whose union is the base and in which any two cells that meet do so in a common face; graph nodes are the
inclusion-maximal cells, adjacent when they share a face of codimension one in both.  The full-span hypothesis is
the source's convention; lower-dimensional bases are handled by a proved transport theorem, not by this statement.
The source definition puts no condition on the vertices of the cells; the application (the common refinement of the
two affinity subdivisions, restricted to a face) uses this generality.  Only connectivity is imported.

Intended use: only in the proof of Lemma 3.5(ii). -/
axiom cjk_dual_connected {ι : Type*} [Fintype ι]
    (base : Set (ι → ℝ)) (cells : Finset (Set (ι → ℝ)))
    (polytope : HibiLi.IsPolytope base) (nonempty : base.Nonempty)
    (spans : affineSpan ℝ base = ⊤)
    (subdivision : HibiLi.IsFinitePolytopalSubdivision base cells) :
    (HibiLi.subdivisionDualGraph cells).Connected

end HibiLi.Cited
