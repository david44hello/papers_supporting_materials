/-
HibiLi/Cited/Fourier.lean — results of G. Fourier, "The Hibi–Li face-number conjecture", arXiv:2609.23629v1 (2026),
taken as AXIOMS.  This is a preprint, not yet refereed; Lean does not check it.  Only the results the paper cites
(paper lines 215–225) appear, each in the narrowest form the paper uses.  Every claim whose AUDIT.md row lists one of
these two is conditional on it; in particular Theorem 4.1, Corollary 5.3 and the headline rest on both, so a single
error in Fourier's preprint would make those results unsound.  Fourier's Theorem 1.1 and Proposition 6.1 are
NOT axioms: we derive them from these (as Fourier does), which keeps the trusted list short.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Switch

namespace HibiLi.Cited

open HibiLi HibiLi.Switch

/-- **Fourier, Lemma 4.1** (= paper Lemma 3.2, first equality).  Source, verbatim: "One has (3)
`F_{O_{I∪{q},J\{q}}(P)} − F_{O_{I,J}(P)} = F_B + F_{S∨T} − F_S − F_T`." -/
axiom fourier_lemma_4_1 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT

/-- **Fourier, Proposition 5.2** (= paper Proposition 3.4).  Source, verbatim: "(Relative transversality) The
subdivisions S and T determined by L and U are transverse relative to every face of B." -/
axiom fourier_prop_5_2 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) : s.Transverse

end HibiLi.Cited
