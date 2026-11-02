/-
HibiLi/Cited/Fourier.lean — the two results of G. Fourier, "The Hibi–Li face-number conjecture", arXiv:2609.23629v1
(2026), that the paper uses without proof (paper lines 186–189 and 259–264), each in the narrowest form the paper uses.
The preprint is not yet refereed.  Proposition 5.2 is taken as an AXIOM: Lean does not check it, and every claim whose
AUDIT.md row lists it is conditional on it (in particular Theorem 4.1, Corollary 5.3 and the headline).  Lemma 4.1 is
NOT an assumption: the statement below is a THEOREM, proved in Lean with no cited input (HibiLi/Proofs/Fourier41.lean,
along the paper's informal reading, lines 380–384); its source text is kept here for the record.  Fourier's Theorem 1.1
and Proposition 6.1 are NOT axioms either: we derive them (as Fourier does).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Switch
import HibiLi.Proofs.Fourier41

namespace HibiLi.Cited

open HibiLi HibiLi.Switch

/-- **Fourier, Lemma 4.1** (= paper Lemma 3.2, first equality, lines 373–376).  Source, verbatim: "One has (3)
`F_{O_{I∪{q},J\{q}}(P)} − F_{O_{I,J}(P)} = F_B + F_{S∨T} − F_S − F_T`."  The paper (line 371): "The subdivisions
`S`, `T` and `R`, the polynomials `F_𝒴` and the carriers are those of Fourier [Section 4]. … So Lemma 3.2 and
Proposition 3.4 below apply to them as stated."  (Fourier's Lemma 4.1 is this one equality; it is the first equality of
the paper's Lemma 3.2, lines 186–188 and 261.)  PROVED in Lean, no cited input: `Proofs.Fourier41.fourier_lemma_4_1_proved`. -/
theorem fourier_lemma_4_1 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT :=
  Proofs.Fourier41.fourier_lemma_4_1_proved s

/-- **Fourier, Proposition 5.2** (= paper Proposition 3.4, lines 397–399).  Source, verbatim: "(Relative
transversality) The subdivisions S and T determined by L and U are transverse relative to every face of B."  The paper
(line 371): "The subdivisions `S`, `T` and `R`, the polynomials `F_𝒴` and the carriers are those of Fourier
[Section 4]. … So Lemma 3.2 and Proposition 3.4 below apply to them as stated." -/
axiom fourier_prop_5_2 {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) : s.Transverse

end HibiLi.Cited
