/-
HibiLi/Cited/Others.lean — the other cited results, taken as AXIOMS, each in its source's own conventions.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Switch

namespace HibiLi.Cited

open HibiLi

/-- **Hibi–Li 2016, Theorem 2.1** (Math. Scand. 118 (2016), 5–12; arXiv:1208.4029v1 §2; = paper Theorem 2.2).  Source, verbatim: "The order polytope
O(P) and the chain polytope C(P) of a finite poset P are unimodularly equivalent if and only if the poset of Figure 1 of
Theorem 1.3 does not appear as a subposet of P."  Stated with Hibi–Li's own `O(P)` (`a_i ≥ a_j` if `x_i ≤ x_j`), own
`C(P)` (maximal chains) and own unimodular equivalence (`Q = f_U(P) + w`, `f_U(v) = vU`).  "Subposet" is Stanley's
(EC1 p. 243: always an induced subposet), which is exactly `ContainsX`. -/
axiom hibiLi_thm_2_1 (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] :
    UnimodEquivHL (orderPolytopeHL P) (chainPolytopeHL P) ↔ ¬ ContainsX P

/-- **Hibi–Li–Sahara–Shikama 2017, Theorem 2.1** (Discrete Math. 340, p. 992).  Source, verbatim: "Let P be an
arbitrary finite poset. Then the number of edges of the order polytope O(P) is equal to that of the chain polytope
C(P)."  Their `O(P)`, `C(P)` are Hibi–Li's (same §1 text).  Used only for the remark that the equality part fails for
edges (paper lines 125–129 and 145–147; abstract lines 55–57). -/
axiom hlss_thm_2_1 (P : Type*) [Fintype P] [PartialOrder P] :
    fNum (orderPolytopeHL P) 1 = fNum (chainPolytopeHL P) 1

/-- **Ziegler, Lectures on Polytopes, Ch. 2 (face figures)** (used in paper Lemma 4.7, lines 659–663).  The faces of a
polytope `B` that contain a face `E` form the face lattice of a polytope `B/E` of dimension `dim B − dim E − 1` (empty when
`E = B`); a face `G ⊇ E` corresponds to a face of dimension `dim G − dim E − 1`.  Stated for faces STRICTLY containing
`E` (they correspond to the NONEMPTY faces of `B/E`), with only the dimension bookkeeping we use. -/
axiom ziegler_face_figure {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) (hB : IsPolytope B)
    (E : Set (ι → ℝ)) (hE : IsFace B E) :
    ∃ (m : ℕ) (Q : Set (Fin m → ℝ)), IsPolytope Q ∧ (Q = ∅ ↔ E = B) ∧
      (Q.Nonempty → adim Q + adim E + 1 = adim B) ∧
      ∃ φ : {G // IsFace B G ∧ E ⊂ G} ≃ {G' // IsFace Q G'}, ∀ G, adim G.1 = adim (φ G).1 + adim E + 1

end HibiLi.Cited
