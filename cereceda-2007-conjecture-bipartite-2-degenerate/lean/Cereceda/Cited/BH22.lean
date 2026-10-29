/-
Cereceda/Cited/BH22.lean — the cited statement [BH22, Theorem 1] (first bullet), used for the claim that the conjecture
holds for all planar bipartite graphs (short v3.90 l. 123-129: degeneracy `3` and `k ≥ 6`, "As planar bipartite graphs are
`3`-degenerate and `6 = (3/2)(3+1)`").
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

SOURCE: M. Bousquet and M. Heinrich, A polynomial version of Cereceda's conjecture, arXiv:1903.05619v1 (the version
the paper's theorem numbers cite; arXiv has only v1; journal version J. Combin. Theory Ser. B 155 (2022)); "txt l." = a
line of a plain-text copy of the arXiv PDF.
- Theorem 1 (txt l. 123-125), verbatim: "Let d, k ∈ N and G be a d-degenerate graph. Then G(G, k) has diameter at most: • Cn² if
  k ≥ (3/2)(d + 1) (where C is a constant independent of k and d), • ... , • ... ."
- d-degenerate (Section 1, txt l. 81-82), verbatim: "A graph G is d-degenerate if any subgraph of G admits a vertex of
  degree at most d" = `IsDegenerate G d` (Defs/Basic.lean, stated for induced subgraphs, which is equivalent).
- G(G, k) (txt l. 68-70) is the k-reconfiguration graph: the proper k-colourings of G, two of them adjacent when they
  differ on exactly one vertex = `recolGraph G k`. "Diameter at most Cn²" includes that G(G, k) is connected (the
  recolouring diameter "is equal to +∞" when G(G, k) is not connected, txt l. 75-76; the proof transforms any colouring
  into any other), so `ediam` (`⊤` when disconnected) is used.
FORM (weaker than the source): for each pair `d`, `k` with `k ≥ (3/2)(d + 1)`, that is `3(d + 1) ≤ 2k`, there is a
constant `C`, allowed to depend on `d` and `k`, with `diam R_k(G) ≤ C n²` for every `d`-degenerate `G`. The source's
`C` is one constant for all `d` and `k`; the paper uses only `d = 3`, `k ≥ 6`.
NOT CITED HERE: [BH22, Theorem 2] ("Let G be a planar bipartite graph. The diameter of G(G, 5) is at most 4n²"). Mathlib
has no planar graphs, so it is a hypothesis of the planarity-free row `intro_planar_bipartite_deduction`.
-/
import Cereceda.Defs.Basic

namespace Cereceda.Cited

/-- [BH22, Theorem 1], first bullet, in the weakest form of "at most `Cn²`": a constant for each pair `d`, `k` with
`k ≥ (3/2)(d + 1)`. -/
axiom bh22_thm1_quadratic : ∀ d k : ℕ, 3 * (d + 1) ≤ 2 * k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], IsDegenerate G d →
      (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)

end Cereceda.Cited
