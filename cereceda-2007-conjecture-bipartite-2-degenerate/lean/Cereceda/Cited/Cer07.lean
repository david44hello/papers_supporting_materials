/-
Cereceda/Cited/Cer07.lean — the cited statement [Cer07, Theorem 5.22] (used for the claims that the conjecture holds
for bipartite 2-degenerate graphs for EVERY k ≥ 4, short paper v3.90 l. 39-42, 51-56, 112-114, that it settles d = 1
(l. 112-113), and that open problem 1 would prove the d = 2 case, l. 741-742).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

SOURCE: L. Cereceda, Mixing graph colourings, PhD thesis, London School of Economics, 2007 ("txt l." = a line of a
plain-text copy of the thesis PDF).
- Theorem 5.22 (p. 94, txt l. 4508-4509), verbatim: "For a graph G with n vertices and k ≥ 2 deg(G) + 1, the diameter
  of C_k(G) is O(n^2)."
- deg(G) (p. 13, txt l. 326-331): "The degeneracy of G, deg(G), is defined as the largest minimum degree of any subgraph
  of G ... a graph has degeneracy r if and only if there is an ordering v1, ..., vn of its vertices such that ... vi has
  at most r neighbours vj with j < i."
- k ≥ 2 (section "Colourings and recolouring: the colour graph", txt l. 362-366): "for a natural number k ≥ 2, we
  define a k-colouring of a graph G as a function α : V → {1, 2, . . . , k} ... (We insist that k ≥ 2 in order to avoid
  trivialities ...)". So the theorem speaks only of k ≥ 2, and the Lean statement assumes 2 ≤ k as well (in every use
  d ≥ 1, so k ≥ 3).
- C_k(G) (Definition 1.1, txt l. 373-376): "the k-colour graph of G ... has the k-colourings of G as its vertex set, with
  two k-colourings joined by an edge in C_k(G) if they differ in colour on precisely one vertex of G" = `recolGraph G k`.
FORM (no stronger than the source): for each `d` and each `k ≥ 2d + 1` there is ONE constant `C`, allowed to depend on
`d` and `k`, with `diam R_k(G) ≤ C n²` for every graph `G` of degeneracy at most `d` (then `k ≥ 2 deg(G) + 1`).
"The diameter is O(n²)" says the diameter is finite, so `ediam` (`⊤` when `R_k(G)` is disconnected) is used.
The thesis proof (txt l. 4548-4551: "every vertex vi is considered only once this way, and for every vi only n − i
recolourings of other vertices are needed before it can be recoloured to β(vi)") gives at most
`∑ (n − i + 1) = n(n+1)/2 ≤ n²` recolourings for every such `G`, so the statement is true (with `C = 1`).
-/
import Cereceda.Defs.Basic

namespace Cereceda.Cited

/-- [Cer07, Theorem 5.22], in the weakest form of "O(n²)": a constant for each pair `d`, `k` with `k ≥ 2d + 1`. -/
axiom cer07_thm522 : ∀ d k : ℕ, 2 * d + 1 ≤ k → 2 ≤ k → ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], IsDegenerate G d →
      (recolGraph G k).ediam ≤ ((C * Fintype.card V ^ 2 : ℕ) : ℕ∞)

end Cereceda.Cited
