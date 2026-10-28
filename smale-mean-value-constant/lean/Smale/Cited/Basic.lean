/-
Smale/Cited/Basic.lean — the outside results paper 009 uses, as axioms. Each docstring QUOTES ITS SOURCE VERBATIM, then
says how the Lean form compares; each axiom is no stronger than its source. Nothing else in the project may be an axiom.
SOURCE of all three: [JN] A. Jatar and T. W. Ng, "Smale's mean value constant and admissible univalent Blaschke pairs",
arXiv:2610.21472v2 (2026) — an UNREFEREED PREPRINT. Its LaTeX source (e-print, downloaded 20261027_1537, file
SmaleWBA_Arxiv_.tex, md5 69f6e6e4) was used to check every quote below word for word.
JN's notation: 𝒫_d = polynomials of degree d ≥ 2 with P(0) = 0, P'(0) = 1; 𝒫 = ⋃_{d≥2} 𝒫_d; S(P) = min_{P'(c)=0} |P(c)/c|
(= our `IsPd`, `mval`); 𝒮, finite Blaschke product, admissible pair: JN Sect. 1.2 and Def. 1.1 (= our `InClassS`,
`IsFiniteBlaschke`, `IsAdmissible`).
-/
import Smale.Defs.Basic

namespace Smale.Cited

open Polynomial

/-- **CITED — UNREFEREED PREPRINT.** [JN, Prop. 4.2] (the paper's Theorem 2.2, tex l.146-148), verbatim:
"For every admissible pair $(W,B)$ and every positive real number $A < \frac{1}{B(0)}$, there is a polynomial
$P \in \mathcal{P}$ such that $S(P) > A$. Consequently $$\Bee \leq \M, \ \Bee_{d} \leq \M \quad (d \geq 0) $$"
Lean form: the first sentence only (the "Consequently" is derived: `thm_2_2_hence`); `P ∈ 𝒫` is `∃ d ≥ 2, IsPd d p`. -/
axiom jatarNg_prop_4_2 (W B : ℂ → ℂ) (k : ℕ) (hWB : IsAdmissible W B k) (A : ℝ) (hA0 : 0 < A)
    (hA : A < 1 / (B 0).re) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ p : ℂ[X], IsPd d p ∧ A < mval p

/-- **CITED — UNREFEREED PREPRINT.** [JN, Prop. 3.1] (sketched in the paper's Remark 2.3, tex l.163-171), verbatim:
"Let $P\in\cP_d$ with $S(P)>1$. Suppose $1<R<S(P)$, then there is an admissible pair $(W,B)$ with $$
B(0)=\frac1R,\qquad 1\le\deg B\le d-1 . $$ Consequently for every $d\ge2$, $\Bee_{d-1}\ge S(P)$ for every
$P\in\cP_d$ and hence $\M_d\le\Bee_{d-1}$ and $\M\le\Bee$."
Lean form: the first sentence only; `B(0) = 1/R` (`B(0) > 0` is part of admissible) as `1/(B 0).re = R`. (A Lean
proof would need the Riemann mapping theorem, which Mathlib v4.35 lacks.) -/
axiom jatarNg_prop_3_1 (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (hm : 1 < mval p) (R : ℝ) (hR1 : 1 < R)
    (hRm : R < mval p) :
    ∃ (W B : ℂ → ℂ) (k : ℕ), 1 ≤ k ∧ k ≤ d - 1 ∧ IsAdmissible W B k ∧ 1 / (B 0).re = R

/-- **CITED — UNREFEREED PREPRINT** (a classical result: J. Dieudonné, Ann. Sci. École Norm. Sup. (3) 48 (1931),
247-358). [JN, Lemma 6.3] (the paper's Dieudonné criterion, tex l.237-240), verbatim:
"A polynomial $H(z)=\sum_{k=1}^n a_k z^k$ is univalent in $\D$ if and only if, for every $c\in[-1,1]$, its
Dieudonn\'e polynomial $$ P_c(w):=\sum_{k=1}^n a_k\,U_{k-1}(c)\,w^{k-1} $$ has no zero in $\D$. Here $U_n$ is the
Chebyshev polynomial of the second kind."
Lean form: the "if" direction only (the paper uses only it), for `H` with `H(0) = 0`; `P_c` = `dieudonne H H.natDegree c`
(the coefficients of index above `deg H` are `0`). The extension to every polynomial (tex l.238-240) is the claim
`sec4_dieudonne_any`, proved from this. -/
axiom dieudonne_criterion (H : ℂ[X]) (h0 : H.coeff 0 = 0)
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    IsUnivalentOn (fun z => H.eval z) disk

end Smale.Cited
