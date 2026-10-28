/-
Osserman/Cited/Isoparametric.lean — the ONLY axioms of the 013 Lean project so far: the cited classification of
isoparametric quartics on ℝ^32 (Münzner, Ferus–Karcher–Münzner, Chi) in polynomial form, and the uniqueness of
symmetric Clifford systems of nine matrices on ℝ^16 (FKM). Paper 013, §3 l. 416-482 and §6 l. 670-675.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.Poly

namespace Osserman.Cited

open MvPolynomial Matrix Osserman

/-- **(A) The isoparametric classification on ℝ^32, polynomial form** [Münzner 1980, Satz 2 p. 63, Satz 3 p. 65 and its
proof p. 66, Folgerung p. 66, §4 p. 65, Satz 4(a)(c) p. 67; Ferus–Karcher–Münzner 1981 (English translation
arXiv:1112.2780), Theorem 4.1 p. 8, §4.3 p. 11, §5.9 p. 19, §6.6 p. 22, Definition 3.2 (m ≥ 1); Chi 2020, abstract
p. 225 = Theorem 7.1 of arXiv:1605.00976v2 p. 61].

THIS IS THE POLYNOMIAL FORM OF [Münzner, FKM, Chi]; THE TRANSLATION USES THE PAPER'S OWN SECTION 3 ARGUMENT
(l. 421-437 and l. 457-471: g = 4, n = 31, c = 8; the exclusion of Münzner's alternative ±(2F² - r^{2g}) since
8 ≠ ∓120; connected levels (Satz 4(a)); the multiplicities (7,8); the principal curvatures cot(π/8 + jπ/4); the
congruence of the zero levels and the uniqueness of the Cartan polynomial up to sign), WHICH LEAN CANNOT EXPRESS
(Mathlib has no hypersurfaces or principal curvatures): THOSE STEPS ARE NOT FORMALIZED. Checked against the sources
(true, no stronger).

The paper's sentences (the posting copy, P013_short.tex):
* l. 421-426: "For a homogeneous polynomial of degree $g$ satisfying $\norm{\nabla F}^2=g^2\norm z^{2g-2}$ and
  $\Delta F=c\norm z^{g-2}$ on $\R^{n+1}$, nonconstant on the sphere, \cite[Satz 3, p.~65]{Munzner} shows that $0$ is a
  regular value of $F|S^n$ and that the zero level is an isoparametric hypersurface"
* l. 426-429: "Its Folgerung (corollary) on p.~66 identifies $F$ with the Cartan polynomial of these hypersurfaces when
  both $g(n-1)-c$ and $g(n-1)+c$ are nonzero. Satz 4(a), p.~67, gives connected level sets."
* l. 440-442: "Chi's classification \cite[abstract, p.~225]{Chi} gives exactly three families with unordered
  multiplicities $\{7,8\}$. They are the FKM family with parameter $m=7$ and the two FKM families with $m=8$."
* l. 447-451: "For a symmetric Clifford system $P_0,\ldots,P_m$ on $\R^{32}$, \cite[Theorem 4.1, p.~8; Section 4.3,
  p.~11]{FKM} gives $F_P(z)=\norm z^4-2\sum_{i=0}^m\ip{P_iz}z^2$, $(m_1,m_2)=(m,15-m)$."
* l. 465-471: "The Cartan polynomial of a connected oriented isoparametric hypersurface is determined by it, and
  reversing the orientation replaces it by its negative \cite[\S4, p.~65]{Munzner}; ... Hence
  $F=\varepsilon F_P\circ U$ with $\varepsilon\in\{1,-1\}$."

The Lean statement keeps `U`, `ε` and an unrestricted `m`: absorbing `U` into the `P_i`, the Laplacian of `F_P` and the
resulting `ε = 1, m = 7` or `ε = -1, m = 8` (l. 473-480) are PROVED rows, not part of this axiom. Münzner's hypothesis
"nonconstant on the sphere" is kept (the paper's Lemma 2.1, l. 394, proves it for its `F`). -/
axiom isoparametric_quartic_R32 (F : MvPolynomial (Fin 32) ℝ) (hF : F.IsHomogeneous 4)
    (hgrad : gradSqP F = 16 * sqP 32 ^ 3) (hlap : lapP F = 8 * sqP 32)
    (hnc : ∃ z w : Vec 32, z ⬝ᵥ z = 1 ∧ w ⬝ᵥ w = 1 ∧ eval z F ≠ eval w F) :
    ∃ (m : ℕ) (P : Fin (m + 1) → Matrix (Fin 32) (Fin 32) ℝ), 0 < m ∧ IsSymmCliffordSystem P ∧
      ∃ U ∈ Matrix.orthogonalGroup (Fin 32) ℝ, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ z : Vec 32, eval z F = ε * eval (U *ᵥ z) (FKMP P)

/-- **(Q) Symmetric Clifford systems of nine matrices on ℝ^16 are unique up to orthogonal conjugacy and the sign of one
generator** [Ferus–Karcher–Münzner 1981, Sections 3.4-3.5, pp. 6-7 of the English translation; Nikolayevsky 2012,
p. 6 of arXiv:0910.1645v1].

The paper's sentences (P013_short.tex l. 670-675): "Let $\Cl_+(9)$ denote the real Clifford algebra on nine generators
with squares $+1$ and pairwise anticommutation. Then $\Cl_+(9)\cong M_{16}(\R)\oplus M_{16}(\R)$. Its representations
on $\R^{16}$ are equivalent up to orthogonal conjugacy and the sign of one generator; see \cite[Sections 3.4--3.5,
pp.~6--7]{FKM} and \cite[p.~6 of arXiv:0910.1645v1]{Nik2012}."
Lean form: for two such systems `S`, `S'` there are `T ∈ O(16)` and `σ = ±1` with `S'_0 = σ T S_0 Tᵀ` and
`S'_i = T S_i Tᵀ` for `i ≠ 0` (FKM 3.5: "replacing P_0 by -P_0"). Checked against the source
(true, equivalent to FKM 3.4-3.5). -/
axiom symm_clifford9_unique (S S' : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ) (hS : IsSymmCliffordSystem S)
    (hS' : IsSymmCliffordSystem S') :
    ∃ T ∈ Matrix.orthogonalGroup (Fin 16) ℝ, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      S' 0 = σ • (T * S 0 * Tᵀ) ∧ ∀ i : Fin 9, i ≠ 0 → S' i = T * S i * Tᵀ

end Osserman.Cited
