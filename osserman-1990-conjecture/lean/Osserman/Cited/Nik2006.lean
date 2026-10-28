/-
Osserman/Cited/Nik2006.lean — four cited results of Y. Nikolayevsky used by paper 013 (Section 7, Section 8, Theorem G):
Lemma 3.1 (polynomial eigenvector frames), Lemma 3.11 (sums of at most eight squares divisible by |x|²), Theorem 3.1
(the ring 𝒪 is a UFD, Nagata) and Proposition 2.1 (multiplicity nine gives Cliff(6)), each stated as its source states
it, or weaker (n = 16). Checked against the sources.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots

namespace Osserman.Cited

open MvPolynomial Matrix Osserman

/-- **[Nik2006, Lemma 3.1(1),(2), p. 383]** = **[Nikolayevsky, Manuscripta Math. 115 (2004) 31-53, Lemma 2, p. 3]**.
Paper's citation: Y. Nikolayevsky, "On Osserman manifolds of dimension 16", Contemporary Geometry and Related Topics,
Belgrade 2005, Univ. Belgrade 2006, 379-398 (p. 383),
where it says "The proof is given in Lemma 2 of [8]". Refereed status: Nik2006 is a conference-proceedings
article; the article does not state the volume's refereeing. The same statement for ℝ^n, with the same text, is Lemma 2
of Y. Nikolayevsky, "Osserman manifolds of dimension 8", Manuscripta Math. 115 (2004) 31-53 (refereed;
arXiv:math/0310387, p. 3).
Cited at lines 741-747 of P013_short.tex (Theorem E) and in sec_small_roots.tex (posting copy) (l. 67-72, 175, 255, 299).
Source text (Nik2006 p. 383): "(1.) Let R be an Osserman algebraic curvature tensor in R^n whose Jacobi operator has k
distinct eigenvalues, one of which is zero, and let λ ≠ 0 be a simple eigenvalue. Then for every X ≠ 0, the eigenspace
E_{λ‖X‖²}(X) of R_X is spanned by a vector P(X) all of whose nonzero components are odd homogeneous polynomials of
degree 2m+1 ≤ k−1, and for all unit vectors X, ⟨P(X),X⟩ = 0, ‖P(X)‖² = 1, P(P(X)) = −X. (2.) Let R be an Osserman
algebraic curvature tensor in R^n whose Jacobi operator has k distinct eigenvalues, one of which is zero, and let λ ≠ 0
be an eigenvalue of multiplicity 2. Then for every X ≠ 0, the eigenspace E_{λ‖X‖²}(X) of R_X is spanned by vectors
U(X), V(X) all of whose nonzero components are odd homogeneous polynomials of degree 2m+1 ≤ k−1, and for all unit
vectors X, ⟨U(X),X⟩ = ⟨V(X),X⟩ = ⟨U(X),V(X)⟩ = 0, ‖U(X)‖² = ‖V(X)‖² = 1." (p. 379: "eigenvalues of the Jacobi
operator" are those of R_X on X^⊥ for unit X.)
Lean form (weaker than the source: n = 16 only; "spanned by" kept as membership plus orthonormality at unit x): `R`
Osserman with exactly `k` distinct reduced eigenvalues `ev`, all of positive multiplicity `m` (`hpos`), filling `x^⊥`,
one of them zero; `τ = ev i₀ ≠ 0` of multiplicity 1 or 2 (the source's two cases). One degree `d` for all fields, as
the source's single "2m+1". The source's sign convention is opposite (`R_X = −J_x`; P013_short.tex l. 782-784): eigenvalues
change sign, eigenspaces and "one of which is zero" do not. -/
axiom nik2006_lemma_3_1 {k : ℕ} (R : CurvTensor 16) (hO : R.IsOsserman) (ev : Fin k → ℝ)
    (hev : Function.Injective ev) (m : Fin k → ℕ) (hpos : ∀ i, 0 < m i) (hsum : ∑ i, m i = 15)
    (hpat : ∀ x : Vec 16, x ⬝ᵥ x = 1 → ∀ i, R.redMult x (ev i) = m i) (hzero : ∃ j, ev j = 0) (i₀ : Fin k)
    (hτ : ev i₀ ≠ 0) (ht : m i₀ = 1 ∨ m i₀ = 2) :
    ∃ (d : ℕ) (E : Fin (m i₀) → Fin 16 → MvPolynomial (Fin 16) ℝ), Odd d ∧ d ≤ k - 1 ∧
      (∀ a j, (E a j).IsHomogeneous d) ∧
      ∀ x : Vec 16, x ⬝ᵥ x = 1 →
        (∀ a b, evalField (E a) x ⬝ᵥ evalField (E b) x = if a = b then 1 else 0) ∧
        (∀ a, evalField (E a) x ∈ Module.End.eigenspace (R.jacobiMap x) (ev i₀) ⊓ perp x) ∧
        (m i₀ = 1 → ∀ a, evalField (E a) (evalField (E a) x) = -x)

/-- **[Nik2006, Lemma 3.11, p. 398]** (same article as above), cited at lines 813-817 of
P013_short.tex (Remark 7.2), at lines 64-65 and 310 of sec_small_roots.tex (posting copy) (Section 8) and, with its proof, at lines 254-257 of
sec_polynomial_gram.tex (Theorem G). Source text: "Let f_1, …, f_m be polynomials in R^16 such that ‖X‖² divides
∑_i f_i². If m ≤ 8, then ‖X‖² divides each of f_i." Lean form: the same, word for word (`sqP 16 = ∑ x_i²`).
Refereed status: as for Lemma 3.1 (proceedings). The proof (p. 398) uses Nagata, J. Math. Soc. Japan 9 (1957), and
Pfister, Quadratic Forms with Applications to Algebraic Geometry and Topology, LMS Lecture Notes 217 (1995), Thm 3.1.4:
the level of ℝ(x_1..x_15)(√(−∑x_j²)) is 8. The statement is true and sharp at 8. -/
axiom nik2006_lemma_3_11 :
    ∀ k : ℕ, k ≤ 8 → ∀ p : Fin k → MvPolynomial (Fin 16) ℝ, sqP 16 ∣ ∑ i, p i ^ 2 → ∀ i, sqP 16 ∣ p i

/-- **[Nik2006, Theorem 3.1, p. 397]** (the ring 𝒪 = ℝ[x_1, …, x_16]/(|x|²) is a UFD). Paper's citation: Y.
Nikolayevsky, "On Osserman manifolds of dimension 16", Contemporary Geometry and Related Topics, Belgrade 2005, Univ.
Belgrade 2006, 379-398 (p. 397), where it
is "Nagata's Theorem [4]" = M. Nagata, "A remark on the unique factorization theorem", J. Math. Soc. Japan 9 (1957)
143-145 (refereed journal; reference [4] on p. 398). Refereed status of Nik2006 itself: conference proceedings, refereeing not
stated. Cited at lines 62-63 of sec_small_roots.tex (posting copy) ("$\mathcal O$ is a UFD \cite[Theorem~3.1, p.~397]{Nik2006}").
Source text (p. 397): "Let for X = (x1, ..., x16), (‖X‖²) be the ideal of R[X] generated by ‖X‖², and K =
R[X]/(‖X‖²), with π : R[X] → K the natural projection. We need the following two facts (the first one is Nagata's
Theorem [4]). Theorem 3.1 The ring K is a unique factorization domain (UFD)."
Lean form (WEAKER than the source): `Ocal` (Osserman/Defs/SmallRoots.lean) is this `K`; the domain property is ASSUMED
(an instance argument; it is the proved row `s8_q_prime`) and only unique factorization is taken from the source.
Mathlib's `UniqueFactorizationMonoid` itself needs only `CommMonoidWithZero`; the `IsDomain` premise is a true extra
hypothesis, so the statement is no stronger than the source (review a3 NIT-3). -/
axiom nik2006_thm_3_1 [IsDomain Ocal] : UniqueFactorizationMonoid Ocal

/-- **[Nik2006, Proposition 2.1, p. 382]** (multiplicity nine gives a Cliff(6)-structure). Same source and refereed
status as `nik2006_thm_3_1` (p. 382). Cited at lines 185-186, 216-217, 246-247, 265-266 and 289 of
sec_small_roots.tex (posting copy), always for a pattern with an eigenvalue of multiplicity nine.
Source text (p. 382): "Proposition 2.1 An Osserman algebraic curvature tensor in R16 whose Jacobi operator has an
eigenvalue of multiplicity 9 has a Clifford structure Cliff(6)." Definition 2.1 (p. 381): "An algebraic curvature
tensor R in Rn has a Cliff(ν)-structure (ν ≥ 0), if there exist anticommuting skew-symmetric orthogonal operators J1,
..., Jν, and the numbers λ0, µ1, ..., µν, with µs ≠ λ0, such that R(X,Y)Z = λ0(⟨X,Z⟩Y − ⟨Y,Z⟩X) + ∑_{s=1}^ν
(1/3)(µs − λ0)(2⟨JsX,Y⟩JsZ + ⟨JsZ,Y⟩JsX − ⟨JsZ,X⟩JsY). (1)" Conventions (p. 379): "RX Y = R(X,Y)X ... "eigenvalues of
the Jacobi operator" refers to eigenvalues of the restriction of RX, with X a unit vector, to the subspace X⊥" — so the
multiplicity is our reduced multiplicity `redMult`, and the source's Jacobi operator is minus ours (`J_x = R(·,x)x`);
multiplicities, "Osserman" and the Clifford shape do not change with the sign.
Lean form (WEAKER than the source): six anticommuting orthogonal complex structures (`IsCliffordStr`) with
`J_x = l₀Π(x) + ∑ η_i (J_ix)(J_ix)ᵀ`; `µs ≠ λ0` is dropped (the `η_i` may vanish) and (1) is not restated for
`R(X,Y)Z` (a tensor is determined by its Jacobi operators). -/
axiom nik2006_prop_2_1 (R : CurvTensor 16) (hO : R.IsOsserman)
    (h9 : ∃ μ : ℝ, ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ = 9) :
    ∃ J : Fin 6 → Matrix (Fin 16) (Fin 16) ℝ, IsCliffordStr J ∧ ∃ (l0 : ℝ) (η : Fin 6 → ℝ),
      ∀ x, R.jacobi x = l0 • Pi x + ∑ i, η i • vecMulVec (J i *ᵥ x) (J i *ᵥ x)

end Osserman.Cited
