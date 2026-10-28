/-
Osserman/Cited/Nik2005.lean — one cited result of Y. Nikolayevsky used by paper 013 (Section 8, the endpoint (10,4,1)):
Proposition 1 of "Osserman Conjecture in dimension n ≠ 8, 16", stated as its source states it, or weaker (n = 16).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots

namespace Osserman.Cited

open Matrix Osserman

/-- **[Nik2005, Proposition 1]** = Y. Nikolayevsky, "Osserman Conjecture in dimension n ≠ 8, 16", Math. Ann. 331
(2005) 505-522 (refereed journal), Proposition 1. Read in its arXiv version math/0204258v2 (10 Oct 2002), p. 3; the journal version was not available.
Cited at lines 290-291 of sec_small_roots.tex (posting copy) ("[Nik2005, Proposition~1] for $(10,4,1)$ (in the notation of
[Nik2005, Proposition~1], $m=10$ and $\nu=5$ satisfy $16\ge3\nu$ and $16>(\nu+1)^2/4$)").
Source text (arXiv version, p. 3): "Proposition 1. Let R be an Osserman algebraic curvature tensor in Rn. Let m be the maximal
multiplicity of the eigenvalues of its Jacobi operator and ν = n − 1 − m. If n ≥ 3ν and n > (ν + 1)²/4, then R has a
Cliff(ν)-structure." Definition 3 (p. 2): "An algebraic curvature tensor R in Rn has a Cliff(ν)-structure if
R(X,Y)Z = λ0(⟨X,Z⟩Y − ⟨Y,Z⟩X) + ∑_{s=1}^ν (1/3)(µs − λ0)(2⟨JsX,Y⟩JsZ + ⟨JsZ,Y⟩JsX − ⟨JsZ,X⟩JsY), (1) where J1, ..., Jν
are skew-symmetric orthogonal operators satisfying the Hurwitz relations JsJq + JqJs = −2δqs In and µs ≠ λ0."
Conventions (p. 1): "the Jacobi operator RX : Rn → Rn is defined by RX Y = R(X,Y)X ... "eigenvalues of the
Jacobi operator" refers to eigenvalues of the restriction of RX, with X a unit vector, to the subspace X⊥" — so the
source's multiplicities are our reduced multiplicities `redMult`, and its Jacobi operator is minus ours (`J_x =
R(·,x)x`); multiplicities, "Osserman" and the Clifford shape do not change with the sign.
Lean form (n = 16 only; WEAKER than the source): `m` is the maximal reduced multiplicity (attained by `μ₀`), `ν = 15 - m`;
the conclusion keeps only the Jacobi operators of (1), `J_x = l₀Π(x) + ∑ η_i (J_ix)(J_ix)ᵀ`, drops `µs ≠ λ0` (the `η_i`
may vanish) and does not restate (1) for `R(X,Y)Z` (a tensor is determined by its Jacobi operators). -/
axiom nik2005_prop_1 (R : CurvTensor 16) (hO : R.IsOsserman) (m : ℕ) (μ0 : ℝ)
    (hmax : ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ0 = m ∧ ∀ μ : ℝ, R.redMult x μ ≤ m)
    (hν1 : (16 : ℝ) ≥ 3 * ((15 - m : ℕ) : ℝ)) (hν2 : (16 : ℝ) > (((15 - m : ℕ) : ℝ) + 1) ^ 2 / 4) :
    ∃ J : Fin (15 - m) → Matrix (Fin 16) (Fin 16) ℝ, IsCliffordStr J ∧ ∃ (l0 : ℝ) (η : Fin (15 - m) → ℝ),
      ∀ x, R.jacobi x = l0 • Pi x + ∑ i, η i • vecMulVec (J i *ᵥ x) (J i *ᵥ x)

end Osserman.Cited
