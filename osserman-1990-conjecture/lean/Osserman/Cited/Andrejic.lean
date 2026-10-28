/-
Osserman/Cited/Andrejic.lean — the cited theorem of V. Andrejić used by paper 013 (Corollary D, P013_short.tex
l. 834-841): a Riemannian Jacobi-proportional non-Clifford tensor has multiplicities (8,7) or (7,7,1). Stated as its
source states it, or weaker (n = 16). Checked against the source.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.ThreeRoot

namespace Osserman.Cited

open Matrix Osserman

/-- **[AL2023, Theorem 3, p. 8470] = [And2022, Theorem 5]**. V. Andrejić, K. Lukić, "On the existence of a curvature
tensor for given Jacobi operators", Filomat 37:25 (2023) 8465-8471, doi:10.2298/FIL2325465A (refereed journal;
received 14 Sep 2022, accepted 28 Oct 2022); V. Andrejić, "The proportionality
principle for Osserman manifolds", J. Geom. Phys. 176 (2022) 104516 (refereed journal; paywalled, its abstract states
the same result). Cited at lines 835-838 of P013_short.tex (Corollary D, proof).
Source text (p. 8470): "Theorem 3. If R is a Riemannian Jacobi-proportional algebraic curvature tensor which is not
Clifford then R is 2-root with multiplicities 8 and 7, or it is 3-root with multiplicities 7, 7, and 1."
Source definitions (p. 8469): "We say that R is Osserman if the polynomial det(λ Id − J_X/ε_X) is independent of a
nonnull X ∈ V. More generally, we say that R is k-root if J̃_X has exactly k distinct eigenvalues ... We say that a
Jacobi-diagonalizable k-root Osserman R is Jacobi-proportional if for any pair of nonnull vectors X, Y ∈ V we have the
proportionality ε_X(ε_{Y_0}, ε_{Y_1}, ..., ε_{Y_k}) = ε_Y(ε_{X_0}, ε_{X_1}, ..., ε_{X_k}), where X = Σ X_i and
Y = Σ Y_j are decomposed such that X_i ∈ V_i(Y) and Y_j ∈ V_j(X)", with V_i(X) = ker(J̃_X − ε_Xλ_i Id) (1 ≤ i ≤ k)
and V_0(X) = Span{X}; (p. 8470) "If all J_i are complex structures (J_i² = −Id) then we say that R is Clifford."
Lean form (weaker: n = 16 only). ε_{Y_i} = ⟨π_i(X)Y, Y⟩, and the i = 0 component always holds
(ε_Xε_{Y_0} = ⟨X,Y⟩² = ε_Yε_{X_0}), so for Osserman R the source's condition is `IsJacobiProportional`. The source's
"Clifford" (R = μ_0R_1 + Σμ_iR^{J_i}, with J_X(R^J) = −3(JX)(JX)ᵀ) is `IsClifford`. "2-root with multiplicities 8 and
7" / "3-root with multiplicities 7, 7, and 1" is `HasPattern` (the multiplicities fill X^⊥, so these are all the
eigenvalues). The source has no hypothesis on k (paper l. 838-839). -/
axiom andrejic_thm5 (R : CurvTensor 16) (hO : R.IsOsserman) (hJP : IsJacobiProportional R)
    (hnc : ¬ R.IsClifford) : HasPattern R ![8, 7] ∨ HasPattern R ![7, 7, 1]

end Osserman.Cited
