/-
NagataHigman/Defs/TwoCornerSteps.lean — the operators of the paper's proof of Lemma 4.2, steps (a)-(c) (tex 441, 470-483):
`Q± = (1 ± Y_top)/2`, `D = Q₊ Y_k Q₊ + Q₋ Y_k Q₋`, and the function `g(x, y) = x + 1/(y - x)` of step (c).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Indices are 0-based: `top = N-1` and `k = N-2` here are the paper's `N` and `N-1`; `Y_j = ρ_λ(X^{(j)})` with
`X^{(j)} = starElem F j`. Proofs about these operators: Proofs/TwoCorner/Lemma42Steps.lean.
-/
import NagataHigman.Defs.YoungSystem

noncomputable section

namespace NagataHigman

open Matrix

variable {F : Type*} [Field F] {N : ℕ}

/-- The paper's `g(x, y) = x + 1/(y - x)` (Lemma 4.2 (c), tex 482): `D v_T = g(c_T(N-1), c_T(N)) v_T`. -/
def lem42g (x y : F) : F := x + 1 / (y - x)

variable (Y : YoungSystem F N)

/-- `Q₊ = (1 + Y_N)/2` (defined at tex 441; Lemma 4.2 (a), tex 472; here `Y_N = Y_top = ρ_λ(X^{(top)})`). -/
def projPlus (lam : Shape N) (top : Fin N) : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F :=
  (1 / 2 : F) • (1 + Y.rhoAlg lam (starElem F top))

/-- `Q₋ = (1 - Y_N)/2` (defined at tex 441; Lemma 4.2 (a), tex 472). -/
def projMinus (lam : Shape N) (top : Fin N) : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F :=
  (1 / 2 : F) • (1 - Y.rhoAlg lam (starElem F top))

/-- `D = Q₊ Y_{N-1} Q₊ + Q₋ Y_{N-1} Q₋` (Lemma 4.2 (c), tex 474; here `Y_{N-1} = Y_k`). -/
def stepD (lam : Shape N) (k top : Fin N) : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F :=
  projPlus Y lam top * Y.rhoAlg lam (starElem F k) * projPlus Y lam top +
    projMinus Y lam top * Y.rhoAlg lam (starElem F k) * projMinus Y lam top

end NagataHigman

end
