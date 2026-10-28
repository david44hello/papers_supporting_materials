/-
Matsaev/Defs/Scalar.lean — the real-valued functions of the paper (trust surface).
Paper: "Matsaev's (1971) conjecture is false for every p != 2", Dave Goel,
short v2.00 (md5 a9b3c6be).

Conventions. `p : ℝ` is the exponent; powers `x ^ p` are `Real.rpow` and are only ever applied to `|x| ≥ 0`
or to `t ≥ 0`. A vector of ℝ² is written as two reals `u v` (the paper's w = (w₁, w₂) = (u, v)).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Matsaev

open Real

/-- The paper's `φ(y) = sgn y · |y|^(p-1)` (Section 2, notation), one coordinate. -/
noncomputable def phi (p y : ℝ) : ℝ := (SignType.sign y : ℝ) * |y| ^ (p - 1)

/-- The paper's `Q(w) = ⟨φ(w), Jw⟩ / ‖w‖_p^p` (Section 3, before Lemma 3.4) for `w = (u, v)`, where `J(u, v) = (v, -u)`, so
`⟨φ(w), Jw⟩ = φ(u)·v + φ(v)·(-u)` and `‖w‖_p^p = |u|^p + |v|^p`. -/
noncomputable def Qf (p u v : ℝ) : ℝ := (phi p u * v - phi p v * u) / (|u| ^ p + |v| ^ p)

/-- The paper's `d(t) = (t - t^(p-1)) / (1 + t^p)` (Section 3, before Lemma 3.4), used for `t ∈ (0, 1)`. For `t < 0` the value is junk
(`Real.rpow` of a negative base); no statement uses it there. -/
noncomputable def dfun (p t : ℝ) : ℝ := (t - t ^ (p - 1)) / (1 + t ^ p)

/-- The paper's `D_* := max_{w ≠ 0} Q(w)` (Lemma 3.4, `lem:N1`), defined here as the supremum of `Q` over `ℝ² \ {0}`.
Lemma 3.4 (`Matsaev.Paper.lemma_3_4`) proves that the set is bounded above and the supremum is attained. -/
noncomputable def Dstar (p : ℝ) : ℝ := sSup {q : ℝ | ∃ u v : ℝ, (u, v) ≠ (0, 0) ∧ Qf p u v = q}

/-- The paper's window function `F` of the Bellman bound (Lemma 3.1, eq. `eq:bellman`) for `P_a(z) = 1 + a z - B z²`
and the window `(u, v, w) = (x_n, x_{n-1}, x_{n-2})`:
`F(u, v, w) = C^p |u|^p + G(v, w) - G(u, v) - |u + a v - B w|^p`. -/
noncomputable def bellmanF (p a B C : ℝ) (G : ℝ → ℝ → ℝ) (u v w : ℝ) : ℝ :=
  C ^ p * |u| ^ p + G v w - G u v - |u + a * v - B * w| ^ p

/-- The paper's `G₀(s, t) = B (1 + B)^(p-1) (|s|^p + |t|^p)` (Lemma 3.2, `lem:B0`). -/
noncomputable def G0 (p B s t : ℝ) : ℝ := B * (1 + B) ^ (p - 1) * (|s| ^ p + |t| ^ p)

/-- The paper's `F₀(u, v, w) = f(u, w) = (1 + B)^(p-1) (|u|^p + B |w|^p) - |u - B w|^p` (Lemma 3.2, `lem:B0`;
Lemma 3.3, `lem:B0q`). It does not depend on `v`. -/
noncomputable def F0 (p B u w : ℝ) : ℝ := (1 + B) ^ (p - 1) * (|u| ^ p + B * |w| ^ p) - |u - B * w| ^ p

/-- The rotation `J = [[0, 1], [-1, 0]]` (Section 1, idea of the proof of Theorem A): `J (u, v) = (v, -u)`. Over any commutative ring. -/
def Jmat {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- The paper's `K_* = ½ (J - D_* I)` (Lemma 4.1, `lem:TK`). -/
noncomputable def Kstar (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (1 / 2 : ℝ) • (Jmat - Dstar p • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- The rotation `R_θ = exp(θ J) = cos θ · I + sin θ · J` (proof of Lemma 4.1). -/
noncomputable def Rot (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin θ • Jmat

/-- The paper's `T_ε = exp(ε K_*) J` (Lemma 4.1, `lem:TK`), written in its closed form
`exp(ε K_*) = e^(-ε D_*/2) R_(ε/2)` (proof of Lemma 4.1). `Matsaev.Paper.teps_eq_exp` proves that this equals
`NormedSpace.exp (ε • Kstar p) * Jmat`. -/
noncomputable def Teps (p ε : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Real.exp (-(ε * Dstar p / 2)) • Rot (ε / 2) * Jmat

end Matsaev
