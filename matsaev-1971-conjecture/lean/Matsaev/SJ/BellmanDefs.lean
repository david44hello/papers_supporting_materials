-- Matsaev/SJ/BellmanDefs.lean — shared DEFINITIONS for Steps F-I of Theorem 3.6 (the Bellman function for small a).
-- Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
import Mathlib
import Matsaev.Defs.Scalar

/-!
# The Bellman function of Theorem 3.6 (`thm:SJ`), our route

Notation: `q` is the real exponent (the paper's `p > 2`), `A = 1 + B`, `ψ(x) = |x|^q`, `φ = phi q`, `C = C_a = ‖P_a(J)‖_q`.

* The paper's Bellman function (Theorem 3.6, Step 2; the paper writes `Δ_a` for `D_a`) is `G = G₀ + ½ D_a + λ₁ k₁ + λ₂ k₂`, with `D_a(s,t) = C^q|s|^q - |A s + a t|^q`,
  `k₁(s,t) = (s² + t²)^(q/2)`, `k₂(s,t) = |s|^q + |t|^q` (`Gab`).
* By `q`-homogeneity it suffices to check the window function `F(u, v, w)` (`bellmanF`) at `s = 0` and on the unit circle
  `(u, v) = (cos θ, sin θ)`. There we write `w = -u + ν` (`ν` = distance from the plane `Π = {w = -u}`): `fcirc θ ν`.
* `fcirc θ ν = F₀(u, -u + ν) + Σ_a(θ)/4 + Δ(u, v, ν)` (the decomposition; `Δ = DeltaUV`, `Δ(u, v, 0) = 0`).
  `F₀ ≥ c₁ (|u| + |ν|)^(q-2) ν²` is Lemma 3.3; `Σ_a ≥ 0` is eq. `eq:Sigma`.
* `Δ(u, v, ν) = q ν n(u, v) + O(a ν²)` near the extremal angles, where `n = nUV` is `N_a(s)/q` (Theorem 3.6, Step 4):
  `n(u, v) = B(φ(A u + a v) - φ(A u)) - (a/2) φ(A v - a u) - λ₁ u - λ₂ φ(u)`.
* The paper's choice of `λ` (Theorem 3.6, Step 4) makes `n = 0` at `s_a = (u, v)` and at `J s_a`... here at `(v, -u) = e(θ_a - π/2)`:
  `λ = (lam1, lam2)` solves the 2×2 system `[[u, φ u], [v, φ v]] λ = (R1, R2)` (Cramer, determinant `detL`).
-/

namespace Matsaev.SJ

open Real

/-- `k₁(s, t) = (s² + t²)^(q/2)` (Theorem 3.6, Step 2). -/
noncomputable def k1 (q s t : ℝ) : ℝ := (s ^ 2 + t ^ 2) ^ (q / 2)

/-- `k₂(s, t) = |s|^q + |t|^q` (Theorem 3.6, Step 2). -/
noncomputable def k2 (q s t : ℝ) : ℝ := |s| ^ q + |t| ^ q

/-- `D_a(s, t) = C^q |s|^q - |(1 + B) s + a t|^q` (the paper's `Δ_a`, Theorem 3.6, Step 1). -/
noncomputable def Da (q a B C s t : ℝ) : ℝ := C ^ q * |s| ^ q - |(1 + B) * s + a * t| ^ q

/-- The Bellman function `G_{a,λ} = G₀ + ½ D_a + λ₁ k₁ + λ₂ k₂` (Theorem 3.6, Step 2). -/
noncomputable def Gab (q a B C l1 l2 : ℝ) (s t : ℝ) : ℝ :=
  G0 q B s t + Da q a B C s t / 2 + l1 * k1 q s t + l2 * k2 q s t

/-- The window function on the unit circle: `f(θ, ν) = F(cos θ, sin θ, -cos θ + ν)` with `G = G_{a,λ}`. -/
noncomputable def fcirc (q a B C l1 l2 θ ν : ℝ) : ℝ :=
  bellmanF q a B C (Gab q a B C l1 l2) (Real.cos θ) (Real.sin θ) (-Real.cos θ + ν)

/-- `Δ(u, v, ν)`: the part of `f(θ, ν) - F₀(u, -u + ν) - Σ_a(θ)/4` (`u = cos θ`, `v = sin θ`); it does not involve `C`. -/
noncomputable def DeltaUV (q a B l1 l2 u v ν : ℝ) : ℝ :=
  ((|(1 + B) * u + a * v| ^ q - |(1 + B) * u + a * v - B * ν| ^ q) - (|(1 + B) * u| ^ q - |(1 + B) * u - B * ν| ^ q))
    + (|(1 + B) * v - a * u| ^ q - |(1 + B) * v - a * u + a * ν| ^ q) / 2
    + l1 * (k1 q v (-u + ν) - 1) + l2 * (|-u + ν| ^ q - |u| ^ q)

/-- `R₁(u, v) = B(φ(A u + a v) - φ(A u)) - (a/2) φ(A v - a u)`: the `λ`-free part of `n(u, v)`. -/
noncomputable def R1 (q a B u v : ℝ) : ℝ :=
  B * (phi q ((1 + B) * u + a * v) - phi q ((1 + B) * u)) - a / 2 * phi q ((1 + B) * v - a * u)

/-- `R₂(u, v) = B(φ(A v - a u) - φ(A v)) + (a/2) φ(A u + a v)`; it equals `R₁(v, -u)` (φ is odd). -/
noncomputable def R2 (q a B u v : ℝ) : ℝ :=
  B * (phi q ((1 + B) * v - a * u) - phi q ((1 + B) * v)) + a / 2 * phi q ((1 + B) * u + a * v)

/-- `n(u, v) = N_a(u, v)/q = R₁(u, v) - λ₁ u - λ₂ φ(u)`: the normal derivative `∂_ν f(θ, 0)` divided by `q`. -/
noncomputable def nUV (q a B l1 l2 u v : ℝ) : ℝ := R1 q a B u v - l1 * u - l2 * phi q u

/-- The determinant of the 2×2 system for `λ` (Step 4): `det [[u, φ u], [v, φ v]] = u φ(v) - v φ(u)`. -/
noncomputable def detL (q u v : ℝ) : ℝ := u * phi q v - v * phi q u

/-- `λ₁` by Cramer's rule: the solution of `λ₁ u + λ₂ φ(u) = R₁`, `λ₁ v + λ₂ φ(v) = R₂`. -/
noncomputable def lam1 (q a B u v : ℝ) : ℝ := (R1 q a B u v * phi q v - R2 q a B u v * phi q u) / detL q u v

/-- `λ₂` by Cramer's rule. -/
noncomputable def lam2 (q a B u v : ℝ) : ℝ := (u * R2 q a B u v - v * R1 q a B u v) / detL q u v

end Matsaev.SJ
