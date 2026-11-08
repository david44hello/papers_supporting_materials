/-
Smale/Defs/Basic.lean — the definitions of paper 009 "Smale's mean value constant exceeds 1.1559" (Dave Goel,
v2.90, tex md5 68d80e57): the class 𝓟_d, m(p), K(d), K*; univalent maps and the class 𝒮; Blaschke factors and finite
Blaschke products; admissible pairs (Def. 2.1 = [JN, Def. 1.1]); J(a, b); the disk automorphism φ_b; the
construction of Lemma 3.1; Dieudonné polynomials P_c and P_c*; the reversed polynomial f* and the Schur transform T.
TRUST SURFACE: every definition cites its lines in that tex file and was reviewed against the paper.
-/
import Mathlib

namespace Smale

open Polynomial Complex Metric ComplexConjugate

/-! ### Smale's mean value constant (tex l.70-81) -/

/-- The open unit disk `𝔻 = {|w| < 1}` (tex l.173). -/
abbrev disk : Set ℂ := ball (0 : ℂ) 1

/-- The closed unit disk `𝔻̄` (tex l.289, l.307). -/
abbrev closedDisk : Set ℂ := closedBall (0 : ℂ) 1

/-- `p ∈ 𝓟_d` (tex l.70): a complex polynomial of degree `d` with `p(0) = 0` and `p'(0) = 1`. -/
def IsPd (d : ℕ) (p : ℂ[X]) : Prop :=
  p.natDegree = d ∧ p.eval 0 = 0 ∧ p.derivative.eval 0 = 1

/-- The numbers `|p(β)|/|β|` over the critical points `β` of `p` (tex l.73). -/
def critRatios (p : ℂ[X]) : Set ℝ :=
  {r | ∃ β : ℂ, p.derivative.eval β = 0 ∧ r = ‖p.eval β‖ / ‖β‖}

/-- `m(p) = min_{p'(β) = 0} |p(β)|/|β|` (tex l.73). For `p ∈ 𝓟_d` with `d ≥ 2` the set `critRatios p` is finite and
nonempty, so this infimum is attained (claim `sec1_m_attained`). -/
noncomputable def mval (p : ℂ[X]) : ℝ := sInf (critRatios p)

/-- `K(d) = sup_{p ∈ 𝓟_d} m(p)` (tex l.73). Taken in `EReal`, where every supremum exists (that `K(d) ≤ 4` is Smale's
theorem [Smale1981], background the proof does not use). -/
noncomputable def Kd (d : ℕ) : EReal := ⨆ p : {p : ℂ[X] // IsPd d p}, ((mval p.1 : ℝ) : EReal)

/-- Smale's mean value constant `K* = sup_{d ≥ 2} K(d)` (tex l.73). -/
noncomputable def Kstar : EReal := ⨆ d : {d : ℕ // 2 ≤ d}, Kd d.1

/-- The normalized polynomial `p(u) = (P(z + u) - P(z))/P'(z)` of `P` at `z` (tex l.75). -/
noncomputable def normalizeAt (P : ℂ[X]) (z : ℂ) : ℂ[X] :=
  C (P.derivative.eval z)⁻¹ * (P.comp (X + C z) - C (P.eval z))

/-! ### Univalent maps, Blaschke products, admissible pairs (tex l.171-187) -/

/-- `W` is univalent (holomorphic and injective) on `S` (tex l.173). -/
def IsUnivalentOn (W : ℂ → ℂ) (S : Set ℂ) : Prop := DifferentiableOn ℂ W S ∧ Set.InjOn W S

/-- `W ∈ 𝒮` (tex l.173): univalent on `𝔻`, `W(0) = 0`, `W'(0) = 1`. -/
def InClassS (W : ℂ → ℂ) : Prop := IsUnivalentOn W disk ∧ W 0 = 0 ∧ deriv W 0 = 1

/-- The Blaschke factor `B_a(w) = (w - a)/(1 - ā w)` (tex l.174). -/
noncomputable def blaschkeFactor (a w : ℂ) : ℂ := (w - a) / (1 - conj a * w)

/-- `λ B_{a₁} ⋯ B_{a_k}` (tex l.174-175). -/
noncomputable def blaschkeProd (lam : ℂ) (as : List ℂ) (w : ℂ) : ℂ :=
  lam * (as.map fun a => blaschkeFactor a w).prod

/-- `B` is a finite Blaschke product of degree `k` (tex l.174-175): `B = λ B_{a₁} ⋯ B_{a_k}` on `𝔻` with `|λ| = 1`
and `a₁, …, a_k ∈ 𝔻`. -/
def IsFiniteBlaschke (B : ℂ → ℂ) (k : ℕ) : Prop :=
  ∃ lam : ℂ, ∃ as : List ℂ, ‖lam‖ = 1 ∧ as.length = k ∧ (∀ a ∈ as, a ∈ disk) ∧ Set.EqOn B (blaschkeProd lam as) disk

/-- `B(0) > 0`: a positive real number (tex l.178). -/
def PosAtZero (B : ℂ → ℂ) : Prop := (B 0).im = 0 ∧ 0 < (B 0).re

/-- An admissible pair with `deg B = k` (Def. 2.1 = [JN, Def. 1.1], tex l.177-181): `W ∈ 𝒮`, `B` a finite Blaschke
product of degree `k` with `B(0) > 0`, and `(WB)'` has no zero in the OPEN disk `𝔻` (tex l.191). -/
def IsAdmissible (W B : ℂ → ℂ) (k : ℕ) : Prop :=
  InClassS W ∧ IsFiniteBlaschke B k ∧ PosAtZero B ∧ ∀ w ∈ disk, deriv (fun z => W z * B z) w ≠ 0

/-- `𝓑_d`, the supremum of `1/B(0)` over the admissible pairs with `deg B ≤ d` (tex l.179-180), in `EReal`. -/
noncomputable def Bcal (d : ℕ) : EReal :=
  sSup {x : EReal | ∃ (W B : ℂ → ℂ) (k : ℕ), k ≤ d ∧ IsAdmissible W B k ∧ x = ((1 / (B 0).re : ℝ) : EReal)}

/-! ### The construction of Section 3 (tex l.220-263) -/

/-- `J(a, b) = 1 + (1 - |a|²)(1 - |b|²)/|a - b|²` (tex l.222-225). -/
noncomputable def Jab (a b : ℂ) : ℝ := 1 + (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2

/-- The disk automorphism `φ_b(w) = (w + b)/(1 + b̄ w)` (tex l.226-227). -/
noncomputable def diskAut (b w : ℂ) : ℂ := (w + b) / (1 + conj b * w)

/-- `∏_j (z - a_j)`. -/
noncomputable def zerosPoly (as : List ℂ) : ℂ[X] := (as.map fun a => X - C a).prod

/-- `∏_j (1 - ā_j z)`. -/
noncomputable def reflPoly (as : List ℂ) : ℂ[X] := (as.map fun a => 1 - C (conj a) * X).prod

/-- `H = Q ∏_j (1 - ā_j z)/(z - a_j)` (tex l.240, l.324), as the polynomial quotient; the division is exact when the
`a_j` are distinct zeros of `Q` (claim `lem_3_1_H_poly`). -/
noncomputable def Hpoly (Q : ℂ[X]) (as : List ℂ) : ℂ[X] := (Q * reflPoly as) /ₘ zerosPoly as

/-- `η = ∏_j B_{a_j}(b)` (tex l.242). -/
noncomputable def etaOf (as : List ℂ) (b : ℂ) : ℂ := (as.map fun a => blaschkeFactor a b).prod

/-- `N = (1 - |b|²) H'(b)` (tex l.242). -/
noncomputable def NOf (Q : ℂ[X]) (as : List ℂ) (b : ℂ) : ℂ :=
  (1 - (‖b‖ : ℂ) ^ 2) * (Hpoly Q as).derivative.eval b

/-- `W = (H ∘ φ)/N` (tex l.244). -/
noncomputable def WOf (Q : ℂ[X]) (as : List ℂ) (b : ℂ) (w : ℂ) : ℂ :=
  (Hpoly Q as).eval (diskAut b w) / NOf Q as b

/-- `B = (|η|/η) ∏_j B_{a_j} ∘ φ` (tex l.244). -/
noncomputable def BOf (as : List ℂ) (b : ℂ) (w : ℂ) : ℂ :=
  ((‖etaOf as b‖ : ℂ) / etaOf as b) * (as.map fun a => blaschkeFactor a (diskAut b w)).prod

/-! ### Section 4: Dieudonné polynomials, f*, Schur–Cohn (tex l.265-355) -/

/-- The Dieudonné polynomial `P_c(w) = Σ_{ℓ=1}^n h_ℓ U_{ℓ-1}(c) w^{ℓ-1}` of `H = Σ h_ℓ z^ℓ` at formal degree `n`
(tex l.271-275, l.328), `U` the Chebyshev polynomials of the second kind. -/
noncomputable def dieudonne (H : ℂ[X]) (n : ℕ) (c : ℝ) : ℂ[X] :=
  ∑ l ∈ Finset.range n, C (H.coeff (l + 1) * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)) * X ^ l

/-- `P_c*(w) = Σ_{ℓ=1}^n h̄_ℓ U_{ℓ-1}(c) w^{n-ℓ}` (tex l.333). -/
noncomputable def dieudonneStar (H : ℂ[X]) (n : ℕ) (c : ℝ) : ℂ[X] :=
  ∑ l ∈ Finset.range n, C (conj (H.coeff (l + 1)) * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)) * X ^ (n - 1 - l)

/-- `f*(w) = w^n \overline{f(1/w̄)} = Σ_{ℓ=0}^n ē_{n-ℓ} w^ℓ` at formal degree `n` (tex l.300-301). -/
noncomputable def conjRev (f : ℂ[X]) (n : ℕ) : ℂ[X] :=
  ∑ l ∈ Finset.range (n + 1), C (conj (f.coeff (n - l))) * X ^ l

/-- The Schur transform `Tf = ē₀ f - e_n f*` at formal degree `n` (tex l.304). -/
noncomputable def schurT (f : ℂ[X]) (n : ℕ) : ℂ[X] := C (conj (f.coeff 0)) * f - C (f.coeff n) * conjRev f n

/-- `f₀ = f`, `f_j = T f_{j-1}` (tex l.306), `f_{j-1}` taken at formal degree `n - j + 1`. -/
noncomputable def schurSeq (f : ℂ[X]) (n : ℕ) : ℕ → ℂ[X]
  | 0 => f
  | j + 1 => schurT (schurSeq f n j) (n - j)

/-- `δ_j`, the constant term of `f_j` (tex l.306). -/
noncomputable def schurDelta (f : ℂ[X]) (n : ℕ) (j : ℕ) : ℂ := (schurSeq f n j).coeff 0

/-- The number of zeros of `f` in the open disk `|w - z₀| < r`, counted with multiplicity. -/
noncomputable def zerosInBall (f : ℂ[X]) (z₀ : ℂ) (r : ℝ) : ℕ := (f.roots.filter fun w => ‖w - z₀‖ < r).card

/-- The number of zeros of `f` in `𝔻`, counted with multiplicity (tex l.305-306, l.295). -/
noncomputable def zerosInDisk (f : ℂ[X]) : ℕ := zerosInBall f 0 1

/-! ### Section 5: integrals of polynomials (tex l.384-393) -/

/-- The antiderivative `∫_0^z P(t) dt = Σ_k p_k z^{k+1}/(k+1)` of a polynomial. -/
noncomputable def antideriv (P : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (P.natDegree + 1), C (P.coeff k / ((k : ℂ) + 1)) * X ^ (k + 1)

/-- `∫_u^v P(t) dt` for a polynomial `P` (path independent; tex l.387, l.392). -/
noncomputable def polyInt (P : ℂ[X]) (u v : ℂ) : ℂ := (antideriv P).eval v - (antideriv P).eval u

end Smale
