/-
Smale/Paper/Statements.lean — every claim of paper 009 "Smale's mean value constant exceeds 1.1559" (Dave Goel, posted
v1.80, tex md5 6863fded; its lines 1-485 are those of v1.40-v1.70), in the paper's order, each with its lines in that tex
file ("tex l."). Bodies link to proofs in other files.
Sentences NOT stated here (background citations of other papers, program descriptions, history) are listed with reasons
at the end of this file; each is listed for the author's review.
## (older version lines: in the header of versions/Statements_version_1.41.lean)
-/
import Smale.Defs.Data
import Smale.Cited.Basic
import Smale.Defs.Conditions
import Smale.Proofs.Sec1Best
import Smale.Proofs.Lemma31
import Smale.Proofs.Sec2
import Smale.Proofs.Sec1Exact
import Smale.Proofs.DataCrit
import Smale.Proofs.Parity
import Smale.Proofs.Lem43
import Smale.Proofs.Lemma53
import Smale.Proofs.Sec4More
import Smale.Proofs.ResScaling
import Smale.Proofs.SchurCertH
import Smale.Proofs.SchurCertV
import Smale.Proofs.DataOrder5
import Smale.Proofs.DataRoots
import Smale.Proofs.DataGUnique
import Smale.Proofs.DataSec5
import Smale.Proofs.DataFacts
import Smale.Proofs.Star
import Smale.Proofs.Count
import Smale.Proofs.Schur
import Smale.Proofs.Dieudonne
import Smale.Proofs.Hpoly
import Smale.Proofs.Disk
import Smale.Proofs.TextClaims
import Smale.Proofs.Margins
import Smale.Proofs.ResDegree
import Smale.Proofs.Lemma53More
import Smale.Proofs.Rem23More
import Smale.Proofs.Hurwitz

namespace Smale

open Polynomial Complex Metric Filter Topology ComplexConjugate

/-! ## Section 1: Smale's mean value problem (tex l.46-133) -/

/-- tex l.52-53: every critical point of `p ∈ 𝓟_d` is nonzero, as `p'(0) = 1`. -/
theorem sec1_crit_ne_zero (d : ℕ) (p : ℂ[X]) (hp : IsPd d p) (β : ℂ) (hβ : p.derivative.eval β = 0) : β ≠ 0 :=
  crit_ne_zero hp hβ

/-- tex l.55 ("min"): for `p ∈ 𝓟_d`, `d ≥ 2`, the set of the numbers `|p(β)|/|β|` is finite and nonempty, and `m(p)` is
its least element. -/
theorem sec1_m_attained (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    (critRatios p).Finite ∧ mval p ∈ critRatios p ∧ ∀ r ∈ critRatios p, mval p ≤ r :=
  sec1_m_attained_proved d hd p hp

/-- tex l.57-58: for `P` of degree `d ≥ 2` and `P'(z) ≠ 0`, `p(u) = (P(z+u) - P(z))/P'(z)` lies in `𝓟_d`, and its
critical points are the points `ζ - z` with `ζ` a critical point of `P`. -/
theorem sec1_normalize (d : ℕ) (hd : 2 ≤ d) (P : ℂ[X]) (hP : P.natDegree = d) (z : ℂ)
    (hz : P.derivative.eval z ≠ 0) :
    IsPd d (normalizeAt P z) ∧ ∀ β : ℂ, (normalizeAt P z).derivative.eval β = 0 ↔ P.derivative.eval (z + β) = 0 :=
  Sec1.sec1_normalize_proved d hd P hP z hz

/-- tex l.58-63: `K(d)` is the best constant `K` in (1.1) over all polynomials `P` of degree `d` and all `z` with
`P'(z) ≠ 0`: a real `K` satisfies (1.1) for all of them iff `K(d) ≤ K`. -/
theorem sec1_best_constant (d : ℕ) (hd : 2 ≤ d) (K : ℝ) :
    (∀ P : ℂ[X], P.natDegree = d → ∀ z : ℂ, P.derivative.eval z ≠ 0 →
      ∃ ζ : ℂ, P.derivative.eval ζ = 0 ∧ ‖(P.eval z - P.eval ζ) / (z - ζ)‖ ≤ K * ‖P.derivative.eval z‖) ↔
    Kd d ≤ (K : EReal) :=
  Sec1.sec1_best_constant_proved d hd K

/-- tex l.62: "`K*` is the best constant over all degrees": a real `K` satisfies (1.1) for every polynomial `P` of every
degree `d ≥ 2` and every `z` with `P'(z) ≠ 0` iff `K* ≤ K` (a polynomial of degree 1 has no critical point). -/
theorem sec1_best_constant_all (K : ℝ) :
    (∀ d : ℕ, 2 ≤ d → ∀ P : ℂ[X], P.natDegree = d → ∀ z : ℂ, P.derivative.eval z ≠ 0 →
      ∃ ζ : ℂ, P.derivative.eval ζ = 0 ∧ ‖(P.eval z - P.eval ζ) / (z - ζ)‖ ≤ K * ‖P.derivative.eval z‖) ↔
    Kstar ≤ (K : EReal) := by
  rw [Kstar, iSup_le_iff]
  exact ⟨fun h d => (sec1_best_constant d.1 d.2 K).1 (h d.1 d.2),
    fun h d hd => (sec1_best_constant d hd K).2 (h ⟨d, hd⟩)⟩

/-- tex l.66: `p = z - z^d/d` lies in `𝓟_d` and has `m(p) = (d-1)/d`, so `K(d) ≥ (d-1)/d`. -/
theorem sec1_example (d : ℕ) (hd : 2 ≤ d) :
    IsPd d (X - C (1 / (d : ℂ)) * X ^ d) ∧ mval (X - C (1 / (d : ℂ)) * X ^ d) = ((d : ℝ) - 1) / d ∧
      ((((d : ℝ) - 1) / d : ℝ) : EReal) ≤ Kd d := by
  apply Exact.sec1_example_proved <;> assumption

/-- tex l.66-67: the critical points `β` of `p = z - z^d/d` are the `(d-1)`-st roots of unity, and
`p(β)/β = 1 - β^{d-1}/d = (d-1)/d` at each. -/
theorem sec1_example_crit (d : ℕ) (hd : 2 ≤ d) (β : ℂ) :
    ((X - C (1 / (d : ℂ)) * X ^ d).derivative.eval β = 0 ↔ β ^ (d - 1) = 1) ∧
      (β ^ (d - 1) = 1 → (X - C (1 / (d : ℂ)) * X ^ d).eval β / β = 1 - β ^ (d - 1) / d ∧
        1 - β ^ (d - 1) / (d : ℂ) = ((d : ℂ) - 1) / d) :=
  sec1_example_crit_proved d hd β

/-- tex l.66: "Smale proved (1.1) with `K = 4`, so `K* ≤ 4`": the deduction, with Smale's theorem [Smale1981] (a cited
result, not assumed anywhere else) as the hypothesis. -/
theorem intro_smale_K4
    (hSmale : ∀ d : ℕ, 2 ≤ d → ∀ P : ℂ[X], P.natDegree = d → ∀ z : ℂ, P.derivative.eval z ≠ 0 →
      ∃ ζ : ℂ, P.derivative.eval ζ = 0 ∧ ‖(P.eval z - P.eval ζ) / (z - ζ)‖ ≤ 4 * ‖P.derivative.eval z‖) :
    Kstar ≤ ((4 : ℝ) : EReal) :=
  (sec1_best_constant_all 4).1 hSmale

/-- tex l.75-76: "All these bounds tend to `4` as `d → ∞`": `4^{(d-2)/(d-1)}` [BMN], `4(d-1)/(d+1)` [CFL] and
`4 - 2.263/√d` [Crane] (the bounds themselves are cited results, N1). -/
theorem intro_bounds_tend_to_4 :
    Tendsto (fun d : ℕ => (4 : ℝ) ^ (((d : ℝ) - 2) / ((d : ℝ) - 1))) atTop (𝓝 4) ∧
      Tendsto (fun d : ℕ => 4 * ((d : ℝ) - 1) / ((d : ℝ) + 1)) atTop (𝓝 4) ∧
      Tendsto (fun d : ℕ => 4 - 2.263 / Real.sqrt d) atTop (𝓝 4) :=
  intro_bounds_tend_to_4_proved

/-- tex l.81: "So Smale's conjecture is false": `K* > 1` (the cited 2026 result, here the hypothesis) gives `K* ≠ 1`. -/
theorem intro_conjecture_false (h : (1 : EReal) < Kstar) : Kstar ≠ 1 :=
  ne_of_gt h

/-- tex l.123-124: the bound `𝓑_d ≤ 4 - 0.00597/(d log d)` of [GoelLong] "improves the bound `4 - 529(log 2)²/(576d²)`
of [JN, Thm. 1.3] for `d ≥ 452`". The two bounds are other papers' results (N2); the COMPARISON is this paper's claim.
-/
theorem intro_improves_JN (d : ℕ) (hd : 452 ≤ d) :
    (4 : ℝ) - 0.00597 / (d * Real.log d) < 4 - 529 * Real.log 2 ^ 2 / (576 * (d : ℝ) ^ 2) := by
  apply Exact.intro_improves_JN_proved <;> assumption

/-- tex l.33, l.48-49, l.84: `√(8081/6656) = 1.1018586…` (truncated decimals), so the bound of [JN] exceeds `1.1018`,
and `1.1559837 > 1.1018586…` ("improving the bound 1.1018"). -/
theorem intro_JN_digits :
    (1.1018586 : ℝ) ≤ Real.sqrt (8081 / 6656) ∧ Real.sqrt (8081 / 6656) < 1.1018587 ∧
      (1.1018 : ℝ) < Real.sqrt (8081 / 6656) ∧ Real.sqrt (8081 / 6656) < 1.1559837 :=
  intro_JN_digits_proved

/-- tex l.122-123, the paper's reading of [JN, Thm. 1.3]: `√(8081/6656) ≤ 𝓑₁ < √(7/5)` gives `1.1018 < 𝓑₁ < 1.1833`
(the numbers), and `𝓑_d < 4 - 529(log 2)²/(576d²)` at `d = 2` "gives `𝓑₂ < 3.89`". -/
theorem intro_JN_B1_B2 :
    (1.1018 : ℝ) < Real.sqrt (8081 / 6656) ∧ Real.sqrt (7 / 5) < 1.1833 ∧
      (4 : ℝ) - 529 * Real.log 2 ^ 2 / (576 * 2 ^ 2) < 3.89 :=
  intro_JN_B1_B2_proved

/-! ## Section 2: admissible pairs (tex l.134-175) -/

/-- Theorem 2.2, "Hence" (tex l.149): `K* ≥ 1/B(0)` for every admissible pair (from [JN, Prop. 4.2]). -/
theorem thm_2_2_hence (W B : ℂ → ℂ) (k : ℕ) (hWB : IsAdmissible W B k) :
    ((1 / (B 0).re : ℝ) : EReal) ≤ Kstar :=
  thm_2_2_hence_proved W B k hWB

/-- Remark 2.3 (tex l.163-171; from the cited [JN, Prop. 3.1], `jatarNg_prop_3_1`): for `p ∈ 𝓟_d` with
`m(p) > 1` and `1 < R < m(p)`, there is an admissible pair with `1/B(0) = R` (in the paper, the pair `W = ψ/κ`,
`B = (q∘ψ)/R`; the Lean statement asserts the existence only). -/
theorem rem_2_3_pair (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (hm : 1 < mval p) (R : ℝ) (hR1 : 1 < R)
    (hRm : R < mval p) : ∃ (W B : ℂ → ℂ) (k : ℕ), IsAdmissible W B k ∧ 1 / (B 0).re = R :=
  rem_2_3_pair_proved d hd p hp hm R hR1 hRm

/-- Remark 2.3 (tex l.164-165, l.169-170), the steps that need no Riemann map: `q = p(w)/w` is a polynomial with
`q(0) = 1`, and every critical point `β` of `p` has `|q(β)| ≥ m(p)`. -/
theorem rem_2_3_q (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    p = X * (p /ₘ X) ∧ (p /ₘ X).eval 0 = 1 ∧ ∀ β : ℂ, p.derivative.eval β = 0 → mval p ≤ ‖(p /ₘ X).eval β‖ :=
  rem_2_3_q_proved d hd p hp

/-- Remark 2.3 (tex l.165-166), a step that needs no Riemann map: `{|q| < R}` is bounded (`q = p(w)/w` has degree
`d - 1 ≥ 1`), so its component `Ω` that contains `0` is bounded. -/
theorem rem_2_3_bounded (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (R : ℝ) :
    Bornology.IsBounded {w : ℂ | ‖(p /ₘ X).eval w‖ < R} :=
  rem_2_3_bounded_proved d hd p hp R

/-- Remark 2.3 (tex l.169-170): for `R < m(p)` every critical point of `p` lies outside `{|q| < R}`, so outside `Ω`. -/
theorem rem_2_3_crit_outside (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (R : ℝ) (hR : R < mval p)
    (β : ℂ) (hβ : p.derivative.eval β = 0) : β ∉ {w : ℂ | ‖(p /ₘ X).eval w‖ < R} :=
  rem_2_3_crit_outside_proved d hd p hp R hR β hβ

/-- Remark 2.3 (tex l.166-169), the formulas, with the Riemann map `ψ` of the paper as a parameter: for every `ψ`
with `ψ(0) = 0` and `ψ'(0) = κ ≠ 0`, the pair `W = ψ/κ`, `B = (q∘ψ)/R` has `W(0) = 0`, `W'(0) = 1`, `B(0) = 1/R`,
and `(WB)' = p'(ψ)ψ'/(κR)` wherever `ψ` is differentiable. -/
theorem rem_2_3_formulas (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (ψ : ℂ → ℂ) (κ R : ℝ)
    (hκ : κ ≠ 0) (hψ0 : ψ 0 = 0) (hψ' : HasDerivAt ψ κ 0) :
    (fun z => ψ z / κ) 0 = 0 ∧ deriv (fun z => ψ z / κ) 0 = 1 ∧ (fun z => (p /ₘ X).eval (ψ z) / R) 0 = 1 / R ∧
      ∀ w : ℂ, DifferentiableAt ℂ ψ w →
        deriv (fun z => ψ z / κ * ((p /ₘ X).eval (ψ z) / R)) w = p.derivative.eval (ψ w) * deriv ψ w / (κ * R) :=
  rem_2_3_formulas_proved d hd p hp ψ κ R hκ hψ0 hψ'

/-- Remark 2.3 (tex l.171-172): `W(w) = w`, `B = 1` is an admissible pair (`deg B = 0`), so `𝓑_k ≥ 1` for every `k`. -/
theorem rem_2_3_trivial : IsAdmissible (fun w => w) (fun _ => 1) 0 ∧ ∀ k : ℕ, (1 : EReal) ≤ Bcal k := by
  apply rem_2_3_trivial_proved <;> assumption

/-- Remark 2.3 (tex l.171-172): `m(p) ≤ sup_k 𝓑_k` for every `p ∈ 𝓟_d`, hence `K* ≤ sup_k 𝓑_k`. -/
theorem rem_2_3_Kstar_le :
    (∀ d : ℕ, 2 ≤ d → ∀ p : ℂ[X], IsPd d p → ((mval p : ℝ) : EReal) ≤ ⨆ k : ℕ, Bcal k) ∧
      Kstar ≤ ⨆ k : ℕ, Bcal k := by
  apply rem_2_3_Kstar_le_proved <;> assumption

/-- Theorem 2.2, "Moreover" (tex l.149; [JN, Thm. 1.2]): `K* = sup_d 𝓑_d` — here from `thm_2_2_hence` and Remark 2.3. -/
theorem thm_2_2_moreover : Kstar = ⨆ d : ℕ, Bcal d := by
  apply thm_2_2_moreover_proved <;> assumption

/-! ## Section 3: the construction (tex l.177-220) -/

/-- tex l.183: `|1 - āb|² - |a - b|² = (1 - |a|²)(1 - |b|²)` (for all `a, b`). -/
theorem sec3_J_identity (a b : ℂ) :
    ‖1 - conj a * b‖ ^ 2 - ‖a - b‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) :=
  sec3_J_identity_proved a b

/-- tex l.183: so `1/|B_a(b)|² = J(a, b)` for `a ≠ b` in `𝔻`. -/
theorem sec3_J (a b : ℂ) (ha : a ∈ disk) (hb : b ∈ disk) (hab : a ≠ b) :
    1 / ‖blaschkeFactor a b‖ ^ 2 = Jab a b :=
  sec3_J_proved a b ha hb hab

/-- tex l.183-184: `φ(w) = (w + b)/(1 + b̄w)` maps `𝔻` onto `𝔻`, with `φ(0) = b` and `φ'(0) = 1 - |b|²`. -/
theorem sec3_phi (b : ℂ) (hb : b ∈ disk) :
    Set.BijOn (diskAut b) disk disk ∧ diskAut b 0 = b ∧ deriv (diskAut b) 0 = 1 - (‖b‖ : ℂ) ^ 2 :=
  sec3_phi_proved b hb

/-- Lemma 3.1, first sentence of the proof (tex l.210): if `a₁, …, a_k` are distinct zeros of `Q`, then `H` is a
polynomial: `H ∏(z - a_j) = Q ∏(1 - ā_j z)`. -/
theorem lem_3_1_H_poly (Q : ℂ[X]) (as : List ℂ) (hnd : as.Nodup) (hz : ∀ a ∈ as, Q.eval a = 0) :
    Hpoly Q as * zerosPoly as = Q * reflPoly as :=
  lem_3_1_H_poly_proved Q as hnd hz

/-- Lemma 3.1, proof (tex l.212-213): for `a, b ∈ 𝔻`, `B_a ∘ φ` is `λ B_γ` on `𝔻` with `|λ| = 1`, `γ ∈ 𝔻`. -/
theorem lem_3_1_aut (a b : ℂ) (ha : a ∈ disk) (hb : b ∈ disk) :
    ∃ lam γ : ℂ, ‖lam‖ = 1 ∧ γ ∈ disk ∧ ∀ w ∈ disk, blaschkeFactor a (diskAut b w) = lam * blaschkeFactor γ w :=
  lem_3_1_aut_proved a b ha hb

/-- Lemma 3.1 (tex l.193-207): `Q'` has no zero in `𝔻`; `b, a₁, …, a_k` are `k + 1` distinct zeros of `Q` in `𝔻`; `H` is
univalent in `𝔻`. Then `(W, B)` is an admissible pair, `deg B = k`, and `1/B(0)² = ∏_j J(a_j, b)`. -/
theorem lem_3_1 (k : ℕ) (hk : 1 ≤ k) (Q : ℂ[X]) (b : ℂ) (as : List ℂ) (hlen : as.length = k)
    (hQ' : ∀ w ∈ disk, Q.derivative.eval w ≠ 0) (hnd : (b :: as).Nodup) (hin : ∀ a ∈ b :: as, a ∈ disk)
    (hzero : ∀ a ∈ b :: as, Q.eval a = 0) (huniv : IsUnivalentOn (fun z => (Hpoly Q as).eval z) disk) :
    IsAdmissible (WOf Q as b) (BOf as b) k ∧ 1 / (BOf as b 0).re ^ 2 = (as.map fun a => Jab a b).prod :=
  Lem31.lem_3_1_proved k hk Q b as hlen hQ' hnd hin hzero huniv

/-- Lemma 3.1, the displayed steps of the proof (tex l.213-217), under the hypotheses of Lemma 3.1: `B(0) = |η|`;
`WB = (|η|/(ηN)) Q∘φ` on `𝔻`; `(WB)' = (|η|/(ηN)) Q'(φ) φ'` on `𝔻`. -/
theorem lem_3_1_WB (k : ℕ) (hk : 1 ≤ k) (Q : ℂ[X]) (b : ℂ) (as : List ℂ) (hlen : as.length = k)
    (hQ' : ∀ w ∈ disk, Q.derivative.eval w ≠ 0) (hnd : (b :: as).Nodup) (hin : ∀ a ∈ b :: as, a ∈ disk)
    (hzero : ∀ a ∈ b :: as, Q.eval a = 0) (huniv : IsUnivalentOn (fun z => (Hpoly Q as).eval z) disk) :
    BOf as b 0 = (‖etaOf as b‖ : ℂ) ∧
      (∀ w ∈ disk, WOf Q as b w * BOf as b w =
        (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) * Q.eval (diskAut b w)) ∧
      ∀ w ∈ disk, deriv (fun z => WOf Q as b z * BOf as b z) w =
        (‖etaOf as b‖ : ℂ) / (etaOf as b * NOf Q as b) * Q.derivative.eval (diskAut b w) * deriv (diskAut b) w :=
  Lem31.lem_3_1_WB_proved k hk Q b as hlen hQ' hnd hin hzero huniv

/-! ## Section 4: reduction to finite checks (tex l.222-309) -/

/-- tex l.233: for `c = cos θ`, `H(ze^{iθ}) - H(ze^{-iθ}) = 2i sin θ · z P_c(z)` (`n ≥ deg H`). -/
theorem sec4_dieudonne_identity (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (θ : ℝ) (z : ℂ) :
    H.eval (z * exp (θ * I)) - H.eval (z * exp (-(θ * I))) =
      2 * I * Real.sin θ * z * (dieudonne H n (Real.cos θ)).eval z :=
  sec4_dieudonne_identity_proved H n hn θ z

/-- tex l.233-234: `P₁ = H'` and `P_c(0) = h₁` (`n ≥ deg H`, `n ≥ 1`). -/
theorem sec4_P_one (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (hn1 : 1 ≤ n) :
    dieudonne H n 1 = H.derivative ∧ ∀ c : ℝ, (dieudonne H n c).eval 0 = H.coeff 1 :=
  sec4_P_one_proved H n hn hn1

/-- tex l.234: `U_{ℓ-1}(-c) = (-1)^{ℓ-1} U_{ℓ-1}(c)` (here with `l = ℓ - 1`), hence `P_{-c}(w) = P_c(-w)`. -/
theorem sec4_P_neg (H : ℂ[X]) (n : ℕ) (c : ℝ) (w : ℂ) :
    (∀ l : ℕ, (Chebyshev.U ℝ (l : ℤ)).eval (-c) = (-1) ^ l * (Chebyshev.U ℝ (l : ℤ)).eval c) ∧
      (dieudonne H n (-c)).eval w = (dieudonne H n c).eval (-w) :=
  sec4_P_neg_proved H n c w

/-- tex l.235-236: "So if `-1 < c < 1` and `P_c(z) = 0` with `0 < |z| < 1`, then `H` takes the same value at the two
distinct points `ze^{±iθ}` of `𝔻`, and `H` is not univalent in `𝔻`" (`c = cos θ`, `θ = arccos c ∈ (0, π)`). -/
theorem sec4_P_zero_not_univalent (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (c : ℝ) (hc1 : -1 < c) (hc2 : c < 1)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : ‖z‖ < 1) (h0 : (dieudonne H n c).eval z = 0) :
    Real.cos (Real.arccos c) = c ∧ 0 < Real.arccos c ∧ Real.arccos c < Real.pi ∧
      z * exp (Real.arccos c * I) ≠ z * exp (-(Real.arccos c * I)) ∧
      z * exp (Real.arccos c * I) ∈ disk ∧ z * exp (-(Real.arccos c * I)) ∈ disk ∧
      H.eval (z * exp (Real.arccos c * I)) = H.eval (z * exp (-(Real.arccos c * I))) ∧
      ¬ IsUnivalentOn (fun w => H.eval w) disk :=
  sec4_P_zero_not_univalent_proved H n hn c hc1 hc2 z hz0 hz1 h0

/-- tex l.237-239: if no`P_c` with `c ∈ [-1, 1]` has a zero in `𝔻`, then `h₁ = P_c(0) ≠ 0` ("the hypothesis gives
$h_1=P_c(0)\neq0$"). -/
theorem sec4_dieudonne_h1 (H : ℂ[X])
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    H.coeff 1 ≠ 0 :=
  sec4_dieudonne_h1_proved H hP

/-- tex l.238-240, verbatim: "It is usually stated for $H(0)=0$ and $H'(0)=1$, but it applies to every polynomial $H$:
the hypothesis gives $h_1=P_c(0)\neq0$, and neither adding a constant to $H$ (the $P_c$ do not involve $h_0$) nor
dividing $H$ by $h_1$ changes univalence or the zeros of the $P_c$." The cited `dieudonne_criterion` follows its source,
[JN, Lemma 6.3] (`H(0) = 0` only); this claim is the paper's extension to every polynomial `H`. -/
theorem sec4_dieudonne_any (H : ℂ[X])
    (hP : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w ∈ disk, (dieudonne H H.natDegree c).eval w ≠ 0) :
    IsUnivalentOn (fun z => H.eval z) disk :=
  sec4_dieudonne_any_proved H hP

/-- Lemma 4.1, the step of the proof (tex l.251-253): if `H'` has no zero in `𝔻̄` and no `P_c` has a zero on the
circle, the number of zeros of `P_c` in `𝔻` is the same for all `c ∈ [-1, 1]`. -/
theorem lem_4_1_count (H : ℂ[X]) (hH' : ∀ w ∈ closedDisk, H.derivative.eval w ≠ 0)
    (hcirc : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 → (dieudonne H H.natDegree c).eval w ≠ 0) :
    ∀ c ∈ Set.Icc (-1 : ℝ) 1, zerosInDisk (dieudonne H H.natDegree c) = zerosInDisk (dieudonne H H.natDegree 1) :=
  lem_4_1_count_proved H hH' hcirc

/-- Lemma 4.1 (tex l.245-248). -/
theorem lem_4_1 (H : ℂ[X]) (hH' : ∀ w ∈ closedDisk, H.derivative.eval w ≠ 0)
    (hcirc : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 → (dieudonne H H.natDegree c).eval w ≠ 0) :
    IsUnivalentOn (fun z => H.eval z) disk :=
  lem_4_1_of sec4_dieudonne_any H hH' hcirc

/-- tex l.258: on the circle `|f*| = |f|` (`deg f ≤ n`). -/
theorem sec4_conjRev_circle (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖(conjRev f n).eval w‖ = ‖f.eval w‖ :=
  sec4_conjRev_circle_proved f n hn w hw

/-- Lemma 4.2 (tex l.261-262): `Tf` has formal degree `n - 1` and constant term `|e₀|² - |e_n|²`. -/
theorem lem_4_2_T (f : ℂ[X]) (n : ℕ) (hn1 : 1 ≤ n) (hn : f.natDegree ≤ n) :
    (schurT f n).natDegree ≤ n - 1 ∧ (schurT f n).coeff 0 = ((‖f.coeff 0‖ ^ 2 - ‖f.coeff n‖ ^ 2 : ℝ) : ℂ) :=
  lem_4_2_T_proved f n hn1 hn

/-- Lemma 4.2, first claim (Schur–Cohn; tex l.262-263): if `|e₀| > |e_n|`, `f` and `Tf` have the same zeros on the
circle, and, if `f` has none there, the same number of zeros in `𝔻`. -/
theorem lem_4_2_a (f : ℂ[X]) (n : ℕ) (hn1 : 1 ≤ n) (hn : f.natDegree ≤ n) (hlt : ‖f.coeff n‖ < ‖f.coeff 0‖) :
    (∀ w : ℂ, ‖w‖ = 1 → (f.eval w = 0 ↔ (schurT f n).eval w = 0)) ∧
      ((∀ w : ℂ, ‖w‖ = 1 → f.eval w ≠ 0) → zerosInDisk (schurT f n) = zerosInDisk f) :=
  lem_4_2_a_proved f n hn1 hn hlt

/-- Lemma 4.2, "Consequently" (tex l.263-264): if the constant terms `δ₁, …, δ_n` are all positive, `f` has no zero in
`𝔻̄`. -/
theorem lem_4_2_b (f : ℂ[X]) (n : ℕ) (hn1 : 1 ≤ n) (hn : f.natDegree ≤ n)
    (hδ : ∀ j, 1 ≤ j → j ≤ n → (schurDelta f n j).im = 0 ∧ 0 < (schurDelta f n j).re) :
    ∀ w ∈ closedDisk, f.eval w ≠ 0 :=
  lem_4_2_b_proved f n hn1 hn hδ

/-- Lemma 4.3, proof (tex l.300-302): a zero `w₀` of `P_c` on the circle is a zero of `P_c*`, and a common zero makes the
resultant at formal degrees `(n-1, n-1)` vanish. (At any formal degrees: `lem_4_3_common_zero_any`.) -/
theorem lem_4_3_common_zero (H : ℂ[X]) (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (w : ℂ) (hw : ‖w‖ = 1)
    (h0 : (dieudonne H n c).eval w = 0) :
    (dieudonneStar H n c).eval w = 0 ∧ resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = 0 :=
  lem_4_3_common_zero_proved H n hn c w hw h0

/-- Lemma 4.3, proof (tex l.301): "a common zero makes the Sylvester matrix singular, at any formal degrees": for formal
degrees `m ≥ deg f`, `k ≥ deg g`, not both `0`, a common zero of `f` and `g` makes the resultant vanish. -/
theorem lem_4_3_common_zero_any (f g : ℂ[X]) (m k : ℕ) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ k)
    (hmk : m ≠ 0 ∨ k ≠ 0) (w : ℂ) (h1 : f.eval w = 0) (h2 : g.eval w = 0) : resultant f g m k = 0 :=
  resultant_eq_zero_of_common_zero f g m k hf hg hmk w h1 h2

/-- Lemma 4.3 (R) (tex l.289-290): "for real $c$ this is $(P_c)^*$, with $P_c$ taken at formal degree $n-1$", i.e.
`P_c* = f*` at formal degree `n - 1` for `f = P_c`. -/
theorem lem_4_3_Pstar (H : ℂ[X]) (n : ℕ) (c : ℝ) :
    dieudonneStar H n c = conjRev (dieudonne H n c) (n - 1) :=
  lem_4_3_Pstar_proved H n c

/-- Lemma 4.3 (D) ⇒ (tex l.284): `H` is a polynomial of degree at most `n`. -/
theorem lem_4_3_H_deg (Q : ℂ[X]) (n : ℕ) (hQ : Q.natDegree = n) (b : ℂ) (as : List ℂ)
    (hnd : (b :: as).Nodup) (hin : ∀ a ∈ b :: as, a ∈ disk) (hzero : ∀ a ∈ b :: as, Q.eval a = 0) :
    (Hpoly Q as).natDegree ≤ n :=
  lem_4_3_H_deg_proved Q n hQ b as hnd hin hzero

/-- Lemma 4.3 (tex l.278-296): under (D), (C), (R), (S) the pair `(W, B)` of Lemma 3.1 is admissible, `deg B = k`,
`1/B(0)² = ∏ J(a_j, b)`; hence `K* ≥ ∏ J(a_j, b)^{1/2}`. -/
theorem lem_4_3 (k : ℕ) (hk : 1 ≤ k) (Q : ℂ[X]) (n : ℕ) (hn : 2 ≤ n) (hQ : Q.natDegree = n) (b : ℂ) (as : List ℂ)
    (hlen : as.length = k)
    (hD : (∀ a ∈ b :: as, ‖a‖ < 1) ∧ (b :: as).Nodup ∧ ∀ a ∈ b :: as, Q.eval a = 0)
    (hC : CondC Q)
    (hR : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 →
      resultant (dieudonne (Hpoly Q as) n c) (dieudonneStar (Hpoly Q as) n c) (n - 1) (n - 1) ≠ 0)
    (hS : ∀ w ∈ closedDisk, (Hpoly Q as).derivative.eval w ≠ 0) :
    IsAdmissible (WOf Q as b) (BOf as b) k ∧ 1 / (BOf as b 0).re ^ 2 = (as.map fun a => Jab a b).prod ∧
      ((Real.sqrt (as.map fun a => Jab a b).prod : ℝ) : EReal) ≤ Kstar := by
  obtain ⟨hlt, hnd, hzero⟩ := hD
  have hin : ∀ a ∈ b :: as, a ∈ disk := fun a ha => mem_ball_zero_iff.2 (hlt a ha)
  -- (C) ⇒ Q' has no zero in 𝔻
  have hQ' : ∀ w ∈ disk, Q.derivative.eval w ≠ 0 := by
    obtain ⟨V, κ, hκ, zs, hzs, hV, hQeq⟩ := hC
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    rw [hQeq, eval_mul, eval_mul, eval_C, eval_list_prod]
    refine mul_ne_zero (mul_ne_zero hκ ?_) (hV w (ball_subset_closedBall hw))
    apply List.prod_ne_zero
    intro hmem
    obtain ⟨p, hp, hp0⟩ := List.mem_map.1 hmem
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
    simp only [eval_pow, eval_sub, eval_X, eval_C] at hp0
    have hwz : w = z.1 := sub_eq_zero.1 (pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 (hzs z hz).2) |>.1 hp0)
    have h1 := (hzs z hz).1
    rw [← hwz] at h1
    linarith
  -- (R), (S) ⇒ H univalent in 𝔻 (Lemma 4.1)
  have hHn : (Hpoly Q as).natDegree ≤ n := lem_4_3_H_deg Q n hQ b as hnd hin hzero
  have hcirc : ∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → ∀ w : ℂ, ‖w‖ = 1 →
      (dieudonne (Hpoly Q as) (Hpoly Q as).natDegree c).eval w ≠ 0 := by
    intro c hc w hw h0
    rw [← dieudonne_eq_natDegree _ n hHn c] at h0
    exact hR c hc (lem_4_3_common_zero _ n hn c w hw h0).2
  have huniv : IsUnivalentOn (fun z => (Hpoly Q as).eval z) disk := lem_4_1 _ hS hcirc
  -- Lemma 3.1, then Theorem 2.2
  obtain ⟨hadm, hB⟩ := lem_3_1 k hk Q b as hlen hQ' hnd hin hzero huniv
  have hB0 : (BOf as b 0).re = ‖etaOf as b‖ := by
    rw [(lem_3_1_WB k hk Q b as hlen hQ' hnd hin hzero huniv).1, Complex.ofReal_re]
  have hsq : Real.sqrt (as.map fun a => Jab a b).prod = 1 / (BOf as b 0).re := by
    rw [← hB, ← one_div_pow, Real.sqrt_sq (one_div_nonneg.2 (hB0 ▸ norm_nonneg _))]
  refine ⟨hadm, hB, ?_⟩
  rw [hsq]
  exact thm_2_2_hence _ _ k hadm

/-- tex l.307 and l.404-405: the Sylvester matrix of `P_c`, `P_c*` is `M(c)` for one matrix `M` of polynomials in `c`
whose entries have degree at most `n - 1` (for `n = 18`: a `34 × 34` matrix, entries of degree at most `17`); so
`Res_w(P_c, P_c*) = F(c)` with `F = det M` of degree at most `2(n-1)²` ("`F` has degree at most `578`"). -/
theorem sec4_res_poly (H : ℂ[X]) (n : ℕ) :
    ∃ (M : Matrix (Fin (n - 1 + (n - 1))) (Fin (n - 1 + (n - 1))) ℂ[X]) (F : ℂ[X]),
      (∀ i j, (M i j).natDegree ≤ n - 1) ∧
      (∀ c : ℝ, sylvester (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = M.map (eval (c : ℂ))) ∧
      F = M.det ∧ F.natDegree ≤ 2 * (n - 1) ^ 2 ∧
      ∀ c : ℝ, resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) = F.eval (c : ℂ) :=
  sec4_res_poly_matrix_proved H n

/-! ## Section 5: the explicit pair (tex l.312-476) -/

/-- tex l.340-346: `(g₀, g₁)` is the unique pair with `∫_b^{a₁} G L = ∫_b^{a₂} G L = 0` (a linear system with nonzero
determinant). -/
theorem sec5_G_unique :
    (∀ g : ℂ × ℂ, (polyInt ((X ^ 2 + C g.2 * X + C g.1) * Lpoly) bD a1D = 0 ∧
        polyInt ((X ^ 2 + C g.2 * X + C g.1) * Lpoly) bD a2D = 0) ↔ g = (g0D, g1D)) ∧
      polyInt (1 * Lpoly) bD a1D * polyInt (X * Lpoly) bD a2D - polyInt (X * Lpoly) bD a1D * polyInt (1 * Lpoly) bD a2D
        ≠ 0 := by
  apply Exact.sec5_G_unique_proved <;> assumption

/-- tex l.345-346: the real and imaginary parts of `g₀` and `g₁` have denominators of 451 to 458 digits. -/
theorem sec5_g_digits :
    ∃ x y u v : ℚ, g0D = gq x y ∧ g1D = gq u v ∧
      ∀ q ∈ [x, y, u, v], 10 ^ 450 ≤ q.den ∧ q.den < 10 ^ 458 := by
  apply Exact.data_g_digits <;> assumption

/-- tex l.350: "`GL` is monic of degree 17". -/
theorem sec5_GL_monic : (Gpoly * Lpoly).Monic ∧ (Gpoly * Lpoly).natDegree = 17 :=
  Exact.sec5_GL_monic_proved

/-- tex l.347-352: `Q(z) = 18 ∫_b^z G L`, so `Q' = 18 (z-1)⁵ G ∏(z - ρ_j)`; `Q` is monic of degree 18 with
`Q(b) = Q(a₁) = Q(a₂) = 0`; `V` has degree 12; `H` is a polynomial of degree 18. -/
theorem sec5_Q :
    (∀ z : ℂ, Qdata.eval z = 18 * polyInt (Gpoly * Lpoly) bD z) ∧
      Qdata.derivative = 18 * (X - 1) ^ 5 * Gpoly * ∏ j : Fin 10, (X - C (rho j)) ∧
      Qdata.Monic ∧ Qdata.natDegree = 18 ∧ Qdata.eval bD = 0 ∧ Qdata.eval a1D = 0 ∧ Qdata.eval a2D = 0 ∧
      Vdata.natDegree = 12 ∧ Hdata * zerosPoly [a1D, a2D] = Qdata * reflPoly [a1D, a2D] ∧ Hdata.natDegree = 18 := by
  apply Exact.sec5_Q_proved <;> assumption

/-- tex l.352-353 (numerical): the zeros of `G` are `1.00000688… - 0.00152261… i` and `-0.41009053… + 1.04265219… i`
(here: within `10⁻⁸` of the printed digits, which are truncations). -/
theorem sec5_G_zeros :
    ∃ z₁ z₂ : ℂ, Gpoly = (X - C z₁) * (X - C z₂) ∧
      1.00000688 ≤ z₁.re ∧ z₁.re < 1.00000689 ∧ -0.00152262 < z₁.im ∧ z₁.im ≤ -0.00152261 ∧
      -0.41009054 < z₂.re ∧ z₂.re ≤ -0.41009053 ∧ 1.04265219 ≤ z₂.im ∧ z₂.im < 1.0426522 := by
  apply Exact.sec5_G_zeros_proved <;> assumption

/-- tex l.354-356 and the caption of Figure 1 (l.378-381): ten of the seventeen critical points of `Q`, counted with
multiplicity, lie within `0.0123` of `z = 1` (the zero of order 5, the zero `z₁` of `G` near 1, and `ρ₁, ρ₂, ρ₉,
ρ₁₀`; here `rho j = ρ_{j+1}`); the other seven (`z₂` and `ρ₃, …, ρ₈`) have moduli between `1.017` and `1.238`; none
lies in `𝔻`. -/
theorem sec5_crit_points :
    ∃ z₁ z₂ : ℂ, Gpoly = (X - C z₁) * (X - C z₂) ∧
      Qdata.derivative.roots = 5 • {1} + {z₁, z₂} + Finset.univ.val.map rho ∧
      ‖z₁ - 1‖ < 0.0123 ∧ (∀ j : Fin 10, j ∈ ({0, 1, 8, 9} : Finset (Fin 10)) → ‖rho j - 1‖ < 0.0123) ∧
      (1.017 < ‖z₂‖ ∧ ‖z₂‖ < 1.238) ∧
      (∀ j : Fin 10, j ∉ ({0, 1, 8, 9} : Finset (Fin 10)) → 1.017 < ‖rho j‖ ∧ ‖rho j‖ < 1.238) ∧
      Multiset.card Qdata.derivative.roots = 17 ∧
      Multiset.card (Qdata.derivative.roots.filter fun z => ‖z - 1‖ < 0.0123) = 10 ∧
      ∀ z ∈ Qdata.derivative.roots, 1 ≤ ‖z‖ :=
  Exact.sec5_crit_points_proved

/-- tex l.357: `J(a₁, b) = 1.30038…` and `J(a₂, b) = 1.02761…` (truncated decimals). -/
theorem sec5_J_values :
    1.30038 ≤ Jab a1D bD ∧ Jab a1D bD < 1.30039 ∧ 1.02761 ≤ Jab a2D bD ∧ Jab a2D bD < 1.02762 :=
  Exact.sec5_J_values_proved

/-- tex l.114-115, l.154-155: `Q'` has a zero of order 5 at `z = 1`, and `(WB)'` of our pair has a zero of order 5
("The pair of Section 5 has such a zero, of order 5") at the point `w₁ = φ_b⁻¹(1) = φ_{-b}(1)` of the unit circle. -/
theorem sec5_order5 :
    Qdata.derivative.rootMultiplicity 1 = 5 ∧ ‖diskAut (-bD) 1‖ = 1 ∧ diskAut bD (diskAut (-bD) 1) = 1 ∧
      deriv (fun z => WOf Qdata [a1D, a2D] bD z * BOf [a1D, a2D] bD z) (diskAut (-bD) 1) = 0 ∧
      analyticOrderAt (deriv (fun z => WOf Qdata [a1D, a2D] bD z * BOf [a1D, a2D] bD z)) (diskAut (-bD) 1) = 5 := by
  apply Exact.sec5_order5_proved <;> assumption

/-- Theorem 5.1, proof (C) and (S) (tex l.400-401, l.419): the 12 numbers `δ_j` of `V` and the 17 numbers `δ_j` of `H'`
are positive. -/
theorem thm_5_1_deltas :
    (∀ j, 1 ≤ j → j ≤ 12 → (schurDelta Vdata 12 j).im = 0 ∧ 0 < (schurDelta Vdata 12 j).re) ∧
    (∀ j, 1 ≤ j → j ≤ 17 → (schurDelta Hdata.derivative 17 j).im = 0 ∧ 0 < (schurDelta Hdata.derivative 17 j).re) :=
  ⟨Exact.v_deltas, Exact.h_deltas⟩

/-- Theorem 5.1 (tex l.384-388), FROM fact (R) (its third conjunct repeats the hypothesis (R); it is NOT a proof of
(R)): for these data, (D), (C) with `Z = (z - 1)⁵`, (R) and (S) hold with
`k = 2`, `n = 18`; the pair `(W, B)` is admissible, `deg B = 2`, `1/B(0)² = J(a₁, b) J(a₂, b) = Λ`, and
`K* ≥ √Λ > 1.1559837`. Fact (R) itself is checked by computer (`CheckR`, `condR_of_checkR`), NOT proved in Lean. -/
theorem thm_5_1_of_R (hR : CondRdata) :
    ((∀ a ∈ [bD, a1D, a2D], ‖a‖ < 1) ∧ [bD, a1D, a2D].Nodup ∧ ∀ a ∈ [bD, a1D, a2D], Qdata.eval a = 0) ∧
    (Qdata.derivative = (X - 1) ^ 5 * Vdata ∧ ∀ w ∈ closedDisk, Vdata.eval w ≠ 0) ∧
    (∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) 17 17 ≠ 0) ∧
    (∀ w ∈ closedDisk, Hdata.derivative.eval w ≠ 0) ∧
    IsAdmissible (WOf Qdata [a1D, a2D] bD) (BOf [a1D, a2D] bD) 2 ∧
    1 / (BOf [a1D, a2D] bD 0).re ^ 2 = Jab a1D bD * Jab a2D bD ∧ Jab a1D bD * Jab a2D bD = (LambdaQ : ℝ) ∧
    ((Real.sqrt LambdaQ : ℝ) : EReal) ≤ Kstar ∧ (1.1559837 : ℝ) < Real.sqrt LambdaQ := by
  obtain ⟨-, -, -, hdeg, -, -, -, hVdeg, -, hHdeg⟩ := sec5_Q
  obtain ⟨hδV, hδH⟩ := thm_5_1_deltas
  have hQV : Qdata.derivative = (X - 1) ^ 5 * Vdata := Exact.Qdata_derivative_eq_V
  have hV : ∀ w ∈ closedDisk, Vdata.eval w ≠ 0 := lem_4_2_b Vdata 12 (by norm_num) hVdeg.le hδV
  have hH'deg : Hdata.derivative.natDegree ≤ 17 := by
    have h := natDegree_derivative_le Hdata
    rw [hHdeg] at h
    omega
  have hS : ∀ w ∈ closedDisk, Hdata.derivative.eval w ≠ 0 := lem_4_2_b _ 17 (by norm_num) hH'deg hδH
  have hC : CondC Qdata := ⟨Vdata, 1, one_ne_zero, [(1, 5)], by simp, hV, by rw [hQV]; simp⟩
  have hprod : ([a1D, a2D].map fun a => Jab a bD).prod = Jab a1D bD * Jab a2D bD := by simp
  obtain ⟨hadm, hB0, hK⟩ := lem_4_3 2 (by norm_num) Qdata 18 (by norm_num) hdeg bD [a1D, a2D] rfl Exact.data_D hC
    hR hS
  rw [hprod, Exact.data_Jab] at hK
  exact ⟨Exact.data_D, ⟨hQV, hV⟩, hR, hS, hadm, hB0.trans hprod, Exact.data_Jab, hK, Exact.data_sqrt_gt⟩

/-- Theorem 5.1, proof (R), first step (tex l.402-404): multiplying `H` by a positive integer `L` multiplies the
resultant by a positive constant. -/
theorem thm_5_1_R_scaling :
    ∀ (H : ℂ[X]) (n : ℕ) (L : ℕ), 0 < L → ∃ κ : ℝ, 0 < κ ∧ ∀ c : ℝ,
      resultant (dieudonne (C (L : ℂ) * H) n c) (dieudonneStar (C (L : ℂ) * H) n c) (n - 1) (n - 1) =
        κ * resultant (dieudonne H n c) (dieudonneStar H n c) (n - 1) (n - 1) := by
  apply Exact.thm_5_1_R_scaling_proved <;> assumption

/-- Theorem 5.1, proof (R), last step (tex l.416-418): the computer-checked statement of (R) (`CheckR`, for `H`; the
program's `F` for `L·H` is `L^34` times it) gives fact (R) of Lemma 4.3. -/
theorem condR_of_checkR (h : CheckR) : CondRdata := by
  obtain ⟨F, -, hF, hm1, hp1, hin⟩ := h
  intro c hc
  rw [hF c]
  have hne : F.eval c ≠ 0 := by
    rcases eq_or_lt_of_le hc.1 with h1 | h1
    · rw [← h1]; exact hm1
    · rcases eq_or_lt_of_le hc.2 with h2 | h2
      · rw [h2]; exact hp1
      · exact hin c ⟨h1, h2⟩
  exact Complex.ofReal_ne_zero.2 hne

/-- Theorem 5.1, proof (tex l.421-422): `Λ - 1.1559837² = 6.75… · 10⁻⁸ > 0`, so `√Λ > 1.1559837`. -/
theorem thm_5_1_margin :
    (6.75e-8 : ℝ) ≤ (LambdaQ : ℝ) - 1.1559837 ^ 2 ∧ (LambdaQ : ℝ) - 1.1559837 ^ 2 < 6.76e-8 := by
  apply Exact.data_margin <;> assumption

/-- Remark 5.2 (tex l.435): `P_{±1}(w) = H'(±w)` (here for every `H`, `n ≥ deg H`). -/
theorem rem_5_2_P_pm_one (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (w : ℂ) :
    (dieudonne H n 1).eval w = H.derivative.eval w ∧ (dieudonne H n (-1)).eval w = H.derivative.eval (-w) :=
  rem_5_2_P_pm_one_proved H n hn w

/-- Remark 5.2 (tex l.431-432), the exact parts: four of the `ρ_j` lie within `0.0123` of `z = 1`; the zero of `V`
nearest to the circle is a zero of `G`, of modulus `1.00000804…`. -/
theorem rem_5_2_exact :
    (Finset.univ.filter fun j : Fin 10 => ‖rho j - 1‖ < 0.0123).card = 4 ∧
    ∃ z : ℂ, Gpoly.eval z = 0 ∧ 1.00000804 ≤ ‖z‖ ∧ ‖z‖ < 1.00000805 ∧
      ∀ w : ℂ, Vdata.eval w = 0 → |‖z‖ - 1| ≤ |‖w‖ - 1| := by
  apply Exact.rem_5_2_exact_proved <;> assumption

/-- Remark 5.2 (tex l.434-435): the zero of `H'` nearest to the circle has modulus `1.00001141…` (truncated decimals).
"Since `P_{±1}(w) = H'(±w)`, this is the margin at `c = ±1`": `rem_5_2_P_pm_one`. -/
theorem rem_5_2_Hprime :
    ∃ z : ℂ, Hdata.derivative.eval z = 0 ∧ 1.00001141 ≤ ‖z‖ ∧ ‖z‖ < 1.00001142 ∧
      ∀ w : ℂ, Hdata.derivative.eval w = 0 → |‖z‖ - 1| ≤ |‖w‖ - 1| :=
  rem_5_2_Hprime_proved

/-- Remark 5.2 (tex l.435): "since `P_{±1}(w) = H'(±w)`, this is the margin at `c = ±1`": the zeros of `P_1` and of
`P_{-1}` nearest to the circle have modulus `1.00001141…`. -/
theorem rem_5_2_margin_pm_one :
    (∃ z : ℂ, (dieudonne Hdata 18 1).eval z = 0 ∧ 1.00001141 ≤ ‖z‖ ∧ ‖z‖ < 1.00001142 ∧
      ∀ w : ℂ, (dieudonne Hdata 18 1).eval w = 0 → |‖z‖ - 1| ≤ |‖w‖ - 1|) ∧
    (∃ z : ℂ, (dieudonne Hdata 18 (-1)).eval z = 0 ∧ 1.00001141 ≤ ‖z‖ ∧ ‖z‖ < 1.00001142 ∧
      ∀ w : ℂ, (dieudonne Hdata 18 (-1)).eval w = 0 → |‖z‖ - 1| ≤ |‖w‖ - 1|) := by
  obtain ⟨z, hz, h1, h2, h3⟩ := rem_5_2_Hprime
  have hd : Hdata.natDegree ≤ 18 := Hdata_natDegree_eq.le
  refine ⟨⟨z, ?_, h1, h2, fun w hw => h3 w ?_⟩, ⟨-z, ?_, by rw [norm_neg]; exact h1, by rw [norm_neg]; exact h2, fun w hw => ?_⟩⟩
  · rw [(rem_5_2_P_pm_one Hdata 18 hd z).1]; exact hz
  · rw [(rem_5_2_P_pm_one Hdata 18 hd w).1] at hw; exact hw
  · rw [(rem_5_2_P_pm_one Hdata 18 hd (-z)).2, neg_neg]; exact hz
  · rw [(rem_5_2_P_pm_one Hdata 18 hd w).2] at hw
    have := h3 (-w) hw
    rw [norm_neg] at this
    rw [norm_neg]
    exact this

/-- The control (tex l.439-440), for every `H`, `n`, `s`, `c`: the Dieudonné polynomials of `H(sz)` are `s P_c(sw)`;
so for `s ≠ 0`, `z` is a zero of `P_c` iff `z/s` is a zero of the Dieudonné polynomial of `H(sz)` ("this divides all
their zeros by `s`"). -/
theorem ctrl_dieudonne_scale (H : ℂ[X]) (n : ℕ) (s : ℂ) (c : ℝ) :
    (∀ w : ℂ, (dieudonne (H.comp (C s * X)) n c).eval w = s * (dieudonne H n c).eval (s * w)) ∧
      (s ≠ 0 → ∀ z : ℂ, (dieudonne (H.comp (C s * X)) n c).eval (z / s) = 0 ↔ (dieudonne H n c).eval z = 0) := by
  refine ⟨dieudonne_comp_scale H n s c, fun hs z => ?_⟩
  rw [dieudonne_comp_scale, mul_div_cancel₀ z hs, mul_eq_zero, or_iff_right hs]

/-- The control (tex l.440): `s - 1 = 7.2·10⁻⁶` exactly for `s = 1250009/1250000`, and
`7.03·10⁻⁶ < 7.2·10⁻⁶ < 1.141·10⁻⁵`. -/
theorem ctrl_s_minus_one :
    sCtrl = ((1250009 / 1250000 : ℝ) : ℂ) ∧ (1250009 / 1250000 : ℝ) - 1 = 7.2e-6 ∧ (7.03e-6 : ℝ) < 7.2e-6 ∧
      (7.2e-6 : ℝ) < 1.141e-5 := by
  refine ⟨by rw [sCtrl]; push_cast; ring, by norm_num, by norm_num, by norm_num⟩

/-- Remark 5.2 and the control (tex l.435-441) at `c = ±0.9231` (that the zeros of the `P_c` come CLOSEST to the
circle near `c = ±0.9231` is numerical only, N7): `P_c` has a zero `z` with
`1 + 7.02·10⁻⁶ < |z| < 1 + 7.03·10⁻⁶` (and `P_{-c}` the zero `-z`); for `H(sz)` the Dieudonné polynomial at `c = 0.9231`
has the zero `z/s`, inside `𝔻` (`s - 1` "exceeds the margin"). -/
theorem ctrl_margin_c :
    ∃ z : ℂ, (dieudonne Hdata 18 0.9231).eval z = 0 ∧ (dieudonne Hdata 18 (-0.9231)).eval (-z) = 0 ∧
      1.00000702 < ‖z‖ ∧ ‖z‖ < 1.00000703 ∧ (dieudonne Hctrl 18 0.9231).eval (z / sCtrl) = 0 ∧ ‖z / sCtrl‖ < 1 := by
  obtain ⟨z, hz, hl, hu⟩ := P_c0_root
  refine ⟨z, hz, ?_, hl, hu, ?_, ?_⟩
  · rw [(sec4_P_neg Hdata 18 0.9231 (-z)).2, neg_neg, hz]
  · rw [Hctrl, dieudonne_comp_scale, mul_div_cancel₀ z sCtrl_ne_zero, hz, mul_zero]
  · rw [norm_div, norm_sCtrl, div_lt_one (by norm_num)]
    linarith

/-- The control (tex l.440-441, "but not the margin at `c = ±1`"): for `H(sz)`, `P_1` and `P_{-1}` still have no zero
in `𝔻̄` (by `rem_5_2_Hprime`'s bound: `H'` has no zero with `|z| ≤ 1.00001141`, and `s < 1.00001141`). -/
theorem ctrl_pm_one (w : ℂ) (hw : w ∈ closedDisk) :
    (dieudonne Hctrl 18 1).eval w ≠ 0 ∧ (dieudonne Hctrl 18 (-1)).eval w ≠ 0 :=
  ctrl_pm_one_proved w hw

/-- The control (tex l.441-442): "for these data the resultant in (R) has a zero in `[-1, 1]`" — PROVED here (the
paper's program finds it by computer): `H(sz)'` has no zero in `𝔻̄`, the Dieudonné polynomial of `H(sz)` at
`c = 0.9231` has a zero in `𝔻`, so by the count of Lemma 4.1 some `P_c` of `H(sz)` has a zero on the circle, and there
the resultant vanishes (Lemma 4.3). -/
theorem ctrl_R_fails :
    ∃ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 ∧ resultant (dieudonne Hctrl 18 c) (dieudonneStar Hctrl 18 c) 17 17 = 0 :=
  ctrl_R_fails_proved

/-- The control (tex l.442): "check (D) fails too, since `H(sz)` no longer matches `Q`":
`H(sz)(z - a₁)(z - a₂) ≠ Q(z)(1 - ā₁z)(1 - ā₂z)`. -/
theorem ctrl_D_fails : Hctrl * zerosPoly [a1D, a2D] ≠ Qdata * reflPoly [a1D, a2D] :=
  ctrl_D_fails_proved

/-- Lemma 5.3 (Crane; tex l.447-449): `K(d+1) ≥ K(d)` for every `d ≥ 2`. -/
theorem lem_5_3 (d : ℕ) (hd : 2 ≤ d) : Kd d ≤ Kd (d + 1) :=
  lem_5_3_proved d hd

/-- tex l.87: a polynomial `p ∈ 𝓟_{29984}` with `m(p) > 1.0000004` (Adamczewski–Colbrook's, cited) "gives `K(d) > 1`
for every `d ≥ 29 984`" (with Lemma 5.3). -/
theorem intro_AC_degree (p : ℂ[X]) (hp : IsPd 29984 p) (hm : 1.0000004 < mval p) :
    ∀ d ≥ 29984, (1 : EReal) < Kd d := by
  have h0 : (1 : EReal) < Kd 29984 := by
    have hle : ((mval p : ℝ) : EReal) ≤ Kd 29984 :=
      le_iSup (fun q : {q : ℂ[X] // IsPd 29984 q} => ((mval q.1 : ℝ) : EReal)) ⟨p, hp⟩
    refine lt_of_lt_of_le ?_ hle
    exact_mod_cast (show (1 : ℝ) < mval p by linarith)
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact h0
  | succ n hn ih => exact ih.trans_le (lem_5_3 n (by omega))

/-- Lemma 5.3, proof (tex l.452-464): for `p ∈ 𝓟_d`, `p_ε = p + εz^{d+1} ∈ 𝓟_{d+1}` (`ε ≠ 0`) and
`m(p_ε) → m(p)` as `ε → 0`. -/
theorem lem_5_3_limit (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    (∀ ε : ℂ, ε ≠ 0 → IsPd (d + 1) (p + C ε * X ^ (d + 1))) ∧
      Tendsto (fun ε : ℂ => mval (p + C ε * X ^ (d + 1))) (𝓝[≠] 0) (𝓝 (mval p)) :=
  lem_5_3_limit_proved d hd p hp

/-- Lemma 5.3, proof (tex l.455-456): for `ε ≠ 0`, `p_ε` has `d` critical points (with multiplicity), and their
product has modulus `1/((d+1)|ε|)`. -/
theorem lem_5_3_prod (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (ε : ℂ) (hε : ε ≠ 0) :
    (p + C ε * X ^ (d + 1)).derivative.roots.card = d ∧
      ‖(p + C ε * X ^ (d + 1)).derivative.roots.prod‖ = 1 / ((d + 1) * ‖ε‖) :=
  lem_5_3_prod_proved d hd p hp ε hε

/-- Lemma 5.3, proof (tex l.453-456), the Hurwitz step: "`d - 1` of the `d` critical points of `p_ε`, counted with
multiplicity, tend to those of `p` ... while the other `d - 1` stay bounded": (i) in a disk `|w| < R₀` that contains all
critical points of `p`, `p_ε` has exactly `d - 1` critical points for small `ε`; (ii) around each critical point `β` of
`p`, for every small `r`, `p_ε` has exactly `μ` critical points in `|w - β| < r` for small `ε`, `μ` the multiplicity. -/
theorem lem_5_3_hurwitz (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    (∀ R₀ : ℝ, (∀ β : ℂ, p.derivative.eval β = 0 → ‖β‖ < R₀) → ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ‖ε‖ < δ →
      zerosInBall (p + C ε * X ^ (d + 1)).derivative 0 R₀ = d - 1) ∧
    (∀ β : ℂ, p.derivative.eval β = 0 → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℂ, ‖ε‖ < δ → zerosInBall (p + C ε * X ^ (d + 1)).derivative β r = p.derivative.rootMultiplicity β) :=
  lem_5_3_hurwitz_proved d hd p hp

/-- Lemma 5.3, proof (tex l.453-456): as `ε → 0` a critical point of `p_ε` tends to `∞` ("the remaining one, `β_ε`,
tends to `∞`", as the product of the `d` critical points has modulus `1/((d+1)|ε|)`): for every `M > 0` there is
`δ > 0` such that for `0 < |ε| < δ` some critical point `β` of `p_ε` has `|β| ≥ M`. -/
theorem lem_5_3_escape (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (M : ℝ) (hM : 0 < M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < δ →
      ∃ β : ℂ, (p + C ε * X ^ (d + 1)).derivative.eval β = 0 ∧ M ≤ ‖β‖ :=
  lem_5_3_escape_proved d hd p hp M hM

/-- Lemma 5.3, proof (tex l.456-460): at a critical point `β` of `p_ε`, `p_ε(β)/β = p(β)/β - p'(β)/(d+1)`. -/
theorem lem_5_3_identity (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (ε β : ℂ) (hε : ε ≠ 0)
    (hβ : (p + C ε * X ^ (d + 1)).derivative.eval β = 0) :
    (p + C ε * X ^ (d + 1)).eval β / β = p.eval β / β - p.derivative.eval β / ((d : ℂ) + 1) :=
  lem_5_3_identity_proved d hd p hp ε β hε hβ

/-- Lemma 5.3, proof (tex l.462-463): the right side `p(β)/β - p'(β)/(d+1)` "tends to `∞` in modulus": at a critical
point `β` of `p_ε`, `|p_ε(β)/β| → ∞` as `|β| → ∞`, uniformly in `ε ≠ 0` (it is the value at `β` of one polynomial of
degree `d - 1 ≥ 1`). -/
theorem lem_5_3_far_ratio (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ ε β : ℂ, ε ≠ 0 → (p + C ε * X ^ (d + 1)).derivative.eval β = 0 → R ≤ ‖β‖ →
      B ≤ ‖(p + C ε * X ^ (d + 1)).eval β / β‖ :=
  lem_5_3_far_ratio_proved d hd p hp B

/-- Corollary 5.4 (tex l.467-469), FROM fact (R): `K(d) > 1.1559837` for all sufficiently large `d`. -/
theorem cor_5_4_of_R (hR : CondRdata) : ∃ d₀ : ℕ, ∀ d ≥ d₀, ((1.1559837 : ℝ) : EReal) < Kd d := by
  obtain ⟨-, -, -, -, -, -, -, hK, hgt⟩ := thm_5_1_of_R hR
  have hlt : ((1.1559837 : ℝ) : EReal) < ⨆ d : {d : ℕ // 2 ≤ d}, Kd d.1 :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hgt) hK
  obtain ⟨⟨d₀, hd₀⟩, h₀⟩ := lt_iSup_iff.1 hlt
  refine ⟨d₀, fun d (hd : d₀ ≤ d) => lt_of_lt_of_le h₀ ?_⟩
  induction d, hd using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact ih.trans (lem_5_3 n (hd₀.trans hn))

/-- Theorem 1.1 (tex l.104-111; proved at l.476), FROM fact (R): `K* ≥ √Λ`, `√Λ = 1.15598372919…`, `K* > 1.1559837`,
and `K(d) > 1.1559837` for all sufficiently large `d`. -/
theorem thm_1_1_of_R (hR : CondRdata) :
    ((Real.sqrt LambdaQ : ℝ) : EReal) ≤ Kstar ∧
      (1.15598372919 : ℝ) ≤ Real.sqrt LambdaQ ∧ Real.sqrt LambdaQ < 1.1559837292 ∧
      ((1.1559837 : ℝ) : EReal) < Kstar ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ((1.1559837 : ℝ) : EReal) < Kd d := by
  obtain ⟨-, -, -, -, -, -, -, hK, hgt⟩ := thm_5_1_of_R hR
  exact ⟨hK, Exact.data_sqrt_digits.1, Exact.data_sqrt_digits.2,
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hgt) hK, cor_5_4_of_R hR⟩

/-- Theorem 5.1 FROM `CheckR` (fact (R) as stated in Defs/Conditions.lean; checked by computer, NOT proved in Lean). -/
theorem thm_5_1_of_checkR (h : CheckR) :
    ((∀ a ∈ [bD, a1D, a2D], ‖a‖ < 1) ∧ [bD, a1D, a2D].Nodup ∧ ∀ a ∈ [bD, a1D, a2D], Qdata.eval a = 0) ∧
    (Qdata.derivative = (X - 1) ^ 5 * Vdata ∧ ∀ w ∈ closedDisk, Vdata.eval w ≠ 0) ∧
    (∀ c : ℝ, c ∈ Set.Icc (-1 : ℝ) 1 → resultant (dieudonne Hdata 18 c) (dieudonneStar Hdata 18 c) 17 17 ≠ 0) ∧
    (∀ w ∈ closedDisk, Hdata.derivative.eval w ≠ 0) ∧
    IsAdmissible (WOf Qdata [a1D, a2D] bD) (BOf [a1D, a2D] bD) 2 ∧
    1 / (BOf [a1D, a2D] bD 0).re ^ 2 = Jab a1D bD * Jab a2D bD ∧ Jab a1D bD * Jab a2D bD = (LambdaQ : ℝ) ∧
    ((Real.sqrt LambdaQ : ℝ) : EReal) ≤ Kstar ∧ (1.1559837 : ℝ) < Real.sqrt LambdaQ :=
  thm_5_1_of_R (condR_of_checkR h)

/-- Corollary 5.4 FROM `CheckR` (checked by computer, NOT proved in Lean). -/
theorem cor_5_4_of_checkR (h : CheckR) : ∃ d₀ : ℕ, ∀ d ≥ d₀, ((1.1559837 : ℝ) : EReal) < Kd d :=
  cor_5_4_of_R (condR_of_checkR h)

/-- Theorem 1.1 FROM `CheckR` (checked by computer, NOT proved in Lean): the headline result, literally from the
computer-checked `Prop`. -/
theorem thm_1_1_of_checkR (h : CheckR) :
    ((Real.sqrt LambdaQ : ℝ) : EReal) ≤ Kstar ∧
      (1.15598372919 : ℝ) ≤ Real.sqrt LambdaQ ∧ Real.sqrt LambdaQ < 1.1559837292 ∧
      ((1.1559837 : ℝ) : EReal) < Kstar ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ((1.1559837 : ℝ) : EReal) < Kd d :=
  thm_1_1_of_R (condR_of_checkR h)

/-! ## NOT stated (proposed; each is listed for the author's review)
Each item: (label) [kind] tex lines: the sentence(s), and why there is no Lean row. scripts/audit.py prints this list as
a table in AUDIT.md.
(N1) [cited] tex l.33-41 abstract, l.66-86, l.94-102 intro table: results of OTHER papers quoted as background
     (Smale's K = 4, Tischler, Crane, Beardon–Minda–Ng, Conte–Fujikawa–Lakic, Fujikawa–Sugawa, the 2026 Lean disproof,
     Jatar–Ng's 1.1018586 and 1.1030). Not used by the proof. The paper's own deductions from them are STATED:
     "so K* ≤ 4" (l.66, intro_smale_K4, Smale's theorem as hypothesis); "all these bounds tend to 4" (l.75-76,
     intro_bounds_tend_to_4); "so Smale's conjecture is false" (l.81, intro_conjecture_false, K* > 1 as hypothesis);
     √(8081/6656) = 1.1018586… and "improving the bound 1.1018" (l.33, l.48-49, l.84, intro_JN_digits).
(N2) [cited] tex l.121-124: results of the long paper [GoelLong] (B₁, B₂, B_d bounds) and of [JN, Thm. 1.3]. Other
     papers' results. STATED: the comparison of the two B_d bounds for d ≥ 452 (intro_improves_JN); the readings
     "1.1018 < B₁ < 1.1833" and "B₂ < 3.89" of [JN, Thm. 1.3] (intro_JN_B1_B2).
(N3) [now stated] tex l.149, Theorem 2.2 "Moreover" (K* = sup_d B_d): Bcal, thm_2_2_moreover.
(N4) [about the cited proof] tex l.155-160: how [JN]'s proof covers pairs with a boundary zero ([JN, Lemma 2.1]).
     Its middle sentence, "the pair of Section 5 has such a zero, of order 5", is STATED: sec5_order5.
(N5) [cited] tex l.165-170, the steps of Remark 2.3 that need the Riemann map ψ of Ω: Ω is simply connected and ψ
     exists; W = ψ/κ is univalent (W ∈ 𝒮); B is a finite Blaschke product (|B| → 1 at the circle). They are inside the
     cited result jatarNg_prop_3_1 (a Lean proof would need the Riemann mapping theorem, which Mathlib v4.35 lacks).
     STATED: rem_2_3_q (q(0) = 1 and |q(β)| ≥ m(p) at the critical points), rem_2_3_bounded (Ω bounded),
     rem_2_3_crit_outside (the critical points lie outside Ω), rem_2_3_formulas (W(0) = 0, W'(0) = 1, B(0) = 1/R and
     (WB)' = p'(ψ)ψ'/(κR), for ψ as a parameter), rem_2_3_pair, rem_2_3_trivial, rem_2_3_Kstar_le. The last sentence
     (how [JN] prove Prop. 4.2: Runge, Hilbert's lemniscate theorem) is about the cited proof.
(N6) [program description] tex l.125-131, l.391-396, l.402-418, l.425-428: what the two programs read and check and how
     the first one computes (primes, Hadamard bound, Chinese remainder theorem, interpolation, 47 Descartes tests, run
     time; the map x ↦ (c₀+c₁x)/(1+x) of (0,∞) onto (c₀,c₁), l.418). In Lean the data are Defs/Data.lean; facts (D),
     (C), (S) about them are proved claims; fact (R) is checked by computer, NOT proved in Lean (CheckR). STATED:
     scaling H by L scales the resultant by a positive constant (thm_5_1_R_scaling); F is a polynomial in c of degree
     at most 578 (sec4_res_poly).
(N6b) [now stated] tex l.439-442, the control: STATED and PROVED: ctrl_dieudonne_scale, ctrl_s_minus_one,
     ctrl_margin_c, ctrl_pm_one, ctrl_R_fails (for H(sz) the resultant in (R) has a zero in [-1, 1]), ctrl_D_fails.
     "(R) should fail" is an expectation (N15).
(N7) [numerical only] tex l.435-436, Remark 5.2: "Numerically the zeros of the P_c come closest to the circle near
     c = ±0.9231, within about 7.03·10⁻⁶": the paper marks it "Numerically ... about"; that the minimum over c is
     near ±0.9231 is a numerical observation (no row). STATED for c = ±0.9231 itself: ctrl_margin_c (a zero with
     1 + 7.02·10⁻⁶ < |z| < 1 + 7.03·10⁻⁶). The other margins of Remark 5.2 are STATED: rem_5_2_exact (V and the ρ_j),
     rem_5_2_Hprime (H'), rem_5_2_P_pm_one (P_{±1}(w) = H'(±w)).
(N8) [method] tex l.314-320, Section 5, opening: how the pair was found and rounded (a search; not a claim the proof
     uses; "G, Q and H are determined by them exactly" is sec5_G_unique).
(N9) [not a claim] tex l.63-64: "In words, (1.1) says that the mean rate of change ..." - a reading of (1.1) in words;
     the content is the definition of K(d) (sec1_best_constant).
(N10) [notation] tex l.86-87: the notation of [JN] (S(P), 𝓜_d, 𝓜 for m(p), K(d), K*).
(N11) [cited] tex l.87: Adamczewski–Colbrook's results (the mechanism behind the 2026 Lean disproof; an explicit p of
     degree 29 984 with m(p) > 1.0000004, verified by interval arithmetic) - another paper's results. STATED: the
     deduction "it gives K(d) > 1 for every d ≥ 29 984" (intro_AC_degree).
(N12) [method] tex l.186-191: the idea before Lemma 3.1 (its content is lem_3_1; "for k = 1 the lemma is [JN, Lemma
     6.2]" is a citation).
(N13) [method] tex l.242-243: "That no P_c has a zero in 𝔻, for all c in an interval, is not a finite check" - a remark
     on the method; the reduction it announces is Lemma 4.1 (lem_4_1).
(N14) [not a claim] tex l.431-433, Remark 5.2: "They are small because the data are close to a numerical maximizer of
     1/B(0) ..." - an explanation of the margins.
(N15) [not a claim] tex l.441: "(R) should fail" - an expectation; the claim that it does fail is ctrl_R_fails.
(N16) [now stated] tex l.453-463, proof of Lemma 5.3: the Hurwitz step (lem_5_3_hurwitz), the product
     (lem_5_3_prod), the escape (lem_5_3_escape), the identity (lem_5_3_identity) and p_ε(β)/β → ∞ (lem_5_3_far_ratio).
     The Lean proof of m(p_ε) → m(p) (lem_5_3_limit) itself takes another route (AUDIT_NOTES.md, A1).
(N17) [not a claim] tex l.152: "Our proof uses only the inequality K* ≥ 1/B(0)" - a remark on the proof; #print axioms
     of thm_1_1_of_R confirms it (it uses jatarNg_prop_4_2 and dieudonne_criterion, not jatarNg_prop_3_1); "We note
     that [JN] is a preprint". tex l.308-310: "Lemma 4.2 can only show ..., this is why (C) splits off the factor Z" -
     a remark on the method. tex l.361-377: the coordinates of Figure 1 (a drawing; its caption is sec5_crit_points).
     tex l.476: "The proof gives no explicit value of d₀" - a remark on the proof.
-/

end Smale
