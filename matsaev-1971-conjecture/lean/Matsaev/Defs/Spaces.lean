/-
Matsaev/Defs/Spaces.lean — the spaces and operators of the paper (trust surface).
Paper: "Matsaev's (1971) conjecture is false for every p != 2", Dave Goel,
short v2.00 (md5 a9b3c6be).

* `ℓ^p_n` is Mathlib's `WithLp p (n → 𝕜)` (norm `(∑ |x_i|^p)^(1/p)`), and the norm of an `n × n` matrix `A` is
  Mathlib's operator norm of `Matrix.toLpLin p p A` on it (`matNorm`).
* `ℓ^p(ℕ)` is Mathlib's `lp (fun _ : ℕ => 𝕜) p`; the right shift `S` is `(S x)_0 = 0`, `(S x)_(n+1) = x_n` (Section 1),
  built here as a continuous linear map (`shiftOp`). For a polynomial `P`, `P(S)` is `Polynomial.aeval (shiftOp p 𝕜) P`
  in the algebra of continuous linear maps, and `shiftNorm p 𝕜 P` is its operator norm.
* `𝕜` is `ℝ` or `ℂ` (`RCLike`).
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Matsaev.Defs.Scalar

namespace Matsaev

open scoped ENNReal
open Polynomial

section Matrices

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The operator `x ↦ A x` of a square matrix on `ℓ^p_n = WithLp p (n → 𝕜)`. -/
noncomputable def matOp (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) :
    WithLp p (n → 𝕜) →L[𝕜] WithLp p (n → 𝕜) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin p p A)

/-- The paper's `‖A‖_{ℓ^p_n → ℓ^p_n}`: Mathlib's operator norm of `matOp p A`. -/
noncomputable def matNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) : ℝ :=
  ‖matOp p A‖

end Matrices

section Shift

/-- The right shift of a sequence: `(shiftSeq x) 0 = 0`, `(shiftSeq x) (n + 1) = x n`. -/
def shiftSeq {E : Type*} [Zero E] (x : ℕ → E) : ℕ → E
  | 0 => 0
  | n + 1 => x n

theorem shiftSeq_add {E : Type*} [AddZeroClass E] (x y : ℕ → E) : shiftSeq (x + y) = shiftSeq x + shiftSeq y := by
  funext n
  cases n
  · simp [shiftSeq]
  · rfl

theorem shiftSeq_smul {R E : Type*} [Zero E] [SMulZeroClass R E] (c : R) (x : ℕ → E) :
    shiftSeq (c • x) = c • shiftSeq x := by
  funext n
  cases n
  · simp [shiftSeq]
  · rfl

variable {𝕜 : Type*} [RCLike 𝕜]

theorem memℓp_shiftSeq (p : ℝ≥0∞) {x : ℕ → 𝕜} (hx : Memℓp x p) : Memℓp (shiftSeq x) p := by
  obtain (rfl | rfl | hp) := p.trichotomy
  · rw [memℓp_zero_iff] at hx ⊢
    refine ((hx.image Nat.succ).union (Set.finite_singleton 0)).subset ?_
    intro n hn
    cases n with
    | zero => exact Or.inr rfl
    | succ k => exact Or.inl ⟨k, hn, rfl⟩
  · rw [memℓp_infty_iff] at hx ⊢
    obtain ⟨C, hC⟩ := hx
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => simp [shiftSeq]
    | succ k => exact le_max_of_le_left (hC ⟨k, rfl⟩)
  · rw [memℓp_gen_iff hp] at hx ⊢
    rw [← summable_nat_add_iff 1]
    simpa [shiftSeq] using hx

/-- The right shift as a linear map on `ℓ^p(ℕ)`. -/
noncomputable def shiftLin (p : ℝ≥0∞) (𝕜 : Type*) [RCLike 𝕜] :
    lp (fun _ : ℕ => 𝕜) p →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) p where
  toFun x := ⟨shiftSeq (x : ℕ → 𝕜), memℓp_shiftSeq p (lp.memℓp x)⟩
  map_add' x y := by
    apply Subtype.ext
    change shiftSeq (⇑(x + y)) = shiftSeq ⇑x + shiftSeq ⇑y
    rw [lp.coeFn_add]
    exact shiftSeq_add _ _
  map_smul' c x := by
    apply Subtype.ext
    change shiftSeq (⇑(c • x)) = c • shiftSeq ⇑x
    rw [lp.coeFn_smul]
    exact shiftSeq_smul _ _

theorem shiftLin_apply_zero (p : ℝ≥0∞) (x : lp (fun _ : ℕ => 𝕜) p) : shiftLin p 𝕜 x 0 = 0 := rfl

theorem shiftLin_apply_succ (p : ℝ≥0∞) (x : lp (fun _ : ℕ => 𝕜) p) (n : ℕ) : shiftLin p 𝕜 x (n + 1) = x n := rfl

theorem norm_shiftLin_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (x : lp (fun _ : ℕ => 𝕜) p) : ‖shiftLin p 𝕜 x‖ ≤ ‖x‖ := by
  obtain (hp0 | rfl | hp) := p.trichotomy
  · exact absurd (hp0 ▸ (Fact.out : (1 : ℝ≥0∞) ≤ p)) (by simp)
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
    cases n with
    | zero => simp [shiftLin_apply_zero]
    | succ k => rw [shiftLin_apply_succ]; exact lp.norm_apply_le_norm ENNReal.top_ne_zero x k
  · refine lp.norm_le_of_tsum_le hp (norm_nonneg _) ?_
    have hs : Summable fun n => ‖shiftLin p 𝕜 x n‖ ^ p.toReal := (lp.memℓp (shiftLin p 𝕜 x)).summable hp
    rw [hs.tsum_eq_zero_add, lp.norm_rpow_eq_tsum hp x]
    simp [shiftLin_apply_zero, shiftLin_apply_succ, Real.zero_rpow hp.ne']

/-- The paper's right shift `S` on `ℓ^p(ℕ)` (Section 1), as a continuous linear map. -/
noncomputable def shiftOp (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [RCLike 𝕜] :
    lp (fun _ : ℕ => 𝕜) p →L[𝕜] lp (fun _ : ℕ => 𝕜) p :=
  (shiftLin p 𝕜).mkContinuous 1 fun x => by simpa using norm_shiftLin_le p x

/-- The paper's `‖P(S)‖_{ℓ^p → ℓ^p}`: Mathlib's operator norm of `P(S) = Polynomial.aeval S P`. -/
noncomputable def shiftNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (𝕜 : Type*) [RCLike 𝕜] (P : 𝕜[X]) : ℝ :=
  ‖Polynomial.aeval (shiftOp p 𝕜) P‖

end Shift

/-- The paper's polynomial `P_a(z) = 1 + a z - B z²` (Theorem A). -/
noncomputable def Pa {𝕜 : Type*} [RCLike 𝕜] (a B : 𝕜) : 𝕜[X] := 1 + C a * X - C B * X ^ 2

/-- Matsaev's conjecture (eq. `eq:matsaev`) for the `L^p` space `ℓ^p_2` (two atoms) over `ℂ`: every
contraction `T` of `ℓ^p_2` satisfies `‖P(T)‖ ≤ ‖P(S)‖_{ℓ^p → ℓ^p}` for every polynomial `P`. The full conjecture
(every contraction of every `L^p` space) contains this case, so `¬ MatsaevOnL2 p` refutes it
(`Matsaev.matsaevOnL2_of_conjecture`, Matsaev/Ops/LpBridge.lean, proves that `MatsaevConjecture p` implies it). -/
def MatsaevOnL2 (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∀ T : Matrix (Fin 2) (Fin 2) ℂ, matNorm p T ≤ 1 → ∀ P : ℂ[X], matNorm p (Polynomial.aeval T P) ≤ shiftNorm p ℂ P

end Matsaev
