/-
Osserman/Proofs/OssTop.lean — proofs of three §1 statements of paper 013: thm_C_clifford_cases, thm_C_hyp_literal,
isOsserman_iff_set.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route for `isOsserman_iff_set` (every `n`): at a unit `x`, (a) the eigenvectors of the symmetric `J_x` span, so
`x^⊥ = ⨆_{s ∈ S} E_s(x)` for any finite `S` containing the reduced eigenvalues; (b) with the Lagrange polynomial
`L_μ` of the nodes `S`, the matrix `L_μ(J_x) Π(x)` is a projection onto `E_μ(x)`, so `redMult x μ = tr(L_μ(J_x)Π(x))`,
a continuous function of `x`; (c) under the set reading, one finite `S` (the eigenvalues of `J_{x₀}`) works at every
unit `x`, so the integer `redMult x μ` is continuous on the connected unit sphere (`n ≥ 2`), hence constant.
`thm_C_hyp_literal` is then a corollary.
-/
import Osserman.Proofs.Spectral
import Osserman.Proofs.Sec2

namespace Osserman.Proofs.OssTop

open Osserman Matrix

open Osserman.Proofs.Spectral (Esp mem_Esp mem_perp)

variable {n : ℕ}

/-! ### (1) The two Clifford normal forms -/

theorem thm_C_clifford_cases_proved (R : CurvTensor 16) (μ κ : ℝ) (A : Vec 16 → Matrix (Fin 16) (Fin 16) ℝ)
    (hJ : ∀ x, R.jacobi x = μ • Pi x + κ • A x) (hA : IsFormCl7 A ∨ IsFormCl8 A) : R.IsClifford := by
  rcases hA with ⟨J, hJs, hA⟩ | ⟨J, hJs, hA⟩
  · refine ⟨7, J, hJs, μ, fun _ => κ, fun x => ?_⟩
    rw [hJ, hA, Finset.smul_sum]
  · refine ⟨8, J, hJs, μ + κ, fun _ => -κ, fun x => ?_⟩
    rw [hJ, hA, smul_sub, Finset.smul_sum]
    simp only [neg_smul, Finset.sum_neg_distrib, add_smul]
    abel

/-! ### Polynomials in `J` and Lagrange polynomials -/

open Polynomial in
/-- A polynomial in `J` acts on an eigenvector by its value at the eigenvalue. -/
lemma aeval_mulVec_eig {J : Matrix (Fin n) (Fin n) ℝ} {v : Vec n} {s : ℝ} (hv : J *ᵥ v = s • v) (p : ℝ[X]) :
    aeval J p *ᵥ v = p.eval s • v := by
  have hpow : ∀ k : ℕ, J ^ k *ᵥ v = s ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mulVec_mulVec, hv, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_mulVec, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mulVec,
      hpow, smul_smul]

open Polynomial in
/-- The Lagrange polynomial of `μ` on the nodes `S`: `L_μ(t) = ∏_{s ∈ S, s ≠ μ} (t - s)/(μ - s)`. -/
noncomputable def lag (S : Finset ℝ) (μ : ℝ) : ℝ[X] := ∏ s ∈ S.erase μ, (C (μ - s)⁻¹ * (X - C s))

lemma lag_eval_self (S : Finset ℝ) (μ : ℝ) : (lag S μ).eval μ = 1 := by
  rw [lag, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun s hs => ?_
  have h : μ - s ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  simp [inv_mul_cancel₀ h]

lemma lag_eval_other {S : Finset ℝ} {μ s : ℝ} (hs : s ∈ S) (hne : s ≠ μ) : (lag S μ).eval s = 0 := by
  rw [lag, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hs⟩) (by simp)

/-! ### Spectral theorem for `J_x`, reduced to `x^⊥` -/

lemma jacobi_isHermitian (R : CurvTensor n) (x : Vec n) : (R.jacobi x).IsHermitian := by
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
  exact Spectral.jacobi_transpose R x

/-- Every vector is a combination of the eigenvectors of `J_x`. -/
lemma eq_sum_eigvec (R : CurvTensor n) (x v : Vec n) :
    ∃ c : Fin n → ℝ, v = ∑ j, c j • ⇑((jacobi_isHermitian R x).eigenvectorBasis j) := by
  set b := (jacobi_isHermitian R x).eigenvectorBasis
  refine ⟨fun j => b.repr (WithLp.toLp 2 v) j, ?_⟩
  have h := congrArg WithLp.ofLp (b.sum_repr (WithLp.toLp 2 v))
  rw [WithLp.ofLp_sum] at h
  simpa using h.symm

/-- Spectral theorem, reduced form: at a unit `x`, if every reduced eigenvalue of `J_x` lies in the finite set `S`,
then `x^⊥ ≤ ⨆_{s ∈ S} E_s(x)`. -/
lemma perp_le_iSup (R : CurvTensor n) {x : Vec n} (hx : x ⬝ᵥ x = 1) (S : Finset ℝ)
    (hS : ∀ μ ∉ S, R.redMult x μ = 0) : perp x ≤ ⨆ s ∈ S, Esp R x s := by
  intro v hv
  obtain ⟨c, hc⟩ := eq_sum_eigvec R x v
  set hH := jacobi_isHermitian R x
  set b := hH.eigenvectorBasis
  -- `b_j - ⟨x, b_j⟩x` lies in `E_{λ_j}(x)`
  have hw : ∀ j, ⇑(b j) - (x ⬝ᵥ ⇑(b j)) • x ∈ Esp R x (hH.eigenvalues j) := by
    intro j
    have hb := hH.mulVec_eigenvectorBasis j
    have hxb : hH.eigenvalues j * (x ⬝ᵥ ⇑(b j)) = 0 := by
      have h1 : x ⬝ᵥ (R.jacobi x *ᵥ ⇑(b j)) = 0 := by
        rw [dotProduct_comm, Curv.symm_dot (Spectral.jacobi_transpose R x), Spectral.jacobi_self,
          zero_dotProduct]
      rw [hb, dotProduct_smul, smul_eq_mul] at h1
      exact h1
    rw [mem_Esp]
    refine ⟨?_, ?_⟩
    · rw [← Curv.jacobi_mulVec, mulVec_sub, mulVec_smul, Spectral.jacobi_self, smul_zero, sub_zero, hb, smul_sub,
        smul_smul, hxb, zero_smul, sub_zero]
    · rw [dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one, sub_self]
  have hwS : ∀ j, ⇑(b j) - (x ⬝ᵥ ⇑(b j)) • x ∈ ⨆ s ∈ S, Esp R x s := by
    intro j
    by_cases hj : hH.eigenvalues j ∈ S
    · exact (le_iSup₂ (f := fun s _ => Esp R x s) _ hj) (hw j)
    · have h0 : Esp R x (hH.eigenvalues j) = ⊥ := Submodule.finrank_eq_zero.mp (hS _ hj)
      have hwj := hw j
      rw [h0, Submodule.mem_bot] at hwj
      rw [hwj]
      exact Submodule.zero_mem _
  have hv' : v = ∑ j, c j • (⇑(b j) - (x ⬝ᵥ ⇑(b j)) • x) := by
    have hxv : x ⬝ᵥ v = 0 := hv
    have hsum : ∑ j, c j * (x ⬝ᵥ ⇑(b j)) = x ⬝ᵥ v := by
      rw [hc, dotProduct_sum]
      simp [dotProduct_smul]
    simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
    rw [← Finset.sum_smul, hsum, hxv, zero_smul, sub_zero, ← hc]
  rw [hv']
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hwS j)

/-! ### The reduced multiplicity as a trace -/

/-- The matrix `L_μ(J_x) Π(x)`. -/
noncomputable def Pmat (R : CurvTensor n) (S : Finset ℝ) (μ : ℝ) (x : Vec n) : Matrix (Fin n) (Fin n) ℝ :=
  Polynomial.aeval (R.jacobi x) (lag S μ) * Pi x

/-- At a unit `x` whose reduced eigenvalues lie in `S`: `redMult x μ = tr(L_μ(J_x) Π(x))`. -/
lemma redMult_eq_trace (R : CurvTensor n) {x : Vec n} (hx : x ⬝ᵥ x = 1) (S : Finset ℝ)
    (hS : ∀ μ ∉ S, R.redMult x μ = 0) (μ : ℝ) : (R.redMult x μ : ℝ) = (Pmat R S μ x).trace := by
  have hspan := perp_le_iSup R hx S hS
  have hmap : ⨆ s ∈ S, Esp R x s ≤
      (Esp R x μ).comap (Matrix.toLin' (Polynomial.aeval (R.jacobi x) (lag S μ))) := by
    refine iSup₂_le fun s hs v hv => ?_
    rw [Submodule.mem_comap, Matrix.toLin'_apply]
    have hJv : R.jacobi x *ᵥ v = s • v := by rw [Curv.jacobi_mulVec]; exact (mem_Esp.mp hv).1
    rw [aeval_mulVec_eig hJv]
    by_cases hsμ : s = μ
    · subst hsμ
      rw [lag_eval_self, one_smul]
      exact hv
    · rw [lag_eval_other hs hsμ, zero_smul]
      exact Submodule.zero_mem _
  have hP : LinearMap.IsProj (Esp R x μ) (Matrix.toLin' (Pmat R S μ x)) := by
    refine ⟨fun y => ?_, fun e he => ?_⟩
    · rw [Matrix.toLin'_apply, Pmat, ← mulVec_mulVec]
      have hy : Pi x *ᵥ y ∈ perp x := by
        rw [mem_perp, Spectral.Pi_mulVec, hx, one_smul, dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one,
          dotProduct_comm, sub_self]
      exact hmap (hspan hy)
    · rw [Matrix.toLin'_apply, Pmat, ← mulVec_mulVec]
      have hPe : Pi x *ᵥ e = e := by
        rw [Spectral.Pi_mulVec, hx, one_smul, dotProduct_comm, (mem_Esp.mp he).2, zero_smul, sub_zero]
      have hJe : R.jacobi x *ᵥ e = μ • e := by rw [Curv.jacobi_mulVec]; exact (mem_Esp.mp he).1
      rw [hPe, aeval_mulVec_eig hJe, lag_eval_self, one_smul]
  have htr := hP.trace
  rw [Matrix.trace_toLin'_eq] at htr
  rw [htr]
  rfl

/-! ### Continuity -/

lemma continuous_quad {A : Vec n → Matrix (Fin n) (Fin n) ℝ} (hA : IsQuadFamily A) : Continuous A := by
  obtain ⟨M, hM⟩ := hA
  rw [show A = fun x => ∑ a, ∑ b, (x a * x b) • M a b from funext hM]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    ((continuous_apply a).mul (continuous_apply b)).smul continuous_const

lemma continuous_trace_Pmat (R : CurvTensor n) (S : Finset ℝ) (μ : ℝ) :
    Continuous fun x => (Pmat R S μ x).trace :=
  (((Polynomial.continuous_aeval (lag S μ)).comp (continuous_quad (Spectral.quad_jacobi R))).mul
    (continuous_quad Spectral.quad_Pi)).matrix_trace

/-! ### Connectedness -/

/-- A continuous real function with natural-number values on a preconnected set is constant. -/
lemma nat_valued_const {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s) {f : X → ℝ}
    (hf : ContinuousOn f s) (g : X → ℕ) (hfg : ∀ z ∈ s, f z = g z) {a b : X} (ha : a ∈ s) (hb : b ∈ s) :
    g a = g b := by
  have key : ∀ a b, a ∈ s → b ∈ s → g a < g b → False := by
    intro a b ha hb hlt
    have hmem : (g a : ℝ) + 1 / 2 ∈ Set.Icc (f a) (f b) := by
      rw [hfg a ha, hfg b hb]
      have h1 : (g a : ℝ) + 1 ≤ g b := by exact_mod_cast hlt
      constructor <;> linarith
    obtain ⟨c, hc, hfc⟩ := hs.intermediate_value ha hb hf hmem
    rw [hfg c hc] at hfc
    have h2 : (2 * g c : ℝ) = 2 * g a + 1 := by linarith
    have h3 : 2 * g c = 2 * g a + 1 := by exact_mod_cast h2
    omega
  rcases lt_trichotomy (g a) (g b) with h | h | h
  · exact (key a b ha hb h).elim
  · exact h
  · exact (key b a hb ha h).elim

lemma unit_mem_sphere {z : Vec n} (hz : z ⬝ᵥ z = 1) :
    WithLp.toLp 2 z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h : ‖WithLp.toLp 2 z‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial, hz]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

lemma sphere_unit {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    WithLp.ofLp v ⬝ᵥ WithLp.ofLp v = 1 := by
  rw [mem_sphere_zero_iff_norm] at hv
  have h := real_inner_self_eq_norm_sq v
  rw [hv, one_pow, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
  exact h

/-! ### (3) Set reading = multiplicity reading, and (2) -/

/-- Below dimension 2, `x^⊥ = 0`, so every reduced multiplicity vanishes. -/
lemma redMult_low (R : CurvTensor n) (hn : n ≤ 1) {z : Vec n} (hz : z ⬝ᵥ z = 1) (ν : ℝ) : R.redMult z ν = 0 := by
  have hp := Spectral.finrank_perp hz
  have hle : R.redMult z ν ≤ Module.finrank ℝ (perp z) := Submodule.finrank_mono inf_le_right
  omega

/-- The reduced multiplicities vanish off the (finite) set of eigenvalues of `J_x`. -/
lemma redMult_eq_zero_of_not_eig (R : CurvTensor n) (x : Vec n) {ν : ℝ}
    (hν : ¬ Module.End.HasEigenvalue (R.jacobiMap x) ν) : R.redMult x ν = 0 := by
  have h0 : Module.End.eigenspace (R.jacobiMap x) ν = ⊥ := by
    by_contra h
    exact hν (Module.End.hasEigenvalue_iff.mpr h)
  show Module.finrank ℝ ↥(Module.End.eigenspace (R.jacobiMap x) ν ⊓ perp x) = 0
  rw [h0, bot_inf_eq, finrank_bot]

theorem isOsserman_iff_set_proved {n : ℕ} (R : CurvTensor n) : R.IsOsserman ↔ R.IsOssermanSet := by
  refine ⟨fun h x y hx hy μ => by rw [h x y hx hy μ], fun hO x y hx hy μ => ?_⟩
  by_cases hn : n ≤ 1
  · rw [redMult_low R hn hx, redMult_low R hn hy]
  set S := (Module.End.finite_hasEigenvalue (R.jacobiMap x)).toFinset
  have hSz : ∀ z : Vec n, z ⬝ᵥ z = 1 → ∀ ν ∉ S, R.redMult z ν = 0 := by
    intro z hz ν hν
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hν
    have h := hO x z hx hz ν
    rw [redMult_eq_zero_of_not_eig R x hν] at h
    omega
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n)
  have hconn := isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin n)) zero_le_one
  have h := nat_valued_const hconn.isPreconnected
    (f := fun v : EuclideanSpace ℝ (Fin n) => (Pmat R S μ (WithLp.ofLp v)).trace)
    ((continuous_trace_Pmat R S μ).comp (PiLp.continuous_ofLp 2 _)).continuousOn
    (fun v => R.redMult (WithLp.ofLp v) μ)
    (fun v hv => (redMult_eq_trace R (sphere_unit hv) S (hSz _ (sphere_unit hv)) μ).symm)
    (unit_mem_sphere hx) (unit_mem_sphere hy)
  simpa using h

theorem thm_C_hyp_literal_proved (R : CurvTensor 16) (hO : R.IsOssermanSet) (μ₁ μ₂ : ℝ) (hne : μ₁ ≠ μ₂)
    (x₀ : Vec 16) (hx₀ : x₀ ⬝ᵥ x₀ = 1) (h₀ : R.redMult x₀ μ₁ = 8 ∧ R.redMult x₀ μ₂ = 7) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → R.redMult x μ₁ = 8 ∧ R.redMult x μ₂ = 7 := by
  have hOs := (isOsserman_iff_set_proved R).mpr hO
  intro x hx
  exact ⟨(hOs x x₀ hx hx₀ μ₁).trans h₀.1, (hOs x x₀ hx hx₀ μ₂).trans h₀.2⟩

end Osserman.Proofs.OssTop
