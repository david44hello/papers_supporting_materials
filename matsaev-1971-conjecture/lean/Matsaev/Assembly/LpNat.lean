/-
Matsaev/Assembly/LpNat.lean — the operator `A ⊕ 0` on `ℓ^p(ℕ) = ℓ^p_2 ⊕_p ℓ^p` and `‖P(A)‖ ≤ ‖P(A ⊕ 0)‖`, for the last
sentence of the proof of Theorem A ("(1) also fails on ℓ^p itself"). Author: Dave Goel.
-/
import Matsaev.Defs.Spaces
import Matsaev.Bridge.Basic

namespace Matsaev.LpNat

open Matsaev
open scoped ENNReal
open Polynomial

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A polynomial in operators commutes with an intertwining map: if `U ∘ ι = ι ∘ A` then `P(U) ∘ ι = ι ∘ P(A)`. -/
theorem aeval_comp_intertwine {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℂ E₂] (U : E₂ →L[ℂ] E₂) (A : E₁ →L[ℂ] E₁) (ι : E₁ →L[ℂ] E₂) (h : U.comp ι = ι.comp A) (P : ℂ[X]) :
    (aeval U P).comp ι = ι.comp (aeval A P) := by
  induction P using Polynomial.induction_on with
  | C c =>
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  | add P Q hP hQ =>
    rw [map_add, map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hP, hQ]
  | monomial n c hn =>
    have hU : aeval U (C c * X ^ (n + 1)) = aeval U (C c * X ^ n) * U := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    have hA : aeval A (C c * X ^ (n + 1)) = aeval A (C c * X ^ n) * A := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [hU, hA, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc, h,
      ← ContinuousLinearMap.comp_assoc, hn, ContinuousLinearMap.comp_assoc]

/-- If `ι` is an isometry and `V ∘ ι = ι ∘ W`, then `‖W‖ ≤ ‖V‖`. -/
theorem opNorm_le_of_intertwine {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
    [NormedSpace ℂ E₂] (V : E₂ →L[ℂ] E₂) (W : E₁ →L[ℂ] E₁) (ι : E₁ →L[ℂ] E₂) (hι : ∀ x, ‖ι x‖ = ‖x‖)
    (h : V.comp ι = ι.comp W) : ‖W‖ ≤ ‖V‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have hx : ι (W x) = V (ι x) := by
    have := congrArg (fun F : E₁ →L[ℂ] E₂ => F x) h
    simpa using this.symm
  calc ‖W x‖ = ‖ι (W x)‖ := (hι _).symm
    _ = ‖V (ι x)‖ := by rw [hx]
    _ ≤ ‖V‖ * ‖ι x‖ := V.le_opNorm _
    _ = ‖V‖ * ‖x‖ := by rw [hι]

/-- The sequence `(ξ₀, ξ₁, 0, 0, …)` of a vector `ξ ∈ ℓ^p_2`. -/
noncomputable def padSeq (ξ : WithLp p (Fin 2 → ℂ)) (i : ℕ) : ℂ := if h : i < 2 then ξ ⟨i, h⟩ else 0

omit [Fact (1 ≤ p)] in
theorem padSeq_add (ξ η : WithLp p (Fin 2 → ℂ)) (i : ℕ) : padSeq p (ξ + η) i = padSeq p ξ i + padSeq p η i := by
  unfold padSeq; split_ifs <;> simp

omit [Fact (1 ≤ p)] in
theorem padSeq_smul (c : ℂ) (ξ : WithLp p (Fin 2 → ℂ)) (i : ℕ) : padSeq p (c • ξ) i = c • padSeq p ξ i := by
  unfold padSeq; split_ifs <;> simp

/-- `ℓ^p_2 → ℓ^p(ℕ)`, `ξ ↦ (ξ₀, ξ₁, 0, 0, …)`, as a linear map. -/
noncomputable def padLin : WithLp p (Fin 2 → ℂ) →ₗ[ℂ] lp (fun _ : ℕ => ℂ) p where
  toFun ξ := ∑ i ∈ Finset.range 2, lp.single p i (padSeq p ξ i)
  map_add' ξ η := by
    ext n
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hn : n = i
    · subst hn; simp [padSeq_add]
    · simp [hn]
  map_smul' c ξ := by
    ext n
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, RingHom.id_apply,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hn : n = i
    · subst hn; simp [padSeq_smul]
    · simp [hn]

theorem norm_padLin (hptop : p ≠ ⊤) (ξ : WithLp p (Fin 2 → ℂ)) : ‖padLin p ξ‖ = ‖ξ‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hptop
  have h : ‖padLin p ξ‖ ^ p.toReal = ‖ξ‖ ^ p.toReal := by
    change ‖∑ i ∈ Finset.range 2, lp.single p i (padSeq p ξ i)‖ ^ p.toReal = _
    rw [lp.norm_sum_single hp0, norm_toLp_rpow p hptop (WithLp.ofLp ξ)]
    simp [Finset.sum_range_succ, Fin.sum_univ_two, padSeq]
  exact (Real.rpow_left_inj (norm_nonneg _) (norm_nonneg _) hp0.ne').mp h

/-- The isometric embedding `ι : ℓ^p_2 → ℓ^p(ℕ)`. -/
noncomputable def pad (hptop : p ≠ ⊤) : WithLp p (Fin 2 → ℂ) →L[ℂ] lp (fun _ : ℕ => ℂ) p :=
  (padLin p).mkContinuous 1 fun ξ => by rw [norm_padLin p hptop, one_mul]

theorem norm_pad (hptop : p ≠ ⊤) (ξ : WithLp p (Fin 2 → ℂ)) : ‖pad p hptop ξ‖ = ‖ξ‖ :=
  norm_padLin p hptop ξ

/-- `ℓ^p(ℕ) → ℓ^p_2`, the first two coordinates, as a linear map. -/
noncomputable def headLin : lp (fun _ : ℕ => ℂ) p →ₗ[ℂ] WithLp p (Fin 2 → ℂ) where
  toFun x := WithLp.toLp p (fun i : Fin 2 => x (i : ℕ))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

theorem norm_headLin_le (hptop : p ≠ ⊤) (x : lp (fun _ : ℕ => ℂ) p) : ‖headLin p x‖ ≤ ‖x‖ := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hptop
  have h : ‖headLin p x‖ ^ p.toReal ≤ ‖x‖ ^ p.toReal := by
    change ‖WithLp.toLp p (fun i : Fin 2 => x (i : ℕ))‖ ^ p.toReal ≤ _
    rw [norm_toLp_rpow p hptop]
    have := lp.sum_rpow_le_norm_rpow hp0 x (Finset.range 2)
    simpa [Finset.sum_range_succ, Fin.sum_univ_two] using this
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp0).mp h

/-- The coordinate map `ℓ^p(ℕ) → ℓ^p_2` (norm at most `1`). -/
noncomputable def head (hptop : p ≠ ⊤) : lp (fun _ : ℕ => ℂ) p →L[ℂ] WithLp p (Fin 2 → ℂ) :=
  (headLin p).mkContinuous 1 fun x => by rw [one_mul]; exact norm_headLin_le p hptop x

theorem head_pad (hptop : p ≠ ⊤) : (head p hptop).comp (pad p hptop) = ContinuousLinearMap.id ℂ _ := by
  ext ξ i
  change (padLin p ξ : ℕ → ℂ) (i : ℕ) = ξ i
  simp only [padLin, LinearMap.coe_mk, AddHom.coe_mk, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  fin_cases i <;> simp [Pi.single_apply, padSeq]

/-- `A ⊕ 0` on `ℓ^p(ℕ) = ℓ^p_2 ⊕_p ℓ^p`: `A` on the first two coordinates, `0` on the others. -/
noncomputable def sumZero (hptop : p ≠ ⊤) (A : WithLp p (Fin 2 → ℂ) →L[ℂ] WithLp p (Fin 2 → ℂ)) :
    lp (fun _ : ℕ => ℂ) p →L[ℂ] lp (fun _ : ℕ => ℂ) p :=
  (pad p hptop).comp (A.comp (head p hptop))

theorem sumZero_comp_pad (hptop : p ≠ ⊤) (A : WithLp p (Fin 2 → ℂ) →L[ℂ] WithLp p (Fin 2 → ℂ)) :
    (sumZero p hptop A).comp (pad p hptop) = (pad p hptop).comp A := by
  rw [sumZero, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, head_pad,
    ContinuousLinearMap.comp_id]

theorem norm_sumZero_le (hptop : p ≠ ⊤) (A : WithLp p (Fin 2 → ℂ) →L[ℂ] WithLp p (Fin 2 → ℂ)) :
    ‖sumZero p hptop A‖ ≤ ‖A‖ := by
  have hpad : ‖pad p hptop‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by rw [norm_pad, one_mul]
  have hhead : ‖head p hptop‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [one_mul]; exact norm_headLin_le p hptop x
  calc ‖sumZero p hptop A‖ ≤ ‖pad p hptop‖ * (‖A‖ * ‖head p hptop‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = ‖A‖ := by ring

/-- `‖P(A)‖ ≤ ‖P(A ⊕ 0)‖` for every polynomial `P`. -/
theorem norm_aeval_le_sumZero (hptop : p ≠ ⊤) (A : WithLp p (Fin 2 → ℂ) →L[ℂ] WithLp p (Fin 2 → ℂ)) (P : ℂ[X]) :
    ‖aeval A P‖ ≤ ‖aeval (sumZero p hptop A) P‖ :=
  opNorm_le_of_intertwine _ _ (pad p hptop) (norm_pad p hptop)
    (aeval_comp_intertwine _ _ _ (sumZero_comp_pad p hptop A) P)

end Matsaev.LpNat
