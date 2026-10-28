/-
Osserman/Proofs/S83Opp1.lean — §8.3 of paper 013, opposite signs, first part: rows s8_3_pm, s8_3_both_vanish,
s8_3_combination, s8_3_block_frame (statements copied verbatim from Osserman/Paper/Statements8.lean).
Premise rows (leading arguments with their exact types): s8_q_prime, lem_8_2_div_q, s8_spectral_identity,
s8_move_eigenfield.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. (pm) In the domain `𝒪`, `u_ju_k = v_jv_k` for all `j, k` gives `u = ±v` (compare a nonzero `u_j`, then cancel).
(both vanish) `p_1 = 0` and `c p_2p_2 = 0` with `c` a unit give `p_2 = 0`; then all fields are divisible by `q`.
(combination) `aP_1 - εbP_2` is a cubic field divisible by `q`, hence `qJ'x`; orthogonality and the norms `q³` give
`|J'x|² = (a²+b²)|x|²` and `⟨J'x, x⟩ = 0`, so `J = J'/√(a²+b²)` is skew and orthogonal. (block frame) With
`Jx = (ap_0 - bp_1)/s` in the orthonormal frame `p_0 = P_1(x), p_1 = εP_2(x)` at a unit `x`, `J_x - C(Jx)(Jx)ᵀ` acts on the
frame by the matrix `diag(μ,σ) - (C/s²)(a,-b)(a,-b)ᵀ`.
-/
import Osserman.Proofs.S83Move

namespace Osserman.Proofs.S83

open Osserman Matrix MvPolynomial Osserman.Proofs.S8Tools

/-- The type of row `s8_q_prime`. -/
abbrev QPrimeHyp : Prop := Irreducible (sqP 16) ∧ Prime (sqP 16) ∧ IsDomain Ocal

lemma piO_eq_iff (p r : MvPolynomial (Fin 16) ℝ) : piO p = piO r ↔ sqP 16 ∣ p - r := by
  unfold piO
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma piO_eq_zero_iff (p : MvPolynomial (Fin 16) ℝ) : piO p = 0 ↔ sqP 16 ∣ p := by
  rw [← map_zero piO, piO_eq_iff, sub_zero]

lemma isUnit_piO_C {c : ℝ} (hc : c ≠ 0) : IsUnit (piO (C c)) := by
  refine IsUnit.of_mul_eq_one (piO (C c⁻¹)) ?_
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]

/-! ### `ap_1 = ±bp_2` -/

lemma pm_of_outer {A : Type*} [CommRing A] [IsDomain A] (u v : Fin 16 → A) (h : ∀ j k, u j * u k = v j * v k) :
    (∀ j, u j = v j) ∨ ∀ j, u j = -v j := by
  by_cases hall : ∀ j, u j = 0
  · left
    intro j
    have hv : v j * v j = 0 := by rw [← h j j, hall j, zero_mul]
    rw [hall j, mul_self_eq_zero.mp hv]
  · simp only [not_forall] at hall
    obtain ⟨j0, hj0⟩ := hall
    have hsq : (u j0 - v j0) * (u j0 + v j0) = 0 := by linear_combination h j0 j0
    rcases mul_eq_zero.mp hsq with h1 | h1
    · left
      intro k
      apply mul_left_cancel₀ hj0
      linear_combination h j0 k - v k * h1
    · right
      intro k
      apply mul_left_cancel₀ hj0
      linear_combination h j0 k + v k * h1

/-- Row `s8_3_pm`. -/
theorem s8_3_pm_proved (hQ : QPrimeHyp) (hSpec : SpecIdHyp) (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1))
    (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ j, piO (MvPolynomial.C a * P 0 j) = piO (MvPolynomial.C (ε * b) * P 1 j) := by
  have : IsDomain Ocal := hQ.2.2
  have hmod := s8_3_mod_q_proved hSpec R M N ev P h
  have key (j k : Fin 16) :
      piO (C a * P 0 j) * piO (C a * P 0 k) = piO (C b * P 1 j) * piO (C b * P 1 k) := by
    rw [← map_mul, ← map_mul]
    have l : C a * P 0 j * (C a * P 0 k) = C (ev 2 * (ev 2 - ev 1)) * P 0 j * P 0 k := by
      rw [← ha2, map_pow]; ring
    have r : C b * P 1 j * (C b * P 1 k) = C (-(ev 3 * (ev 3 - ev 1))) * P 1 j * P 1 k := by
      rw [← hb2, map_pow]; ring
    rw [l, r]
    exact hmod j k
  have hsc (ε : ℝ) (j : Fin 16) : piO (C (ε * b) * P 1 j) = piO (C ε) * piO (C b * P 1 j) := by
    rw [map_mul C ε b, mul_assoc, map_mul piO]
  rcases pm_of_outer (fun j => piO (C a * P 0 j)) (fun j => piO (C b * P 1 j)) key with hp | hp
  · exact ⟨1, Or.inl rfl, fun j => by rw [hsc, map_one, map_one, one_mul]; exact hp j⟩
  · exact ⟨-1, Or.inr rfl, fun j => by rw [hsc, map_neg, map_one, map_neg, map_one]; linear_combination hp j⟩

/-- Row `s8_3_both_vanish`. -/
theorem s8_3_both_vanish_proved (hQ : QPrimeHyp) (hdiv : DivQHyp) (hSpec : SpecIdHyp) (hMove : MoveHyp)
    (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (ha : 0 < ev 2 * (ev 2 - ev 1))
    (hb : ev 3 * (ev 3 - ev 1) < 0) (h0 : ∀ j, piO (P 0 j) = 0) :
    (∀ j, piO (P 1 j) = 0) ∧ R.IsClifford := by
  have : IsDomain Ocal := hQ.2.2
  have hmod := s8_3_mod_q_proved hSpec R M N ev P h
  have hcu := isUnit_piO_C (by linarith : -(ev 3 * (ev 3 - ev 1)) ≠ 0)
  have h1 : ∀ j, piO (P 1 j) = 0 := by
    intro j
    have e := hmod j j
    simp only [map_mul, h0 j, mul_zero] at e
    rw [mul_assoc] at e
    exact mul_self_eq_zero.mp (hcu.mul_right_eq_zero.mp e.symm)
  refine ⟨h1, s8_3_linear_case_proved hdiv hMove R M N ev P h fun i j => ?_⟩
  fin_cases i
  · exact (piO_eq_zero_iff _).mp (h0 j)
  · exact (piO_eq_zero_iff _).mp (h1 j)

/-! ### The combination `aP_1 - εbP_2 = √(a²+b²) qJx` -/

lemma sec83_unit_facts {R : CurvTensor 16} {M N : ℕ} {ev : Fin 4 → ℝ}
    {P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ} (h : Sec83Data R M N ev P) (x : Vec 16) :
    evalField (P 0) x ⬝ᵥ evalField (P 0) x = (x ⬝ᵥ x) ^ 3 ∧ evalField (P 1) x ⬝ᵥ evalField (P 1) x = (x ⬝ᵥ x) ^ 3 ∧
      evalField (P 0) x ⬝ᵥ evalField (P 1) x = 0 ∧ evalField (P 0) x ⬝ᵥ x = 0 ∧ evalField (P 1) x ⬝ᵥ x = 0 := by
  have o := sec83_orth h x 0 1
  obtain ⟨-, -, -, -, hC, -, -⟩ := h
  exact ⟨(hC 0 x).2.1, (hC 1 x).2.1, by simpa using o, (hC 0 x).1, (hC 1 x).1⟩

/-- Row `s8_3_combination`. -/
theorem s8_3_combination_proved (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1)) (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hpm : ∀ j, piO (MvPolynomial.C a * P 0 j) = piO (MvPolynomial.C (ε * b) * P 1 j)) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧ ∀ x : Vec 16,
      a • evalField (P 0) x - (ε * b) • evalField (P 1) x = (Real.sqrt (a ^ 2 + b ^ 2) * (x ⬝ᵥ x)) • (J *ᵥ x) := by
  have h3 := h.2.2.2.1
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  let F : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => C a * P 0 j - C (ε * b) * P 1 j
  have hF3 (j : Fin 16) : (F j).IsHomogeneous 3 := ((h3 0 j).C_mul a).sub ((h3 1 j).C_mul _)
  have hFq (j : Fin 16) : sqP 16 ∣ F j := (piO_eq_iff _ _).mp (hpm j)
  obtain ⟨J', hJ'⟩ := dvd_cubic_field hF3 hFq
  have hFx (x : Vec 16) : evalField F x = a • evalField (P 0) x - (ε * b) • evalField (P 1) x := by
    funext j
    simp [F, evalField]
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs
  have hS : 0 < a ^ 2 + b ^ 2 := by positivity
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hss : s * s = a ^ 2 + b ^ 2 := Real.mul_self_sqrt hS.le
  -- the two facts at a unit `x`
  have hunit (x : Vec 16) (hx : x ⬝ᵥ x = 1) :
      (J' *ᵥ x) ⬝ᵥ (J' *ᵥ x) = s * s ∧ x ⬝ᵥ (J' *ᵥ x) = 0 := by
    obtain ⟨n0, n1, o01, t0, t1⟩ := sec83_unit_facts h x
    have e := hJ' x
    rw [hFx, hx, one_smul] at e
    rw [← e, hss, hx] at *
    constructor
    · simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, n0, n1, o01,
        dotProduct_comm (evalField (P 1) x) (evalField (P 0) x)]
      linear_combination (b ^ 2) * hε2
    · rw [dotProduct_comm]
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, t0, t1]
      ring
  let J : Matrix (Fin 16) (Fin 16) ℝ := s⁻¹ • J'
  have hJx (x : Vec 16) : J' *ᵥ x = s • (J *ᵥ x) := by
    rw [Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hs0, one_smul]
  obtain ⟨hJc, hJo⟩ := ThmEFrames.thm_E_frame_clifford_proved (fun _ : Fin 1 => J)
    (fun x hx α β => by
      obtain ⟨n, -⟩ := hunit x hx
      rw [hJx, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at n
      have : J *ᵥ x ⬝ᵥ J *ᵥ x = 1 := by
        have h2 : s * s * (J *ᵥ x ⬝ᵥ J *ᵥ x - 1) = 0 := by linear_combination n
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 (mul_ne_zero hs0 hs0)
        · linarith
      simpa [Subsingleton.elim α β] using this)
    (fun x hx α => by
      obtain ⟨-, p⟩ := hunit x hx
      rw [hJx, dotProduct_smul, smul_eq_mul] at p
      exact (mul_eq_zero.mp p).resolve_left hs0)
  refine ⟨J, hJc.1 0, hJo 0, fun x => ?_⟩
  rw [← hFx, hJ', hJx, smul_smul, mul_comm]

/-! ### The changed block in the frame `(P_1, εP_2)` -/

lemma frame_calc (A : Matrix (Fin 16) (Fin 16) ℝ) (p0 p1 u : Vec 16) (μ σ C s a b : ℝ)
    (hA0 : A *ᵥ p0 = μ • p0) (hA1 : A *ᵥ p1 = σ • p1) (h00 : p0 ⬝ᵥ p0 = 1) (h11 : p1 ⬝ᵥ p1 = 1)
    (h01 : p0 ⬝ᵥ p1 = 0) (hs : s ≠ 0) (hu : s • u = a • p0 - b • p1) :
    (A - C • vecMulVec u u) *ᵥ p0 = (μ - C / s ^ 2 * (a * a)) • p0 + (0 - C / s ^ 2 * (-b * a)) • p1 ∧
      (A - C • vecMulVec u u) *ᵥ p1 = (0 - C / s ^ 2 * (a * -b)) • p0 + (σ - C / s ^ 2 * (-b * -b)) • p1 := by
  have hu' : u = s⁻¹ • (a • p0 - b • p1) := by rw [← hu, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have h10 : p1 ⬝ᵥ p0 = 0 := by rw [dotProduct_comm]; exact h01
  have d0 : u ⬝ᵥ p0 = s⁻¹ * a := by
    rw [hu', smul_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, h00, h10]; simp
  have d1 : u ⬝ᵥ p1 = -(s⁻¹ * b) := by
    rw [hu', smul_dotProduct, sub_dotProduct, smul_dotProduct, smul_dotProduct, h01, h11]; simp
  constructor
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Spectral.vecMulVec_self_mulVec, d0, hA0, hu']
    module
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Spectral.vecMulVec_self_mulVec, d1, hA1, hu']
    module

/-- Row `s8_3_block_frame`. -/
theorem s8_3_block_frame_proved (R : CurvTensor 16) (M N : ℕ) (ev : Fin 4 → ℝ)
    (P : Fin 2 → Fin 16 → MvPolynomial (Fin 16) ℝ) (h : Sec83Data R M N ev P) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ 2 = ev 2 * (ev 2 - ev 1)) (hb2 : b ^ 2 = -(ev 3 * (ev 3 - ev 1))) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (J : Matrix (Fin 16) (Fin 16) ℝ) (hJs : Jᵀ = -J) (hJo : Jᵀ * J = 1)
    (hJ : ∀ x : Vec 16, a • evalField (P 0) x - (ε * b) • evalField (P 1) x =
      (Real.sqrt (a ^ 2 + b ^ 2) * (x ⬝ᵥ x)) • (J *ᵥ x))
    (R' : CurvTensor 16) (hR' : ∀ u v z, R'.op u v z = R.op u v z - (ev 2 + ev 3 - ev 1) • RJfun J u v z) :
    let B2 : Matrix (Fin 2) (Fin 2) ℝ :=
      !![ev 2, 0; 0, ev 3] - ((ev 2 + ev 3 - ev 1) / (a ^ 2 + b ^ 2)) • vecMulVec ![a, -b] ![a, -b]
    ∀ x : Vec 16, x ⬝ᵥ x = 1 →
      R'.jacobi x *ᵥ evalField (P 0) x = B2 0 0 • evalField (P 0) x + B2 1 0 • (ε • evalField (P 1) x) ∧
      R'.jacobi x *ᵥ (ε • evalField (P 1) x) = B2 0 1 • evalField (P 0) x + B2 1 1 • (ε • evalField (P 1) x) := by
  intro B2 x hx
  obtain ⟨n0, n1, o01, -, -⟩ := sec83_unit_facts h x
  obtain ⟨-, -, -, -, -, he2, he3⟩ := h
  rw [hx] at n0 n1
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs
  have hS : 0 < a ^ 2 + b ^ 2 := by positivity
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  have hss : a ^ 2 + b ^ 2 = s ^ 2 := (Real.sq_sqrt hS.le).symm
  have hjac : R'.jacobi x = R.jacobi x - (ev 2 + ev 3 - ev 1) • vecMulVec (J *ᵥ x) (J *ᵥ x) := by
    rw [(Rem72a.rem_7_2_jac_split_proved R R' J hJs _ hR' x).1]
    simp [jfam]
  have hA0 : R.jacobi x *ᵥ evalField (P 0) x = ev 2 • evalField (P 0) x := by
    have := (mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp (he2 x)).1
    rwa [hx, mul_one] at this
  have hA1 : R.jacobi x *ᵥ (ε • evalField (P 1) x) = ev 3 • (ε • evalField (P 1) x) := by
    have := (mem_eig_iff R x _ _).mp (Submodule.mem_inf.mp (he3 x)).1
    rw [hx, mul_one] at this
    rw [Matrix.mulVec_smul, this, smul_comm]
  have h11 : (ε • evalField (P 1) x) ⬝ᵥ (ε • evalField (P 1) x) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, n1]; rcases hε with rfl | rfl <;> norm_num
  have h01 : evalField (P 0) x ⬝ᵥ (ε • evalField (P 1) x) = 0 := by rw [dotProduct_smul, o01, smul_zero]
  have hu : s • (J *ᵥ x) = a • evalField (P 0) x - b • (ε • evalField (P 1) x) := by
    have e := hJ x
    rw [hx, mul_one] at e
    rw [← e, smul_smul, mul_comm b ε]
  obtain ⟨c0, c1⟩ := frame_calc (R.jacobi x) _ _ (J *ᵥ x) (ev 2) (ev 3) (ev 2 + ev 3 - ev 1) s a b hA0 hA1
    (by rw [n0]; norm_num) h11 h01 hs0 hu
  have hB : B2 0 0 = ev 2 - (ev 2 + ev 3 - ev 1) / s ^ 2 * (a * a) ∧
      B2 1 0 = 0 - (ev 2 + ev 3 - ev 1) / s ^ 2 * (-b * a) ∧ B2 0 1 = 0 - (ev 2 + ev 3 - ev 1) / s ^ 2 * (a * -b) ∧
      B2 1 1 = ev 3 - (ev 2 + ev 3 - ev 1) / s ^ 2 * (-b * -b) := by
    simp only [B2, hss, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    simp
  rw [hjac, hB.1, hB.2.1, hB.2.2.1, hB.2.2.2]
  exact ⟨c0, c1⟩

end Osserman.Proofs.S83
