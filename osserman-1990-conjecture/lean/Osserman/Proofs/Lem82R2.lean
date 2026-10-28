/-
Osserman/Proofs/Lem82R2.lean — Lemma 8.2 of paper 013, the cases r = 3 and r = 2 (rows lem_8_2_r3, lem_8_2_r2_linear,
lem_8_2_r2_conformal, lem_8_2_r2_compose, lem_8_2_r2_c_ne, lem_8_2_r2_substitute, lem_8_2_r2; statements copied verbatim
from Osserman/Paper/Statements8.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Tools: evaluation of substitutions (`eval_bind`), `q ∣ F_k - G_k` for all `k` gives `q ∣ f(F) - f(G)` (`bind_congr`,
induction on `f`), `f(φ·g) = φ^n f(g)` for `f` homogeneous of degree `n`, `B(Ax)` is linear with matrix `AB`.
r = 3: `Ψ` is constant; `φ⟨Ψ,x⟩ = -q⟨Cx,x⟩` (`lem_8_2_tangency`, a leading premise), `q` prime, `q ∤ φ`, so `q` divides
the linear form `⟨Ψ,x⟩`, which is therefore `0`. r = 2: `Ψ = Bx`; `|P|² = q³` gives `q ∣ |Bx|²`, so `|Bx|² = c₀|x|²` and
`B = cU`; the three congruences of the composition; `c ≠ 0` gives `q ∣ φ(Bx)`, and `x = B⁻¹y` gives `q ∣ φ`, false.
-/
import Osserman.Proofs.S86
import Osserman.Proofs.QPrime

namespace Osserman.Proofs.Lem82R2

open Osserman Matrix MvPolynomial

/-! ### Substitutions -/

lemma eval_bind (x : Vec 16) (g : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : MvPolynomial (Fin 16) ℝ) :
    eval x (bind₁ g f) = eval (fun k => eval x (g k)) f :=
  eval₂Hom_bind₁ (RingHom.id ℝ) x g f

/-- Substitution respects congruences modulo `q`. -/
lemma bind_congr {F G : Fin 16 → MvPolynomial (Fin 16) ℝ} (hFG : ∀ k, sqP 16 ∣ F k - G k)
    (f : MvPolynomial (Fin 16) ℝ) : sqP 16 ∣ bind₁ F f - bind₁ G f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [bind₁_C_right, bind₁_C_right, sub_self]
    exact dvd_zero _
  | add p p' hp hp' =>
    rw [map_add, map_add, add_sub_add_comm]
    exact dvd_add hp hp'
  | mul_X p k hp =>
    rw [map_mul, map_mul, bind₁_X_right, bind₁_X_right]
    have e : bind₁ F p * F k - bind₁ G p * G k = (bind₁ F p - bind₁ G p) * F k + bind₁ G p * (F k - G k) := by
      ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right hp _) (Dvd.dvd.mul_left (hFG k) _)

/-- `f(φ·g) = φ^n f(g)` for `f` homogeneous of degree `n`. -/
lemma bind_mul_homog {f : MvPolynomial (Fin 16) ℝ} {n : ℕ} (hf : f.IsHomogeneous n) (φ : MvPolynomial (Fin 16) ℝ)
    (g : Fin 16 → MvPolynomial (Fin 16) ℝ) : bind₁ (fun k => φ * g k) f = φ ^ n * bind₁ g f :=
  MvPolynomial.funext fun x => by
    rw [eval_bind, eval_mul, eval_pow, eval_bind]
    have e : (fun k => eval x (φ * g k)) = eval x φ • fun k => eval x (g k) := funext fun k => by simp
    rw [e, S8Tools.eval_smul_of_homogeneous hf]

/-- `(A(Bx))_j`: the substitution `x ↦ Bx` in `Ax` is `(AB)x`. -/
lemma bind_linP (A B : Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 16) : bind₁ (linP B) (linP A j) = linP (A * B) j :=
  MvPolynomial.funext fun x => by
    rw [eval_bind, show (fun k => eval x (linP B k)) = B *ᵥ x from S8Tools.evalField_linP B x]
    exact (congrFun (S8Tools.evalField_linP A (B *ᵥ x)) j).trans
      (by rw [Matrix.mulVec_mulVec]; exact (congrFun (S8Tools.evalField_linP (A * B) x) j).symm)

lemma linP_one (i : Fin 16) : linP (1 : Matrix (Fin 16) (Fin 16) ℝ) i = X i :=
  MvPolynomial.funext fun x => (congrFun (S8Tools.evalField_linP 1 x) i).trans (by rw [Matrix.one_mulVec, eval_X])

lemma bind_sqP (F : Fin 16 → MvPolynomial (Fin 16) ℝ) : bind₁ F (sqP 16) = ∑ j, F j ^ 2 := by
  simp only [sqP, map_sum, map_pow, bind₁_X_right]

/-- (8.1), second identity, as polynomials: `∑ P_j² = q³`. -/
lemma sumsq_eq {P : Fin 16 → MvPolynomial (Fin 16) ℝ} (hP : CubicIdentities P) : ∑ j, P j ^ 2 = sqP 16 ^ 3 :=
  MvPolynomial.funext fun x => by
    rw [map_sum, map_pow, Poly.eval_sqP, ← (hP x).2.1]
    simp only [dotProduct, evalField, sq, map_mul]

/-- (8.1), third identity, as polynomials: `P(P(x)) = -q⁴x`. -/
lemma bind_P_P {P : Fin 16 → MvPolynomial (Fin 16) ℝ} (hP : CubicIdentities P) (j : Fin 16) :
    bind₁ P (P j) = -(sqP 16 ^ 4 * X j) :=
  MvPolynomial.funext fun x => by
    rw [eval_bind]
    refine (congrFun (hP x).2.2 j).trans ?_
    simp [Poly.eval_sqP]

lemma q_prime : Prime (sqP 16) := QPrime.s8_q_prime_proved.2.1

/-- A nonzero linear form is not divisible by `q`. -/
lemma not_dvd_linear {f : MvPolynomial (Fin 16) ℝ} (hf : f.IsHomogeneous 1) (h0 : f ≠ 0) : ¬ sqP 16 ∣ f :=
  fun hd => by have := S86.two_le_of_dvd hf h0 hd; omega

/-! ### r = 3 -/

/-- The type of row `lem_8_2_tangency` (a leading premise). -/
abbrev TangHyp : Prop := ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (r : ℕ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P r φ Ψ Cm →
    φ * ∑ j, Ψ j * X j = -(sqP 16 * quadP Cm)

/-- Row `lem_8_2_r3`. -/
theorem lem_8_2_r3_proved (htang : TangHyp) (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 3 φ Ψ Cm) :
    (∃ ψ : Vec 16, ∀ j, Ψ j = MvPolynomial.C (ψ j)) ∧ sqP 16 ∣ ∑ j, Ψ j * X j ∧ ∀ j, Ψ j = 0 := by
  have e := htang P 3 φ Ψ Cm h
  obtain ⟨-, -, -, -, -, hφq, hΨ, -⟩ := h
  have hconst : ∀ j, Ψ j = C ((Ψ j).coeff 0) := fun j =>
    totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hΨ j).totalDegree_le)
  have hdvd : sqP 16 ∣ ∑ j, Ψ j * X j :=
    (q_prime.dvd_or_dvd ⟨-quadP Cm, by rw [e]; ring⟩).resolve_left hφq
  refine ⟨⟨fun j => (Ψ j).coeff 0, hconst⟩, hdvd, ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Vec 16, ∀ j, Ψ j = C (ψ j) := ⟨_, hconst⟩
  simp only [hψ] at hdvd ⊢
  have hL : (∑ j, C (ψ j) * X j).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => by simpa using (isHomogeneous_C (Fin 16) (ψ j)).mul (isHomogeneous_X ℝ j)
  have hL0 : ∑ j, C (ψ j) * X j = 0 := by
    by_contra hne
    exact not_dvd_linear hL hne hdvd
  intro j
  have ev := congrArg (eval (Pi.single j 1)) hL0
  simp [Pi.single_apply] at ev
  rw [ev, map_zero]

/-! ### r = 2 -/

/-- Row `lem_8_2_r2_linear`. -/
theorem lem_8_2_r2_linear_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ Ψ Cm) :
    ∃ B : Matrix (Fin 16) (Fin 16) ℝ, ∀ j, Ψ j = linP B j := by
  obtain ⟨-, -, -, -, -, -, hΨ, -⟩ := h
  obtain ⟨B, hB⟩ := ThmEFrames.thm_E_linear_fields_proved Ψ 1 odd_one (by norm_num) hΨ
  exact ⟨B, fun j => MvPolynomial.funext fun x =>
    (congrFun (hB x) j).trans (congrFun (S8Tools.evalField_linP B x) j).symm⟩

/-- A matrix with `|Bx|² = c|x|²` for every `x` has `BᵀB = cI`. -/
lemma gram_of_norm {B : Matrix (Fin 16) (Fin 16) ℝ} {c : ℝ}
    (h : ∀ x : Vec 16, (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = c * (x ⬝ᵥ x)) : Bᵀ * B = c • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by
  have hxy : ∀ x y : Vec 16, (B *ᵥ x) ⬝ᵥ (B *ᵥ y) = c * (x ⬝ᵥ y) := fun x y => by
    have h1 := h (x + y)
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add] at h1
    rw [h x, h y, dotProduct_comm (B *ᵥ y) (B *ᵥ x), dotProduct_comm y x] at h1
    linear_combination h1 / 2
  ext a b
  have e := hxy (Pi.single a 1) (Pi.single b 1)
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one, dotProduct_single, mul_one, Pi.single_apply] at e
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have e2 : ∑ i, Bᵀ a i * B i b = B.col a ⬝ᵥ B.col b := Finset.sum_congr rfl fun i _ => rfl
  rw [e2, e]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [ite_eq_right (Ne.symm hab), ite_eq_right hab]

/-- Row `lem_8_2_r2_conformal`. -/
theorem lem_8_2_r2_conformal_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (B Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ (linP B) Cm) :
    sqP 16 ∣ (∑ j, P j ^ 2) - φ ^ 2 * ∑ j, linP B j ^ 2 ∧ sqP 16 ∣ ∑ j, linP B j ^ 2 ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∃ U ∈ Matrix.orthogonalGroup (Fin 16) ℝ, B = c • U := by
  obtain ⟨-, hP, -, -, -, hφq, -, hPdef⟩ := h
  have h1 : sqP 16 ∣ (∑ j, P j ^ 2) - φ ^ 2 * ∑ j, linP B j ^ 2 := by
    refine ⟨∑ j, (2 * φ * linP B j * linP Cm j + sqP 16 * linP Cm j ^ 2), ?_⟩
    simp only [hPdef]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hq3 : sqP 16 ∣ ∑ j, P j ^ 2 := by
    rw [sumsq_eq hP]
    exact dvd_pow_self _ (by norm_num)
  have h3 : sqP 16 ∣ φ ^ 2 * ∑ j, linP B j ^ 2 := by
    have e := dvd_sub hq3 h1
    rwa [sub_sub_cancel] at e
  have h2 : sqP 16 ∣ ∑ j, linP B j ^ 2 :=
    (q_prime.dvd_or_dvd h3).resolve_left fun hd => hφq (q_prime.dvd_of_dvd_pow hd)
  refine ⟨h1, h2, ?_⟩
  have hSh : (∑ j, linP B j ^ 2).IsHomogeneous (0 + 2) :=
    IsHomogeneous.sum _ _ _ fun j _ => by simpa using (S83.linP_homogeneous B j).pow 2
  obtain ⟨g, hg, hSg⟩ := S86.dvd_homog_eq hSh h2
  have hgC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hg.totalDegree_le)
  have hc0 : ∀ x : Vec 16, (B *ᵥ x) ⬝ᵥ (B *ᵥ x) = g.coeff 0 * (x ⬝ᵥ x) := fun x => by
    have e := congrArg (eval x) hSg
    rw [hgC, map_mul, eval_C, Poly.eval_sqP, map_sum] at e
    rw [mul_comm, ← e, ← S8Tools.evalField_linP B x]
    simp only [dotProduct, evalField, sq, map_mul]
  have hG := gram_of_norm hc0
  have hc0n : 0 ≤ g.coeff 0 := by
    have e := hc0 (Pi.single 0 1)
    rw [show (Pi.single 0 1 : Vec 16) ⬝ᵥ Pi.single 0 1 = 1 by simp, mul_one] at e
    rw [← e]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  refine ⟨Real.sqrt (g.coeff 0), Real.sqrt_nonneg _, ?_⟩
  by_cases hz : g.coeff 0 = 0
  · refine ⟨1, one_mem _, ?_⟩
    rw [hz, Real.sqrt_zero, zero_smul]
    exact Matrix.ext_iff_mulVec.mpr fun v => by
      rw [Matrix.zero_mulVec]
      exact dotProduct_self_eq_zero.mp (by rw [hc0 v, hz, zero_mul])
  · have hs : Real.sqrt (g.coeff 0) ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne hc0n (Ne.symm hz))).ne'
    refine ⟨(Real.sqrt (g.coeff 0))⁻¹ • B, ?_, by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]⟩
    rw [Matrix.mem_orthogonalGroup_iff' (Fin 16) ℝ, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hG, smul_smul, smul_smul, ← mul_inv,
      Real.mul_self_sqrt hc0n, inv_mul_cancel₀ hz, one_smul]

/-- Row `lem_8_2_r2_compose`. -/
theorem lem_8_2_r2_compose_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (B Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ (linP B) Cm) :
    ∀ j, sqP 16 ∣ bind₁ P (P j) ∧ sqP 16 ∣ bind₁ P (P j) - bind₁ P φ * bind₁ P (linP B j) ∧
      sqP 16 ∣ bind₁ P φ * bind₁ P (linP B j) - φ ^ 3 * bind₁ (linP B) φ * linP (B * B) j := by
  obtain ⟨-, hP, -, -, hφh, -, -, hPdef⟩ := h
  have hcong : ∀ k, sqP 16 ∣ P k - φ * linP B k := fun k => ⟨linP Cm k, by rw [hPdef k]; ring⟩
  intro j
  refine ⟨?_, ?_, ?_⟩
  · rw [bind_P_P hP]
    exact ⟨-(sqP 16 ^ 3 * X j), by ring⟩
  · have e : bind₁ P (P j) - bind₁ P φ * bind₁ P (linP B j) = bind₁ P (sqP 16) * bind₁ P (linP Cm j) := by
      conv_lhs => rw [hPdef j]
      rw [map_add, map_mul, map_mul]
      ring
    rw [e, bind_sqP, sumsq_eq hP]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by norm_num)) _
  · have c1 := bind_congr hcong φ
    rw [bind_mul_homog hφh] at c1
    have c2 := bind_congr hcong (linP B j)
    rw [bind_mul_homog (S83.linP_homogeneous B j), pow_one, bind_linP] at c2
    have e : bind₁ P φ * bind₁ P (linP B j) - φ ^ 3 * bind₁ (linP B) φ * linP (B * B) j =
        (bind₁ P φ - φ ^ 2 * bind₁ (linP B) φ) * bind₁ P (linP B j) +
          φ ^ 2 * bind₁ (linP B) φ * (bind₁ P (linP B j) - φ * linP (B * B) j) := by ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_right c1 _) (Dvd.dvd.mul_left c2 _)

/-- Row `lem_8_2_r2_c_ne`. -/
theorem lem_8_2_r2_c_ne_proved :
    (∀ (B U : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ), c ≠ 0 → U ∈ Matrix.orthogonalGroup (Fin 16) ℝ → B = c • U →
        IsUnit (B * B).det) ∧
      ∀ (φ : MvPolynomial (Fin 16) ℝ) (B : Matrix (Fin 16) (Fin 16) ℝ), ¬ sqP 16 ∣ φ → IsUnit (B * B).det →
        (∀ j, sqP 16 ∣ φ ^ 3 * bind₁ (linP B) φ * linP (B * B) j) → sqP 16 ∣ bind₁ (linP B) φ := by
  refine ⟨fun B U c hc hU hB => ?_, fun φ B hφq hdet hall => ?_⟩
  · have hUd : U.det ≠ 0 := by
      have e := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff' (Fin 16) ℝ).mp hU)
      rw [Matrix.det_mul, Matrix.det_one] at e
      exact right_ne_zero_of_mul_eq_one e
    rw [isUnit_iff_ne_zero, Matrix.det_mul, hB, Matrix.det_smul]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) hUd) (mul_ne_zero (pow_ne_zero _ hc) hUd)
  · obtain ⟨j, hj⟩ : ∃ j, linP (B * B) j ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      refine isUnit_iff_ne_zero.mp hdet (Matrix.det_eq_zero_of_row_eq_zero 0 fun k => ?_)
      have e := congrArg (eval (Pi.single k 1)) (hcon 0)
      have e2 := congrFun (S8Tools.evalField_linP (B * B) (Pi.single k 1)) 0
      rw [Matrix.mulVec_single_one] at e2
      rw [map_zero] at e
      exact e2.symm.trans e
    rcases q_prime.dvd_or_dvd (hall j) with hd | hd
    · rcases q_prime.dvd_or_dvd hd with hd' | hd'
      · exact absurd (q_prime.dvd_of_dvd_pow hd') hφq
      · exact hd'
    · exact absurd hd (not_dvd_linear (S83.linP_homogeneous _ j) hj)

/-- Row `lem_8_2_r2_substitute`. -/
theorem lem_8_2_r2_substitute_proved (φ : MvPolynomial (Fin 16) ℝ) (B U : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ)
    (hc : c ≠ 0) (hU : U ∈ Matrix.orthogonalGroup (Fin 16) ℝ) (hB : B = c • U) (hdiv : sqP 16 ∣ bind₁ (linP B) φ) :
    sqP 16 ∣ φ := by
  have hUU : U * Uᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 16) ℝ).mp hU
  have hBB : B * (c⁻¹ • Uᵀ) = 1 := by
    rw [hB, Matrix.smul_mul, Matrix.mul_smul, hUU, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have h1 : bind₁ (linP (c⁻¹ • Uᵀ)) (bind₁ (linP B) φ) = φ := by
    rw [bind₁_bind₁]
    have e : (fun i => bind₁ (linP (c⁻¹ • Uᵀ)) (linP B i)) = X := funext fun i => by
      rw [bind_linP, hBB, linP_one]
    rw [e, bind₁_X_left]
    rfl
  have h2 : bind₁ (linP (c⁻¹ • Uᵀ)) (sqP 16) = C (c⁻¹ ^ 2) * sqP 16 := MvPolynomial.funext fun x => by
    rw [eval_bind, show (fun k => eval x (linP (c⁻¹ • Uᵀ) k)) = (c⁻¹ • Uᵀ) *ᵥ x from
      S8Tools.evalField_linP _ x, Matrix.smul_mulVec, S8Tools.eval_smul_of_homogeneous Poly.sqP_isHomogeneous,
      Poly.eval_sqP_mulVec Uᵀ (by rw [Matrix.transpose_transpose, hUU]), map_mul, eval_C]
  have h3 := map_dvd (bind₁ (linP (c⁻¹ • Uᵀ))) hdiv
  rw [h1, h2] at h3
  exact (dvd_mul_left _ _).trans h3

/-- Row `lem_8_2_r2`. -/
theorem lem_8_2_r2_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
    (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ) (h : Lem82Lift P 2 φ Ψ Cm) :
    ∀ j, Ψ j = 0 := by
  obtain ⟨B, hB⟩ := lem_8_2_r2_linear_proved P φ Ψ Cm h
  obtain rfl : Ψ = linP B := funext hB
  obtain ⟨-, -, -, -, -, hφq, -, -⟩ := id h
  obtain ⟨-, -, c, -, U, hU, hBU⟩ := lem_8_2_r2_conformal_proved P φ B Cm h
  by_cases hc : c = 0
  · intro j
    rw [hBU, hc, zero_smul]
    simp [linP]
  · exfalso
    have hdet := lem_8_2_r2_c_ne_proved.1 B U c hc hU hBU
    have hall : ∀ j, sqP 16 ∣ φ ^ 3 * bind₁ (linP B) φ * linP (B * B) j := fun j => by
      obtain ⟨h1, h2, h3⟩ := lem_8_2_r2_compose_proved P φ B Cm h j
      have hb := dvd_sub h1 h2
      rw [sub_sub_cancel] at hb
      have hc' := dvd_sub hb h3
      rwa [sub_sub_cancel] at hc'
    exact hφq (lem_8_2_r2_substitute_proved φ B U c hc hU hBU (lem_8_2_r2_c_ne_proved.2 φ B hφq hdet hall))

end Osserman.Proofs.Lem82R2

