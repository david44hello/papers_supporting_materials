/-
Osserman/Proofs/Six4a.lean — Theorem G of paper 013 (§9.4, sec_polynomial_gram.tex), the anisotropy step:
rows thm_G_nilpotent_self_adjoint_zero, thm_G_self_adjoint, thm_G_gram_pencil, thm_G_nilpotent, thm_G_q_pointS,
jacAlg_real, thm_G_degree_two, thm_G_Phi_scalar, thm_G_fraction_field.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SixPieces
import Osserman.Cited.Nik2006

namespace Osserman.Proofs.Six4

open Osserman Matrix

/-! ### thm_G_nilpotent_self_adjoint_zero -/

lemma adj_pow {K : Type*} [Field K] {n : ℕ} (H N : Matrix (Fin n) (Fin n) K)
    (hadj : ∀ v w : Fin n → K, (N *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ (H *ᵥ (N *ᵥ w))) (k : ℕ) :
    ∀ v w : Fin n → K, ((N ^ k) *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ (H *ᵥ ((N ^ k) *ᵥ w)) := by
  induction k with
  | zero => intro v w; simp
  | succ k ih =>
    intro v w
    rw [pow_succ, ← mulVec_mulVec, ih, hadj, mulVec_mulVec w N (N ^ k), ← pow_succ, ← pow_succ']

lemma zero_of_sq_zero {K : Type*} [Field K] {n : ℕ} (H P : Matrix (Fin n) (Fin n) K)
    (hanis : ∀ v : Fin n → K, v ⬝ᵥ (H *ᵥ v) = 0 → v = 0)
    (hadj : ∀ v w : Fin n → K, (P *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ (H *ᵥ (P *ᵥ w))) (hsq : P * P = 0) : P = 0 := by
  have hv : ∀ v, P *ᵥ v = 0 := by
    intro v
    apply hanis
    rw [hadj, mulVec_mulVec v P P, hsq, zero_mulVec, mulVec_zero, dotProduct_zero]
  exact ext_of_mulVec_single fun i => by rw [hv, zero_mulVec]

theorem thm_G_nilpotent_self_adjoint_zero_proved {K : Type*} [Field K] {n : ℕ} (H N : Matrix (Fin n) (Fin n) K)
    (hanis : ∀ v : Fin n → K, v ⬝ᵥ (H *ᵥ v) = 0 → v = 0)
    (hadj : ∀ v w : Fin n → K, (N *ᵥ v) ⬝ᵥ (H *ᵥ w) = v ⬝ᵥ (H *ᵥ (N *ᵥ w))) (hnil : IsNilpotent N) : N = 0 := by
  obtain ⟨e, he⟩ := hnil
  have key : ∀ k : ℕ, N ^ (k + 1) = 0 → N = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro h
      apply ih
      apply zero_of_sq_zero H (N ^ (k + 1)) hanis (adj_pow H N hadj (k + 1))
      rw [← pow_add, show k + 1 + (k + 1) = (k + 1 + 1) + k by omega, pow_add, h, zero_mul]
  cases e with
  | zero =>
    have h1 : (1 : Matrix (Fin n) (Fin n) K) = 0 := by simpa using he
    calc N = N * 1 := (Matrix.mul_one N).symm
      _ = 0 := by rw [h1, Matrix.mul_zero]
  | succ k => exact key k he

/-! ### thm_G_self_adjoint -/

lemma dot_mulVec_left {K : Type*} [CommRing K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (v u : Fin n → K) :
    (A *ᵥ v) ⬝ᵥ u = v ⬝ᵥ (Aᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

theorem thm_G_self_adjoint_proved {ν : ℕ} (μ : Fin ν → ℝ) (hμ : ∀ i, μ i ≠ 0) (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15)
    (h1 : Φ1ᵀ = Φ1) (h0 : Φ0ᵀ = Φ0) (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼) :
    let Λe := (diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF)
    let N := Λe * GramAt α Φ1 Φ0
    Λe⁻¹ * N = GramAt α Φ1 Φ0 ∧ (GramAt α Φ1 Φ0)ᵀ = GramAt α Φ1 Φ0 ∧
      ∀ v w : Fin ν → 𝔼, (N *ᵥ v) ⬝ᵥ (Λe⁻¹ *ᵥ w) = v ⬝ᵥ (Λe⁻¹ *ᵥ (N *ᵥ w)) := by
  intro Λe N
  have hΛ : Λe = diagonal fun i => ((algebraMap RatF15 𝔼).comp ofRealF) (μ i) :=
    diagonal_map (map_zero _)
  have hdet : IsUnit Λe.det := by
    rw [hΛ, det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    exact (map_ne_zero _).mpr (hμ i)
  have hinvN : Λe⁻¹ * N = GramAt α Φ1 Φ0 := by
    show Λe⁻¹ * (Λe * GramAt α Φ1 Φ0) = GramAt α Φ1 Φ0
    rw [← Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hGT : (GramAt α Φ1 Φ0)ᵀ = GramAt α Φ1 Φ0 := by
    simp only [GramAt, transpose_add, transpose_smul, transpose_one, ← transpose_map, h1, h0]
  have hΛT : Λeᵀ = Λe := by rw [hΛ, diagonal_transpose]
  have hNT : Nᵀ * Λe⁻¹ = GramAt α Φ1 Φ0 := by
    show (Λe * GramAt α Φ1 Φ0)ᵀ * Λe⁻¹ = GramAt α Φ1 Φ0
    rw [transpose_mul, hGT, hΛT, Matrix.mul_assoc, mul_nonsing_inv _ hdet, Matrix.mul_one]
  refine ⟨hinvN, hGT, fun v w => ?_⟩
  rw [dot_mulVec_left, mulVec_mulVec, mulVec_mulVec, hNT, hinvN]

/-! ### thm_G_gram_pencil -/

theorem thm_G_gram_pencil_proved {ν : ℕ} (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15)
    (hMX : MXᵀ * MX = 1) :
    (factorS MX MY)ᵀ * factorS MX MY = GramS (Phi1 MX MY) (Phi0 MY) ∧ (Phi1 MX MY)ᵀ = Phi1 MX MY ∧
      (Phi0 MY)ᵀ = Phi0 MY := by
  refine ⟨?_, ?_, ?_⟩
  · set A := (MX.map ofRealF).map (Polynomial.C : RatF15 →+* Polynomial RatF15) with hA
    set B := MY.map (Polynomial.C : RatF15 →+* Polynomial RatF15) with hB
    have hfac : factorS MX MY = (Polynomial.X : Polynomial RatF15) • A + B := by
      ext i j; simp [factorS, hA, hB]
    have hAA : Aᵀ * A = 1 := by
      rw [hA, ← transpose_map, ← Matrix.map_mul, ← transpose_map, ← Matrix.map_mul, hMX]
      simp
    have hG : GramS (Phi1 MX MY) (Phi0 MY) =
        (Polynomial.X ^ 2 : Polynomial RatF15) • (1 : Matrix (Fin ν) (Fin ν) (Polynomial RatF15)) +
          (Polynomial.X : Polynomial RatF15) • (Aᵀ * B + Bᵀ * A) + Bᵀ * B := by
      simp only [GramS, Phi1, Phi0, Matrix.map_add _ (map_add (Polynomial.C : RatF15 →+* Polynomial RatF15)),
        Matrix.map_mul, transpose_map, hA, hB]
    rw [hfac, hG]
    simp only [transpose_add, transpose_smul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, hAA, smul_smul, smul_add]
    rw [pow_two]
    abel
  · simp only [Phi1, transpose_add, transpose_mul, transpose_transpose]
    exact add_comm _ _
  · simp only [Phi0, transpose_mul, transpose_transpose]

/-! ### thm_G_nilpotent -/

theorem thm_G_nilpotent_proved {ν : ℕ} (μ : Fin ν → ℝ) (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15)
    (hspec : SpectralPencil μ Φ1 Φ0) (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) :
    ((diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0).charpoly = Polynomial.X ^ ν ∧
      IsNilpotent ((diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Polynomial RatF15 →+* 𝔼, ψ = Polynomial.eval₂RingHom (algebraMap RatF15 𝔼) α := ⟨_, rfl⟩
  have hmap : ((diagonal μ).map (Polynomial.C.comp ofRealF) * GramS Φ1 Φ0).map ψ =
      (diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0 := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    · ext i j; simp [hψ]
    · ext i j
      simp only [hψ, GramS, GramAt, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, Polynomial.coe_eval₂RingHom]
      split_ifs <;> simp <;> ring
  have hchar : ((diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0).charpoly =
      Polynomial.X ^ ν := by
    rw [← hmap, charpoly_map, hspec, Polynomial.map_prod]
    have hq : ψ (Polynomial.X ^ 2 + Polynomial.C dF) = 0 := by
      simp only [hψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, hα, neg_add_cancel]
    have : ∀ i, Polynomial.map ψ (Polynomial.X - Polynomial.C ((Polynomial.X ^ 2 + Polynomial.C dF) *
        Polynomial.C (ofRealF (μ i)))) = Polynomial.X := by
      intro i
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_mul, hq, zero_mul, map_zero, sub_zero]
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨hchar, ⟨ν, ?_⟩⟩
  have := aeval_self_charpoly ((diagonal μ).map ((algebraMap RatF15 𝔼).comp ofRealF) * GramAt α Φ1 Φ0)
  rwa [hchar, map_pow, Polynomial.aeval_X] at this

/-! ### thm_G_q_pointS -/

theorem thm_G_q_pointS_proved (Xa : Vec 16) (f : Fin 15 → Vec 16) (hX : Xa ⬝ᵥ Xa = 1)
    (hXf : ∀ i, Xa ⬝ᵥ f i = 0) (hf : ∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) :
    ∑ a, pointS Xa f a ^ 2 = Polynomial.X ^ 2 + Polynomial.C dF := by
  set p : Fin 16 → RatF15 := fun a => ofRealF (Xa a) with hp
  set q : Fin 16 → RatF15 := fun a => ∑ i, yF i * ofRealF (f i a) with hq
  have e1 : ∑ a, p a ^ 2 = 1 := by
    have : ofRealF (Xa ⬝ᵥ Xa) = 1 := by rw [hX, map_one]
    rw [← this, dotProduct, map_sum]
    simp [hp, sq]
  have e2 : ∑ a, p a * q a = 0 := by
    simp only [hp, hq, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have : ofRealF (Xa ⬝ᵥ f i) = 0 := by rw [hXf, map_zero]
    calc ∑ a, ofRealF (Xa a) * (yF i * ofRealF (f i a)) = yF i * ofRealF (Xa ⬝ᵥ f i) := by
          rw [dotProduct, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [map_mul]; ring
      _ = 0 := by rw [this, mul_zero]
  have e3 : ∑ a, q a ^ 2 = dF := by
    have hqa : ∀ a, q a ^ 2 = ∑ i, ∑ j, yF i * yF j * (ofRealF (f i a) * ofRealF (f j a)) := by
      intro a
      simp only [hq, sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hqa]
    rw [Finset.sum_comm]
    simp only [dF]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    have hij : ∀ j, ∑ a, yF i * yF j * (ofRealF (f i a) * ofRealF (f j a)) =
        yF i * yF j * ofRealF (f i ⬝ᵥ f j) := by
      intro j
      rw [← Finset.mul_sum, dotProduct, map_sum]
      simp only [map_mul]
    simp only [hij, hf]
    simp [sq]
  have hpt : ∀ a, pointS Xa f a ^ 2 = Polynomial.C (p a ^ 2) * Polynomial.X ^ 2 +
      Polynomial.C (2 * (p a * q a)) * Polynomial.X + Polynomial.C (q a ^ 2) := by
    intro a
    simp only [pointS, hp, hq, map_pow, map_mul, map_ofNat]
    ring
  simp only [hpt, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, ← map_sum, ← map_sum, ← Finset.mul_sum, e1, e2, e3]
  simp

/-! ### jacAlg_real -/

theorem jacAlg_real_proved (R : CurvTensor 16) (μ0 : ℝ) (x : Vec 16) :
    jacAlg R μ0 (RingHom.id ℝ) x = R.jacobi x - μ0 • Osserman.Pi x := by
  have hx : x = ∑ a, x a • (Pi.single a 1 : Vec 16) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have hop : ∀ k, R.op (Pi.single k 1) x x =
      ∑ a, ∑ b, (x a * x b) • R.op (Pi.single k 1) (Pi.single a 1) (Pi.single b 1) := by
    intro k
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  ext j k
  simp only [jacAlg, Matrix.of_apply, RingHom.id_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    CurvTensor.jacobi, LinearMap.toMatrix'_apply, CurvTensor.jacobiMap, LinearMap.coe_mk, AddHom.coe_mk, hop,
    Finset.sum_apply, Pi.smul_apply, Osserman.Pi, Matrix.one_apply, vecMulVec_apply, dotProduct]
  split_ifs <;> simp [sq]

/-! ### thm_G_degree_two: `𝔽` is formally real, `-d` is not a square, `[𝔼 : 𝔽] = 2` -/

lemma isSumSq_exists {R : Type*} [CommSemiring R] {s : R} (hs : IsSumSq s) :
    ∃ (k : ℕ) (x : Fin k → R), s = ∑ i, x i * x i := by
  induction hs with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | @sq_add a s hs ih =>
    obtain ⟨k, x, rfl⟩ := ih
    exact ⟨k + 1, Fin.cons a x, by simp [Fin.sum_univ_succ]⟩

/-- Real polynomials: `P² + Σ Qᵢ² = 0` forces `P = 0` (evaluate at every real point). -/
lemma poly_sq_eq_zero {k : ℕ} (P : MvPolynomial (Fin 15) ℝ) (Q : Fin k → MvPolynomial (Fin 15) ℝ)
    (h : P * P + ∑ i, Q i * Q i = 0) : P = 0 := by
  apply MvPolynomial.funext
  intro x
  have hx := congrArg (MvPolynomial.eval x) h
  simp only [map_add, map_sum, map_mul, map_zero] at hx
  have h1 : 0 ≤ ∑ i, MvPolynomial.eval x (Q i) * MvPolynomial.eval x (Q i) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h2 : MvPolynomial.eval x P * MvPolynomial.eval x P = 0 := by
    nlinarith [mul_self_nonneg (MvPolynomial.eval x P)]
  rw [map_zero]
  exact mul_self_eq_zero.1 h2

/-- Rational functions: `a² + Σ xᵢ² = 0` forces `a = 0` (clear the denominators). -/
lemma ratF_sq_eq_zero {k : ℕ} (a : RatF15) (x : Fin k → RatF15) (h : a * a + ∑ i, x i * x i = 0) : a = 0 := by
  classical
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (MvPolynomial (Fin 15) ℝ))
    (Finset.univ : Finset (Fin (k + 1))) (Fin.cons a x : Fin (k + 1) → RatF15)
  choose P hP using fun i => RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
  set B := algebraMap (MvPolynomial (Fin 15) ℝ) RatF15 b with hB
  have hb0 : B ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hP' : ∀ i, algebraMap (MvPolynomial (Fin 15) ℝ) RatF15 (P i) = B * (Fin.cons a x : Fin (k + 1) → RatF15) i :=
    fun i => by rw [hP i, Algebra.smul_def]
  have key : P 0 * P 0 + ∑ i : Fin k, P i.succ * P i.succ = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 15) ℝ) RatF15
    rw [map_zero, map_add, map_sum]
    simp only [map_mul, hP', Fin.cons_zero, Fin.cons_succ]
    have e : ∀ i : Fin k, B * x i * (B * x i) = B ^ 2 * (x i * x i) := fun i => by ring
    simp only [e, ← Finset.mul_sum]
    rw [show B * a * (B * a) + B ^ 2 * ∑ i, x i * x i = B ^ 2 * (a * a + ∑ i, x i * x i) by ring, h, mul_zero]
  have h0 := hP' 0
  rw [poly_sq_eq_zero _ _ key, map_zero, Fin.cons_zero] at h0
  exact (mul_eq_zero.1 h0.symm).resolve_left hb0

instance : IsFormallyReal RatF15 :=
  IsFormallyReal.of_eq_zero_of_eq_zero_of_mul_self_add fun {_ a} hs h => by
    obtain ⟨k, x, rfl⟩ := isSumSq_exists hs
    exact ratF_sq_eq_zero a x h

lemma dF_not_sq (c : RatF15) : c ^ 2 ≠ -dF := by
  intro hc
  have hy : yF 0 = 0 := by
    apply ratF_sq_eq_zero (yF 0) (Fin.cons c fun i : Fin 14 => yF i.succ)
    rw [Fin.sum_univ_succ, Fin.cons_zero]
    simp only [Fin.cons_succ]
    have hd : dF = yF 0 * yF 0 + ∑ i : Fin 14, yF i.succ * yF i.succ := by
      simp only [dF, Fin.sum_univ_succ, sq]
    linear_combination hc - hd
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 15) ℝ) = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 15) ℝ) RatF15
    rw [map_zero]
    exact hy
  exact MvPolynomial.X_ne_zero 0 hX

theorem thm_G_degree_two_proved (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    IsFormallyReal RatF15 ∧ (∀ c : RatF15, c ^ 2 ≠ -dF) ∧ Module.finrank RatF15 𝔼 = 2 := by
  refine ⟨inferInstance, dF_not_sq, ?_⟩
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [Polynomial.natDegree_X_pow_add_C]
      decide
    · intro c hc
      rw [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hc
      exact dF_not_sq c (by linear_combination hc)
  have hmon : (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15).Monic :=
    Polynomial.monic_X_pow_add_C _ two_ne_zero
  have haeval : Polynomial.aeval α (Polynomial.X ^ 2 + Polynomial.C dF : Polynomial RatF15) = 0 := by
    simp [hα]
  have hint : IsIntegral RatF15 α := ⟨_, hmon, by rwa [Polynomial.aeval_def] at haeval⟩
  have hmin := minpoly.eq_of_irreducible_of_monic hirr haeval hmon
  have h2 := IntermediateField.adjoin.finrank hint
  rw [← hmin, Polynomial.natDegree_X_pow_add_C, hgen, IntermediateField.finrank_top'] at h2
  exact h2

/-! ### thm_G_Phi_scalar -/

lemma one_alpha_indep (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) :
    LinearIndependent RatF15 ![(1 : 𝔼), α] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    rw [map_zero, zero_mul, add_zero] at hst
    exact ⟨(map_eq_zero_iff _ (algebraMap RatF15 𝔼).injective).1 hst, rfl⟩
  · exfalso
    have htne : algebraMap RatF15 𝔼 t ≠ 0 := (map_ne_zero _).2 ht
    have hα' : algebraMap RatF15 𝔼 (-(s / t)) = α := by
      rw [map_neg, map_div₀]
      field_simp
      linear_combination -hst
    apply dF_not_sq (-(s / t))
    apply (algebraMap RatF15 𝔼).injective
    rw [map_pow, hα', hα, map_neg]

theorem thm_G_Phi_scalar_proved {ν : ℕ} (Φ1 Φ0 : Matrix (Fin ν) (Fin ν) RatF15) (𝔼 : Type*) [Field 𝔼]
    [Algebra RatF15 𝔼] (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (_hgen : IntermediateField.adjoin RatF15 {α} = ⊤)
    (h : Φ0.map (algebraMap RatF15 𝔼) - algebraMap RatF15 𝔼 dF • (1 : Matrix (Fin ν) (Fin ν) 𝔼) +
      α • Φ1.map (algebraMap RatF15 𝔼) = 0) :
    LinearIndependent RatF15 ![(1 : 𝔼), α] ∧ Φ1 = 0 ∧ Φ0 = dF • (1 : Matrix (Fin ν) (Fin ν) RatF15) := by
  have hli := one_alpha_indep 𝔼 α hα
  have hij : ∀ i j, (Φ0 i j - dF * (1 : Matrix (Fin ν) (Fin ν) RatF15) i j) • (1 : 𝔼) + Φ1 i j • α = 0 := by
    intro i j
    have hc := congrFun (congrFun h i) j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply] at hc
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, map_sub, map_mul]
    rcases eq_or_ne i j with rfl | hne
    · simp only [Matrix.one_apply_eq, map_one, mul_one] at hc ⊢
      linear_combination hc
    · simp only [Matrix.one_apply_ne hne, map_zero, mul_zero] at hc ⊢
      linear_combination hc
  have hc := fun i j => LinearIndependent.pair_iff.1 hli _ _ (hij i j)
  refine ⟨hli, ?_, ?_⟩
  · ext i j
    exact (hc i j).2
  · ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact sub_eq_zero.1 (hc i j).1

/-! ### thm_G_fraction_field -/

section fraction

variable {𝔼 : Type*} [Field 𝔼] [Algebra RatF15 𝔼]

/-- `ι : ℝ[y] → 𝔼`. -/
noncomputable def iotaE : MvPolynomial (Fin 15) ℝ →+* 𝔼 :=
  (algebraMap RatF15 𝔼).comp (algebraMap (MvPolynomial (Fin 15) ℝ) RatF15)

/-- `ψ : ℝ[s, y] → 𝔼`, `s ↦ α`, `y_i ↦ y_i`. -/
noncomputable def evE (α : 𝔼) : MvPolynomial (Fin 16) ℝ →+* 𝔼 :=
  MvPolynomial.eval₂Hom ((algebraMap RatF15 𝔼).comp ofRealF)
    (Fin.cons α (fun i : Fin 15 => algebraMap RatF15 𝔼 (yF i)) : Fin 16 → 𝔼)

lemma evE_eq (α : 𝔼) : evE α = (Polynomial.eval₂RingHom (iotaE (𝔼 := 𝔼)) α).comp
    (MvPolynomial.finSuccEquiv ℝ 15 : MvPolynomial (Fin (15 + 1)) ℝ →+* Polynomial (MvPolynomial (Fin 15) ℝ)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [evE, iotaE, ofRealF, MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [evE, MvPolynomial.finSuccEquiv_X_zero]
    · simp [evE, iotaE, yF, MvPolynomial.finSuccEquiv_X_succ]

lemma iotaE_sqP : iotaE (𝔼 := 𝔼) (sqP 15) = algebraMap RatF15 𝔼 dF := by
  simp [iotaE, sqP, dF, yF, map_sum, map_pow]

lemma evE_C (α : 𝔼) (m : MvPolynomial (Fin 15) ℝ) :
    evE α ((MvPolynomial.finSuccEquiv ℝ 15).symm (Polynomial.C m)) = iotaE m := by
  rw [evE_eq, RingHom.comp_apply]
  simp

lemma evE_X0 (α : 𝔼) : evE α (MvPolynomial.X 0) = α := by
  simp [evE]

lemma finSucc_sqP : MvPolynomial.finSuccEquiv ℝ 15 (sqP 16) = Polynomial.X ^ 2 + Polynomial.C (sqP 15) := by
  simp only [sqP, map_sum, map_pow]
  rw [Fin.sum_univ_succ, MvPolynomial.finSuccEquiv_X_zero]
  simp only [MvPolynomial.finSuccEquiv_X_succ, ← map_pow, ← map_sum]

lemma evE_sqP (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) : evE α (sqP 16) = 0 := by
  rw [evE_eq, RingHom.comp_apply]
  erw [finSucc_sqP]
  simp [iotaE_sqP, hα]

lemma evE_ker (α : 𝔼) (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (p : MvPolynomial (Fin 16) ℝ) (hp : evE α p = 0) :
    p ∈ Ideal.span {sqP 16} := by
  set e := MvPolynomial.finSuccEquiv ℝ 15
  set g : Polynomial (MvPolynomial (Fin 15) ℝ) := Polynomial.X ^ 2 + Polynomial.C (sqP 15) with hg
  have hmon : g.Monic := Polynomial.monic_X_pow_add_C _ two_ne_zero
  set P := e p with hP
  set r := P %ₘ g with hr
  have hdeg : r.degree ≤ 1 := by
    have h := Polynomial.degree_modByMonic_lt P hmon
    rw [hg, Polynomial.degree_X_pow_add_C two_pos] at h
    exact Order.le_of_lt_succ h
  have hrep := Polynomial.eq_X_add_C_of_degree_le_one hdeg
  have hgα : Polynomial.eval₂ (iotaE (𝔼 := 𝔼)) α g = 0 := by
    simp [hg, iotaE_sqP, hα]
  have hev : Polynomial.eval₂ (iotaE (𝔼 := 𝔼)) α r = 0 := by
    have h1 : evE α p = Polynomial.eval₂ iotaE α P := by rw [evE_eq, RingHom.comp_apply]; rfl
    rw [h1, ← Polynomial.modByMonic_add_div P g, Polynomial.eval₂_add, Polynomial.eval₂_mul, hgα, zero_mul,
      add_zero] at hp
    exact hp
  rw [hrep] at hev
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X] at hev
  have hli := one_alpha_indep 𝔼 α hα
  have hc := LinearIndependent.pair_iff.1 hli (algebraMap _ RatF15 (r.coeff 0)) (algebraMap _ RatF15 (r.coeff 1))
    (by rw [Algebra.smul_def, Algebra.smul_def, mul_one]; simp only [iotaE, RingHom.comp_apply] at hev
        linear_combination hev)
  have h0 : r.coeff 0 = 0 := IsFractionRing.injective (MvPolynomial (Fin 15) ℝ) RatF15 (by rw [hc.1, map_zero])
  have h1 : r.coeff 1 = 0 := IsFractionRing.injective (MvPolynomial (Fin 15) ℝ) RatF15 (by rw [hc.2, map_zero])
  have hr0 : r = 0 := by rw [hrep, h0, h1]; simp
  have hPg : P = g * (P /ₘ g) := by
    have := Polynomial.modByMonic_add_div P g
    rw [← hr, hr0, zero_add] at this
    exact this.symm
  have hpe : p = sqP 16 * e.symm (P /ₘ g) := by
    apply e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, finSucc_sqP, ← hg, ← hPg]
  rw [hpe]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end fraction

theorem thm_G_fraction_field_proved (𝔼 : Type*) [Field 𝔼] [Algebra RatF15 𝔼] (α : 𝔼)
    (hα : α ^ 2 = -algebraMap RatF15 𝔼 dF) (hgen : IntermediateField.adjoin RatF15 {α} = ⊤) :
    ∃ φ : (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) →+* 𝔼,
      (∀ p, φ (Ideal.Quotient.mk _ p) =
        MvPolynomial.eval₂ ((algebraMap RatF15 𝔼).comp ofRealF)
          (Fin.cons α (fun i : Fin 15 => algebraMap RatF15 𝔼 (yF i)) : Fin 16 → 𝔼) p) ∧
      (letI : Algebra (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼 := φ.toAlgebra
       IsFractionRing (MvPolynomial (Fin 16) ℝ ⧸ Ideal.span {sqP 16}) 𝔼) := by
  set I := Ideal.span {sqP 16}
  have hI : ∀ a ∈ I, evE α a = 0 := fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, evE_sqP α hα, mul_zero]
  set φ := Ideal.Quotient.lift I (evE α) hI with hφ
  have hmk : ∀ p, φ (Ideal.Quotient.mk I p) = evE α p := fun p => Ideal.Quotient.lift_mk I (evE α) hI
  refine ⟨φ, fun p => hmk p, ?_⟩
  let _ : Algebra (MvPolynomial (Fin 16) ℝ ⧸ I) 𝔼 := φ.toAlgebra
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun q hq => ?_
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hmk] at hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 (evE_ker α hα p hq)
  have : FaithfulSMul (MvPolynomial (Fin 16) ℝ ⧸ I) 𝔼 := (faithfulSMul_iff_algebraMap_injective _ 𝔼).2 hinj
  refine IsFractionRing.of_field _ 𝔼 fun z => ?_
  -- `z = a + bα` with `a, b ∈ 𝔽`
  have hli := one_alpha_indep 𝔼 α hα
  have hcard : Fintype.card (Fin 2) = Module.finrank RatF15 𝔼 := by
    rw [Fintype.card_fin, (thm_G_degree_two_proved 𝔼 α hα hgen).2.2]
  set bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hz := bs.sum_repr z
  rw [Fin.sum_univ_two, coe_basisOfLinearIndependentOfCardEqFinrank] at hz
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at hz
  obtain ⟨a1, a2, ha2, ha⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 15) ℝ) (bs.repr z 0)
  obtain ⟨b1, b2, hb2, hb⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 15) ℝ) (bs.repr z 1)
  have ha2' : iotaE (𝔼 := 𝔼) a2 ≠ 0 := by
    simp only [iotaE, RingHom.comp_apply]
    exact (map_ne_zero _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha2)
  have hb2' : iotaE (𝔼 := 𝔼) b2 ≠ 0 := by
    simp only [iotaE, RingHom.comp_apply]
    exact (map_ne_zero _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb2)
  set e := MvPolynomial.finSuccEquiv ℝ 15
  refine ⟨Ideal.Quotient.mk I (e.symm (Polynomial.C (a1 * b2)) + e.symm (Polynomial.C (b1 * a2)) * MvPolynomial.X 0),
    Ideal.Quotient.mk I (e.symm (Polynomial.C (a2 * b2))), ?_⟩
  change z = φ _ / φ _
  rw [hmk, hmk, map_add, map_mul (evE α), evE_C, evE_C, evE_C, evE_X0]
  simp only [map_mul]
  rw [← hz, ← ha, ← hb]
  simp only [map_div₀]
  change iotaE a1 / iotaE a2 + iotaE b1 / iotaE b2 * α = _
  field_simp

end Osserman.Proofs.Six4
