/-
Six4w.lean — the Lean-only row `thm_G_partner_nonvacuous` of paper 013 (Theorem G, sec_polynomial_gram.tex
l. 237-267): the hypotheses of `thm_G_conclude` can all hold, by an explicit Clifford witness.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Witness. `J_a = Jcl a` (a `Cl(8)`-structure on `ℝ^16`), `R` with `J_x = ∑_a (J_a x)(J_a x)ᵀ`, `μ₀ = 0` (reduced
multiplicity 7 at every unit `x`, the smallest reduced eigenvalue; the other one is `1`, of multiplicity 8), `μ = 1`,
`X = e_0`, `f_i = e_{i+1}`, `M_X = [J_a X]`, `M_Y = [J_a Y]`. The identity over `𝔽[s]` comes from the real identity
`J_x = ∑_a (J_a x)(J_a x)ᵀ`: both sides are the same quadratic polynomial in `x` (`MvPolynomial.funext`), and that
polynomial is evaluated at `z = sX + Y`.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.S8Example
import Osserman.Proofs.Six4a

namespace Osserman.Proofs.Six4w

open Osserman Matrix MvPolynomial Osserman.Proofs.CorDNonvacuous

/-! ### The two quadratic polynomials -/

/-- `(J_x)_{jk}` as a polynomial in `x`, in the shape of `jacAlg`. -/
noncomputable def jacQ (R : CurvTensor 16) (j k : Fin 16) : MvPolynomial (Fin 16) ℝ :=
  ∑ a, ∑ b, X a * X b * C (R.op (Pi.single k 1) (Pi.single a 1) (Pi.single b 1) j)

/-- `∑_c (J_c x)_j (J_c x)_k` as a polynomial in `x`. -/
noncomputable def cliffQ (j k : Fin 16) : MvPolynomial (Fin 16) ℝ :=
  ∑ c, (∑ b, C (Jcl c j b) * X b) * (∑ b, C (Jcl c k b) * X b)

lemma eval_jacQ {A : Type*} [CommRing A] (φ : ℝ →+* A) (z : Fin 16 → A) (R : CurvTensor 16) (j k : Fin 16) :
    eval₂Hom φ z (jacQ R j k) = jacAlg R 0 φ z j k := by
  simp [jacQ, jacAlg, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']

lemma eval_cliffQ {A : Type*} [CommRing A] (φ : ℝ →+* A) (z : Fin 16 → A) (j k : Fin 16) :
    eval₂Hom φ z (cliffQ j k) = ∑ c, (∑ b, φ (Jcl c j b) * z b) * (∑ b, φ (Jcl c k b) * z b) := by
  simp only [cliffQ, map_sum, map_mul, eval₂Hom_C, eval₂Hom_X']

/-- The real identity `J_x = ∑_c (J_c x)(J_c x)ᵀ`, as an identity of polynomials. -/
lemma jacQ_eq (R : CurvTensor 16) (hR : ∀ x, R.jacobi x = ∑ c, (1 : ℝ) • jfam (Jcl c) x) (j k : Fin 16) :
    jacQ R j k = cliffQ j k := by
  apply MvPolynomial.funext
  intro x
  change eval₂Hom (RingHom.id ℝ) x _ = eval₂Hom (RingHom.id ℝ) x _
  rw [eval_jacQ, eval_cliffQ, Six4.jacAlg_real_proved, zero_smul, sub_zero, hR]
  simp [Matrix.sum_apply, jfam, vecMulVec_apply, mulVec, dotProduct]

/-! ### The frames -/

/-- `M_X = [J_a X]`. -/
noncomputable def frameX (Xa : Vec 16) : Matrix (Fin 16) (Fin 8) ℝ := Matrix.of fun j a => (Jcl a *ᵥ Xa) j

/-- `M_Y = [J_a Y]` for a vector `Y` with coordinates in `𝔽`. -/
noncomputable def frameY (Yv : Fin 16 → RatF15) : Matrix (Fin 16) (Fin 8) RatF15 :=
  Matrix.of fun j a => ∑ b, ofRealF (Jcl a j b) * Yv b

/-- `Y = ∑ y_i f_i`. -/
noncomputable def pointY (f : Fin 15 → Vec 16) : Fin 16 → RatF15 := fun b => ∑ i, yF i * ofRealF (f i b)

lemma factorS_apply (Xa : Vec 16) (Yv : Fin 16 → RatF15) (j : Fin 16) (a : Fin 8) :
    factorS (frameX Xa) (frameY Yv) j a =
      ∑ b, Polynomial.C (ofRealF (Jcl a j b)) *
        (Polynomial.C (ofRealF (Xa b)) * Polynomial.X + Polynomial.C (Yv b)) := by
  simp only [factorS, frameX, frameY, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.comp_apply, smul_eq_mul, mulVec, dotProduct, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [map_mul]
  ring

/-- THE KEY IDENTITY `J_{sX+Y} = (sM_X + M_Y)(sM_X + M_Y)ᵀ` over `𝔽[s]`. -/
lemma key (R : CurvTensor 16) (hR : ∀ x, R.jacobi x = ∑ c, (1 : ℝ) • jfam (Jcl c) x) (Xa : Vec 16)
    (f : Fin 15 → Vec 16) :
    jacAlg R 0 (Polynomial.C.comp ofRealF) (pointS Xa f) =
      factorS (frameX Xa) (frameY (pointY f)) *
        (diagonal fun _ : Fin 8 => (1 : ℝ)).map (Polynomial.C.comp ofRealF) *
          (factorS (frameX Xa) (frameY (pointY f)))ᵀ := by
  rw [diagonal_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine Matrix.ext fun j k => ?_
  rw [← eval_jacQ (Polynomial.C.comp ofRealF) (pointS Xa f) R j k, jacQ_eq R hR, eval_cliffQ, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [transpose_apply, factorS_apply, factorS_apply]
  rfl

/-! ### The spectrum -/

lemma mult (R : CurvTensor 16) (hR : ∀ x, R.jacobi x = ∑ c, (1 : ℝ) • jfam (Jcl c) x) (x : Vec 16)
    (hx : x ⬝ᵥ x = 1) (ℓ : ℝ) : R.redMult x ℓ = (if ℓ = 1 then 8 else 0) + (if ℓ = 0 then 7 else 0) := by
  rw [Rem72d.clifford_multiplicity R Jcl S8Example.jcl_clifford.1 0 (fun _ => 1)
    (fun x => by rw [hR, zero_smul, zero_add]) x hx ℓ]
  by_cases h1 : ℓ = 1
  · subst h1
    simp
  · have h1' : (1 : ℝ) ≠ ℓ := fun h => h1 h.symm
    simp [h1, h1']

lemma osserman (R : CurvTensor 16) (hR : ∀ x, R.jacobi x = ∑ c, (1 : ℝ) • jfam (Jcl c) x) : R.IsOsserman := by
  intro x y hx hy ℓ
  rw [mult R hR x hx, mult R hR y hy]

lemma extreme (R : CurvTensor 16) (hR : ∀ x, R.jacobi x = ∑ c, (1 : ℝ) • jfam (Jcl c) x) :
    IsExtremeSevenEight R 0 := by
  refine ⟨⟨7, Or.inl rfl, fun x hx => by rw [mult R hR x hx]; norm_num⟩, Or.inl fun x hx ℓ hpos => ?_⟩
  rw [mult R hR x hx] at hpos
  by_contra hneg
  have h1 : ℓ ≠ 1 := by intro h; rw [h] at hneg; norm_num at hneg
  have h0 : ℓ ≠ 0 := by intro h; rw [h] at hneg; norm_num at hneg
  simp [h1, h0] at hpos

/-! ### The partner -/

lemma partner (R : CurvTensor 16) (hR : ∀ x, R.jacobi x = ∑ c, (1 : ℝ) • jfam (Jcl c) x) :
    IsRationalPartner R 0 (diagonal fun _ : Fin 8 => (1 : ℝ)) (Pi.single 0 1) (fun i => Pi.single i.succ 1)
      (frameX (Pi.single 0 1)) (frameY (pointY fun i => Pi.single i.succ 1)) := by
  refine ⟨?_, fun i => ?_, fun i j => ?_, ?_, ?_, key R hR _ _⟩
  · simp
  · simp [Fin.succ_ne_zero]
  · by_cases h : i = j
    · subst h
      simp
    · simp [h, Fin.succ_inj]
  · ext a b
    have hd : ((frameX (Pi.single 0 1))ᵀ * frameX (Pi.single 0 1)) a b =
        (Jcl a *ᵥ (Pi.single 0 1 : Vec 16)) ⬝ᵥ (Jcl b *ᵥ (Pi.single 0 1 : Vec 16)) := rfl
    rw [hd, frame_dot, Matrix.one_apply]
    simp
  · rw [zero_smul, sub_zero, hR, diagonal_one, Matrix.mul_one]
    ext j k
    simp [Matrix.sum_apply, jfam, vecMulVec_apply, Matrix.mul_apply, frameX]

/-! ### The row -/

theorem thm_G_partner_nonvacuous_proved :
    ∃ (R : CurvTensor 16) (μ0 : ℝ) (ν : ℕ) (μ : Fin ν → ℝ) (Xa : Vec 16) (f : Fin 15 → Vec 16)
      (MX : Matrix (Fin 16) (Fin ν) ℝ) (MY : Matrix (Fin 16) (Fin ν) RatF15),
      R.IsOsserman ∧ IsExtremeSevenEight R μ0 ∧ (∀ i, μ i ≠ 0) ∧
        IsRationalPartner R μ0 (diagonal μ) Xa f MX MY := by
  obtain ⟨R, hR⟩ := S8Example.exists_sum_RJ Jcl Jcl_skew (fun _ => (1 : ℝ))
  exact ⟨R, 0, 8, fun _ => 1, Pi.single 0 1, fun i => Pi.single i.succ 1, frameX (Pi.single 0 1),
    frameY (pointY fun i => Pi.single i.succ 1), osserman R hR, extreme R hR, fun _ => one_ne_zero, partner R hR⟩

end Osserman.Proofs.Six4w

