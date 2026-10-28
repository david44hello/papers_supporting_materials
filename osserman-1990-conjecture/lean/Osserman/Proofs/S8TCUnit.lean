/-
S8TCUnit.lean — the unit branch of the three-column step, paper 013, Section 8.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.S8TCFields
import Osserman.Proofs.QPrime

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial

lemma homogeneous_ratio_constants (u : Ocal) (f g : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hf : ∀ a, (f a).IsHomogeneous 3) (hg : ∀ a, (g a).IsHomogeneous 3)
    (heq : ∀ a, piO (f a) = u * piO (g a)) :
    ∃ c : ℝ, ∀ a, piO (f a) = piO (C c) * piO (g a) := by
  classical
  let 𝒜 := homogeneousSubmodule (Fin 16) ℝ
  let := MvPolynomial.gradedAlgebra (σ := Fin 16) (R := ℝ)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective u
  change piO r = u at hr
  let r0 : MvPolynomial (Fin 16) ℝ := (DirectSum.decompose 𝒜 r) 0
  have r0hom : r0.IsHomogeneous 0 := ((DirectSum.decompose 𝒜 r) 0).property
  have constant : r0 = C (r0.coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 16)).mpr r0hom)
  have idealHom : (Ideal.span {sqP 16}).IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact ⟨2, Osserman.Proofs.Poly.sqP_isHomogeneous⟩
  refine ⟨r0.coeff 0, fun a => ?_⟩
  have zero : piO (f a - r * g a) = 0 := by
    rw [map_sub, map_mul, hr, heq a, sub_self]
  have member : f a - r * g a ∈ Ideal.span {sqP 16} := Ideal.Quotient.eq_zero_iff_mem.mp zero
  have projected : (DirectSum.decompose 𝒜 (f a - r * g a) 3 : MvPolynomial (Fin 16) ℝ) ∈
      Ideal.span {sqP 16} := (Ideal.IsHomogeneous.mem_iff 𝒜 idealHom).mp member 3
  have componentProduct : (DirectSum.decompose 𝒜 (r * g a) 3 : MvPolynomial (Fin 16) ℝ) = r0 * g a :=
    DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := 0) (j := 3) (hg a)
  rw [DirectSum.decompose_sub, DFinsupp.sub_apply, Submodule.coe_sub,
    DirectSum.decompose_of_mem_same 𝒜 (hf a), componentProduct] at projected
  have equation : piO (f a - r0 * g a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr projected
  rw [map_sub, map_mul, constant] at equation
  exact sub_eq_zero.mp equation

theorem s8_tc_unit_const_proved (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (u0 u1 u3 : Ocal) (v : Fin 16 → Ocal)
    (h0 : tcImg wt P 0 = u0 • v) (h1 : tcImg wt P 1 = u1 • v) (h2 : tcImg wt P 2 = u3 • v) (hu : IsUnit u3) :
    ∃ k0 k1 : ℝ, tcImg wt P 0 = piO (MvPolynomial.C k0) • tcImg wt P 2 ∧
      tcImg wt P 1 = piO (MvPolynomial.C k1) • tcImg wt P 2 := by
  obtain ⟨unit, rfl⟩ := hu
  have relation (i : Fin 3) (u : Ocal) (hi : tcImg wt P i = u • v) :
      ∃ c : ℝ, tcImg wt P i = piO (C c) • tcImg wt P 2 := by
    obtain ⟨c, hc⟩ := homogeneous_ratio_constants (u * (↑(unit⁻¹) : Ocal))
      (fun a => C (Real.sqrt |wt i|) * P i a) (fun a => C (Real.sqrt |wt 2|) * P 2 a)
      (fun a => (h.1 i a).C_mul _) (fun a => (h.1 2 a).C_mul _) (fun a => by
        change tcImg wt P i a = (u * (↑(unit⁻¹) : Ocal)) * tcImg wt P 2 a
        rw [hi, h2]
        simp only [Pi.smul_apply, smul_eq_mul]
        simp [mul_assoc])
    exact ⟨c, funext hc⟩
  obtain ⟨k0, hk0⟩ := relation 0 u0 h0
  obtain ⟨k1, hk1⟩ := relation 1 u1 h1
  exact ⟨k0, k1, hk0, hk1⟩

theorem s8_tc_lincomb_proved (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (k0 k1 : ℝ)
    (h0 : tcImg wt P 0 = piO (MvPolynomial.C k0) • tcImg wt P 2)
    (h1 : tcImg wt P 1 = piO (MvPolynomial.C k1) • tcImg wt P 2) (h2 : tcImg wt P 2 ≠ 0) :
    ∃ (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ), c1 ^ 2 + c2 ^ 2 = 1 ∧ Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  classical
  let := Osserman.Proofs.QPrime.s8_q_prime_proved.2.2
  have weights := (s8_tc_rankone_proved R μ P wt h).1
  have rankone := (s8_tc_rankone_proved R μ P wt h).2
  have pair_nonzero : k0 ≠ 0 ∨ k1 ≠ 0 := by
    by_contra absent
    simp only [not_or, not_not] at absent
    apply h2
    funext a
    have relation := rankone a a
    rw [h0, h1, absent.1, absent.2] at relation
    simp only [map_zero, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add] at relation
    exact mul_self_eq_zero.mp relation.symm
  let a0 := Real.sqrt |wt 0|
  let a1 := Real.sqrt |wt 1|
  have a0ne : a0 ≠ 0 := weights 0
  have a1ne : a1 ≠ 0 := weights 1
  let A := k1 * a0
  let B := -(k0 * a1)
  have positive : 0 < A ^ 2 + B ^ 2 := by
    rcases pair_nonzero with first | second
    · have nz : B ≠ 0 := neg_ne_zero.mpr (mul_ne_zero first a1ne)
      nlinarith [sq_nonneg A, sq_pos_of_ne_zero nz]
    · have nz : A ≠ 0 := mul_ne_zero second a0ne
      nlinarith [sq_nonneg B, sq_pos_of_ne_zero nz]
  let d := Real.sqrt (A ^ 2 + B ^ 2)
  have dne : d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr positive)
  have dsq : d ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt positive.le
  let c1 := A / d
  let c2 := B / d
  have normalized : c1 ^ 2 + c2 ^ 2 = 1 := by
    dsimp only [c1, c2]
    field_simp
    exact dsq.symm
  have cancel : c1 * a0⁻¹ * k0 + c2 * a1⁻¹ * k1 = 0 := by
    dsimp only [c1, c2, A, B]
    field_simp
    ring
  let Q : Fin 16 → MvPolynomial (Fin 16) ℝ := fun a => C c1 * P 0 a + C c2 * P 1 a
  have evaluation (x : Vec 16) : evalField Q x = c1 • evalField (P 0) x + c2 • evalField (P 1) x := by
    ext a
    simp [Q, evalField]
  have qdiv (a : Fin 16) : sqP 16 ∣ Q a := by
    have zero : piO (Q a) = 0 := by
      dsimp only [Q]
      rw [map_add, map_mul, map_mul, inverse_weight wt P 0 (weights 0) a,
        inverse_weight wt P 1 (weights 1) a, h0, h1]
      change piO (C c1) * (piO (C a0⁻¹) * (piO (C k0) * tcImg wt P 2 a)) +
        piO (C c2) * (piO (C a1⁻¹) * (piO (C k1) * tcImg wt P 2 a)) = 0
      calc
        _ = piO (C (c1 * a0⁻¹ * k0 + c2 * a1⁻¹ * k1)) * tcImg wt P 2 a := by
          simp only [map_add, map_mul]
          ring
        _ = 0 := by rw [cancel, map_zero, map_zero, zero_mul]
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp zero)
  have tangent (x : Vec 16) : evalField Q x ⬝ᵥ x = 0 := by
    rw [evaluation, add_dotProduct, smul_dotProduct, smul_dotProduct]
    have p0 : evalField (P 0) x ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact (h.2.1 0 x).2
    have p1 : evalField (P 1) x ⬝ᵥ x = 0 := by rw [dotProduct_comm]; exact (h.2.1 1 x).2
    simp only [p0, p1, smul_zero, add_zero]
  have norm (x : Vec 16) : evalField Q x ⬝ᵥ evalField Q x = (x ⬝ᵥ x) ^ 3 := by
    rw [evaluation]
    have cross := h.2.2.1 x 0 1 (by decide)
    have reverse : evalField (P 1) x ⬝ᵥ evalField (P 0) x = 0 := by rw [dotProduct_comm]; exact cross
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      h.2.2.2.1 x 0, h.2.2.2.1 x 1, cross, reverse]
    linear_combination (x ⬝ᵥ x) ^ 3 * normalized
  obtain ⟨J, skew, orthogonal, image⟩ := q_division_linear Q
    (fun a => ((h.1 0 a).C_mul c1).add ((h.1 1 a).C_mul c2)) qdiv tangent norm
  exact ⟨c1, c2, J, normalized, skew, orthogonal, fun x => by rw [← evaluation, image]⟩

end Osserman.Proofs.S8TC
