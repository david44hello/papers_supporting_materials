/-
S8TCFields.lean — extraction and transport of linear eigenfields, paper 013, Section8.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Proofs.S8TCAlgebra
import Osserman.Proofs.ThmEFrames
import Osserman.Proofs.Poly
import Osserman.Proofs.S8Tools

namespace Osserman.Proofs.S8TC

open Osserman Matrix MvPolynomial Osserman.Proofs.Poly Osserman.Proofs.ThmEFrames

lemma homogeneous_q_division (p : MvPolynomial (Fin 16) ℝ) (hp : p.IsHomogeneous 3) (hq : sqP 16 ∣ p) :
    ∃ L : MvPolynomial (Fin 16) ℝ, L.IsHomogeneous 1 ∧ p = sqP 16 * L := by
  obtain ⟨z, hz⟩ := hq
  let := MvPolynomial.gradedAlgebra (σ := Fin 16) (R := ℝ)
  have component := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule (Fin 16) ℝ) (i := 2) (j := 1) (a := sqP 16) (b := z)
    (Osserman.Proofs.Poly.sqP_isHomogeneous (N := 16))
  rw [← hz, DirectSum.decompose_of_mem_same (homogeneousSubmodule (Fin 16) ℝ) hp] at component
  exact ⟨(DirectSum.decompose (homogeneousSubmodule (Fin 16) ℝ) z) 1,
    ((DirectSum.decompose (homogeneousSubmodule (Fin 16) ℝ) z) 1).property, component⟩

lemma q_division_linear (P : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (hP3 : ∀ a, (P a).IsHomogeneous 3) (hq : ∀ a, sqP 16 ∣ P a)
    (hperp : ∀ x : Vec 16, evalField P x ⬝ᵥ x = 0)
    (hnorm : ∀ x : Vec 16, evalField P x ⬝ᵥ evalField P x = (x ⬝ᵥ x) ^ 3) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      ∀ x : Vec 16, evalField P x = (x ⬝ᵥ x) • (J *ᵥ x) := by
  choose L hL equal using fun a => homogeneous_q_division (P a) (hP3 a) (hq a)
  obtain ⟨J, hJ⟩ := thm_E_linear_fields_proved L 1 (by decide) (by omega) hL
  have decomposition (x : Vec 16) : evalField P x = (x ⬝ᵥ x) • (J *ᵥ x) := by
    rw [← hJ]
    ext a
    change eval x (P a) = (x ⬝ᵥ x) * eval x (L a)
    rw [equal, map_mul, eval_sqP]
  have unit (x : Vec 16) (hx : x ⬝ᵥ x = 1) : evalField P x = J *ᵥ x := by
    rw [decomposition, hx, one_smul]
  have norm_unit (x : Vec 16) (hx : x ⬝ᵥ x = 1) : (J *ᵥ x) ⬝ᵥ (J *ᵥ x) = 1 := by
    simpa only [unit x hx, hx, one_pow] using hnorm x
  have perpendicular_unit (x : Vec 16) (hx : x ⬝ᵥ x = 1) : x ⬝ᵥ (J *ᵥ x) = 0 := by
    rw [dotProduct_comm, ← unit x hx]
    exact hperp x
  obtain ⟨clifford, orthogonal⟩ := thm_E_frame_clifford_proved (fun _ : Fin 1 => J)
    (fun x hx a b => by simpa only [Subsingleton.elim a b, ite_true] using norm_unit x hx)
    (fun x hx _ => perpendicular_unit x hx)
  exact ⟨J, clifford.1 0, orthogonal 0, decomposition⟩

lemma inverse_weight (wt : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (i : Fin 3) (hne : Real.sqrt |wt i| ≠ 0) (a : Fin 16) :
    piO (P i a) = piO (C ((Real.sqrt |wt i|)⁻¹)) * tcImg wt P i a := by
  unfold tcImg
  rw [← map_mul]
  congr 1
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]

theorem s8_tc_zero_column_proved (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (i : Fin 3) (hi : tcImg wt P i = 0) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      (∀ x : Vec 16, evalField (P i) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ i) (linP J) := by
  have weight := (s8_tc_rankone_proved R μ P wt h).1 i
  have divides (a : Fin 16) : sqP 16 ∣ P i a := by
    have zero : piO (P i a) = 0 := by rw [inverse_weight wt P i weight a, hi]; simp
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp zero)
  have tangent (x : Vec 16) : evalField (P i) x ⬝ᵥ x = 0 := by
    rw [dotProduct_comm]
    exact (h.2.1 i x).2
  obtain ⟨J, hJs, hJo, hJ⟩ := q_division_linear (P i) (h.1 i) divides tangent (fun x => h.2.2.2.1 x i)
  exact ⟨J, hJs, hJo, hJ, S8Tools.eigenfield_linP (h.2.1 i) J hJ⟩

theorem s8_tc_nonunit_of_lem_8_2
    (hLemma : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (_hP3 : ∀ j, (P j).IsHomogeneous 3)
      (_hP : CubicIdentities P) (_hdiv : ∃ d : Ocal, ¬ IsUnit d ∧ ∀ j, d ∣ piO (P j)),
      ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧ ∀ x : Vec 16,
        evalField P x = (x ⬝ᵥ x) • (J *ᵥ x))
    (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hP2 : CubicIdentities (P 2)) (u3 : Ocal) (v : Fin 16 → Ocal)
    (h2 : tcImg wt P 2 = u3 • v) (hu : ¬ IsUnit u3) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, Jᵀ = -J ∧ Jᵀ * J = 1 ∧
      (∀ x : Vec 16, evalField (P 2) x = (x ⬝ᵥ x) • (J *ᵥ x)) ∧ IsEigenfield R (μ 2) (linP J) := by
  have weight := (s8_tc_rankone_proved R μ P wt h).1 2
  have divides (a : Fin 16) : u3 ∣ piO (P 2 a) := by
    refine ⟨piO (C ((Real.sqrt |wt 2|)⁻¹)) * v a, ?_⟩
    rw [inverse_weight wt P 2 weight a, h2]
    change _ * (u3 * v a) = u3 * (_ * v a)
    ring
  obtain ⟨J, hJs, hJo, hJ⟩ := hLemma (P 2) (h.1 2) hP2 ⟨u3, hu, divides⟩
  exact ⟨J, hJs, hJo, hJ, S8Tools.eigenfield_linP (h.2.1 2) J hJ⟩

theorem s8_tc_same_eigen_proved (R : CurvTensor 16) (μ : Fin 3 → ℝ) (P : Fin 3 → Fin 16 → MvPolynomial (Fin 16) ℝ)
    (wt : Fin 3 → ℝ) (h : ThreeColHyp R μ P wt) (hμ : μ 0 = μ 1) (c1 c2 : ℝ) (J : Matrix (Fin 16) (Fin 16) ℝ)
    (_hc : c1 ^ 2 + c2 ^ 2 = 1)
    (hJ : ∀ x : Vec 16, c1 • evalField (P 0) x + c2 • evalField (P 1) x = (x ⬝ᵥ x) • (J *ᵥ x)) :
    IsEigenfield R (μ 0) (linP J) := by
  let Q : Fin 16 → MvPolynomial (Fin 16) ℝ := fun a => C c1 * P 0 a + C c2 * P 1 a
  have evaluation (x : Vec 16) : evalField Q x = c1 • evalField (P 0) x + c2 • evalField (P 1) x := by
    ext a
    simp [Q, evalField]
  apply S8Tools.eigenfield_linP (R := R) (μ := μ 0) (P := Q) ?_ J (fun x => by rw [evaluation, hJ])
  intro x
  rw [evaluation]
  have first := h.2.1 0 x
  have second := h.2.1 1 x
  rw [← hμ] at second
  exact Submodule.add_mem _ (Submodule.smul_mem _ c1 first) (Submodule.smul_mem _ c2 second)

end Osserman.Proofs.S8TC
