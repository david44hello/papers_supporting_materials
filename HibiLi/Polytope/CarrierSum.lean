/-
HibiLiLean — paper Lemma 3.2: sum of local carrier contributions.
-/
import HibiLi.Polytope.CarrierCounts
import HibiLi.Cited.Fourier

namespace HibiLi

open Polynomial

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (switch : Switch P)

theorem fNum_eq_sum_face_indicator (dim : ℕ) :
    (fNum switch.B dim : ℤ) = ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset,
      if dim = adim face then 1 else 0 := by
  classical
  let allFaces := switch.B_isPolytope.finite_faces.toFinset
  have set_eq : faces switch.B dim =
      (allFaces.filter (fun face => dim = adim face) : Set (Set (switch.P' → ℝ))) := by
    ext face
    simp [faces, allFaces, eq_comm]
  rw [fNum, set_eq, Set.ncard_coe_finset, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [allFaces]

theorem sum_deltaCoeff (dim : ℕ) :
    ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset, switch.deltaCoeff face dim =
      (fNum switch.B dim : ℤ) + cellNum switch.cellsR dim -
        cellNum switch.cellsS dim - cellNum switch.cellsT dim := by
  classical
  have countR : (cellNum switch.cellsR dim : ℤ) =
      ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset, (switch.carrierNum switch.cellsR face dim : ℤ) := by
    exact_mod_cast switch.cellNum_eq_sum_carrierNum switch.cellsR switch.cellsR_finite
      (fun _ member => switch.cellsR_properties member) dim
  have countS : (cellNum switch.cellsS dim : ℤ) =
      ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset, (switch.carrierNum switch.cellsS face dim : ℤ) := by
    exact_mod_cast switch.cellNum_eq_sum_carrierNum switch.cellsS switch.cellsS_finite
      (fun _ member => switch.cellsS_properties member) dim
  have countT : (cellNum switch.cellsT dim : ℤ) =
      ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset, (switch.carrierNum switch.cellsT face dim : ℤ) := by
    exact_mod_cast switch.cellNum_eq_sum_carrierNum switch.cellsT switch.cellsT_finite
      (fun _ member => switch.cellsT_properties member) dim
  simp only [deltaCoeff, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← countR, ← countS, ← countT, ← switch.fNum_eq_sum_face_indicator dim]
  ring

theorem sum_delta_eq :
    ∑ face ∈ switch.B_isPolytope.finite_faces.toFinset, switch.delta face =
      facePoly switch.B + cellPoly switch.cellsR - cellPoly switch.cellsS - cellPoly switch.cellsT := by
  classical
  unfold delta facePoly cellPoly facePolyUpTo cellPolyUpTo
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, switch.sum_deltaCoeff]
  simp only [map_add, map_sub, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

end Switch

theorem lemma_3_2_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    {E | IsFace s.B E}.Finite ∧
    facePoly (chainOrderPolytope P (insert s.q s.I)) - facePoly (chainOrderPolytope P s.I) =
      ∑ᶠ (E : Set (s.P' → ℝ)) (_ : IsFace s.B E), s.delta E := by
  refine ⟨s.B_isPolytope.finite_faces, ?_⟩
  rw [Cited.fourier_lemma_4_1]
  exact s.sum_delta_eq.symm.trans
    (finsum_mem_eq_finite_toFinset_sum _ s.B_isPolytope.finite_faces).symm

end HibiLi
