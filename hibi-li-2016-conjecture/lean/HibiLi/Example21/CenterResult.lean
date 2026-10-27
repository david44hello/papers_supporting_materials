/-
HibiLi — assembly of Proposition 5.1's central-switch calculation.
-/
import HibiLi.Example21.CenterGeometricCounts
import HibiLi.Example21.CenterGeometry

namespace HibiLi

open Polynomial
open Example21

namespace Example21.CenterResult

abbrev center := CenterSwitch.canonical.toSwitch

theorem carrierS (face : Set (center.P' → ℝ)) (dim : ℕ) :
    center.carrierNum center.cellsS face dim =
      carriedCount CenterRegions.base CenterRegions.familyS (CenterGeometry.canonicalEquiv '' face) dim := by
  have h := carriedCount_image_affineEquiv CenterGeometry.canonicalEquiv center.B center.cellsS face dim
  rw [CenterGeometry.image_B, CenterGeometry.image_cellsS] at h
  exact h.symm

theorem carrierT (face : Set (center.P' → ℝ)) (dim : ℕ) :
    center.carrierNum center.cellsT face dim =
      carriedCount CenterRegions.base CenterRegions.familyT (CenterGeometry.canonicalEquiv '' face) dim := by
  have h := carriedCount_image_affineEquiv CenterGeometry.canonicalEquiv center.B center.cellsT face dim
  rw [CenterGeometry.image_B, CenterGeometry.image_cellsT] at h
  exact h.symm

theorem carrierR (face : Set (center.P' → ℝ)) (dim : ℕ) :
    center.carrierNum center.cellsR face dim =
      carriedCount CenterRegions.base CenterRegions.familyR (CenterGeometry.canonicalEquiv '' face) dim := by
  have h := carriedCount_image_affineEquiv CenterGeometry.canonicalEquiv center.B center.cellsR face dim
  rw [CenterGeometry.image_B, CenterGeometry.image_cellsR] at h
  exact h.symm

theorem proper_delta (face : Set (center.P' → ℝ)) (hface : IsFace center.B face)
    (proper : face ≠ center.B) : center.delta face = 0 := by
  have imageFace := hface.image_affineEquiv CenterGeometry.canonicalEquiv
  rw [CenterGeometry.image_B] at imageFace
  have imageProper : CenterGeometry.canonicalEquiv '' face ≠ CenterRegions.base := by
    intro same
    apply proper
    apply Set.image_injective.mpr CenterGeometry.canonicalEquiv.injective
    rw [CenterGeometry.image_B, same]
  have coefficients (dim : ℕ) : center.deltaCoeff face dim = 0 := by
    have h := CenterRegions.geometric_proper_coeff _ imageFace imageProper dim
    rw [adim_image_affineEquiv] at h
    simpa only [Switch.deltaCoeff, carrierS, carrierT, carrierR] using h
  ext dim
  rw [Proofs.delta_coeff]
  simp [coefficients]

theorem base_counts (dim : ℕ) :
    center.carrierNum center.cellsS center.B dim = (if dim = 4 then 2 else if dim = 3 then 1 else 0) ∧
    center.carrierNum center.cellsT center.B dim = (if dim = 4 then 2 else if dim = 3 then 1 else 0) ∧
    center.carrierNum center.cellsR center.B dim =
      (if dim = 4 then 4 else if dim = 3 then 4 else if dim = 2 then 1 else 0) := by
  rw [carrierS, carrierT, carrierR, CenterGeometry.image_B]
  exact CenterRegions.geometric_base_counts dim

theorem base_delta : center.delta center.B = X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  have card : Fintype.card center.P' = 4 := by rw [Proofs.card_P']; rfl
  have dimension : adim center.B = 4 := by rw [Switch.B, chainOrderPolytope_adim]; exact card
  have hs (dim : ℕ) := (base_counts dim).1
  have ht (dim : ℕ) := (base_counts dim).2.1
  have hr (dim : ℕ) := (base_counts dim).2.2
  simp [Switch.delta, Switch.deltaCoeff, card, dimension, hs, ht, hr, Finset.sum_range_succ]
  ring

def Conclusion (s : Switch XElem) : Prop :=
  (∀ E, IsFace s.B E → E ≠ s.B → s.delta E = 0) ∧
  (∀ k, s.carrierNum s.cellsS s.B k = if k = 4 then 2 else if k = 3 then 1 else 0) ∧
  (∀ k, s.carrierNum s.cellsT s.B k = if k = 4 then 2 else if k = 3 then 1 else 0) ∧
  (∀ k, s.carrierNum s.cellsR s.B k = if k = 4 then 4 else if k = 3 then 4 else if k = 2 then 1 else 0) ∧
  s.delta s.B = X ^ 2 + 2 * X ^ 3 + X ^ 4

theorem canonical_conclusion : Conclusion center :=
  ⟨proper_delta, fun k => (base_counts k).1, fun k => (base_counts k).2.1,
    fun k => (base_counts k).2.2, base_delta⟩

end Example21.CenterResult

theorem prop_5_1_c_switch_proved :
    Nonempty (XSwitch XElem) ∧ ∀ x : XSwitch XElem, x.q = XElem.c ∧ x.E0 = x.toSwitch.B ∧
      (∀ E, IsFace x.toSwitch.B E → E ≠ x.toSwitch.B → x.toSwitch.delta E = 0) ∧
      (∀ k, x.toSwitch.carrierNum x.toSwitch.cellsS x.toSwitch.B k = if k = 4 then 2 else if k = 3 then 1 else 0) ∧
      (∀ k, x.toSwitch.carrierNum x.toSwitch.cellsT x.toSwitch.B k = if k = 4 then 2 else if k = 3 then 1 else 0) ∧
      (∀ k, x.toSwitch.carrierNum x.toSwitch.cellsR x.toSwitch.B k =
        if k = 4 then 4 else if k = 3 then 4 else if k = 2 then 1 else 0) ∧
      x.toSwitch.delta x.toSwitch.B = X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  refine ⟨⟨CenterSwitch.canonical⟩, fun x => ⟨CenterSwitch.q_eq_c x, CenterSwitch.E0_eq_B x, ?_⟩⟩
  change CenterResult.Conclusion x.toSwitch
  rw [CenterSwitch.switch_eq_canonical]
  exact CenterResult.canonical_conclusion

end HibiLi
