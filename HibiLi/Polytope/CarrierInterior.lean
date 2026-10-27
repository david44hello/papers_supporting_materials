/-
HibiLiLean — intrinsic interiors and minimal carriers.
-/
import HibiLi.Polytope.SwitchDomains

open Set Filter
open scoped Topology

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem linear_eq_on_affineSpan {body : Set E} (functional : StrongDual ℝ E) (level : ℝ)
    (flat : ∀ point ∈ body, functional point = level) :
    ∀ point ∈ affineSpan ℝ body, functional point = level := by
  exact AffineMap.eqOn_affineSpan (f := functional.toLinearMap.toAffineMap)
    (g := AffineMap.const ℝ E level) flat

omit [FiniteDimensional ℝ E] in
theorem linear_eq_of_intrinsicInterior_max {body : Set E} {point : E}
    (interior : point ∈ intrinsicInterior ℝ body) (functional : StrongDual ℝ E)
    (bounded : ∀ other ∈ body, functional other ≤ functional point) :
    ∀ other ∈ body, functional other = functional point := by
  obtain ⟨intrinsicPoint, open_member, rfl⟩ := mem_intrinsicInterior.mp interior
  let : Nonempty (affineSpan ℝ body) := ⟨intrinsicPoint⟩
  intro other member
  let otherPoint : affineSpan ℝ body := ⟨other, subset_affineSpan ℝ body member⟩
  have curve_cont : Continuous (fun scalar : ℝ => AffineMap.lineMap intrinsicPoint otherPoint scalar) := by
    fun_prop
  have nearby : ∀ᶠ scalar : ℝ in 𝓝 0,
      ((AffineMap.lineMap intrinsicPoint otherPoint scalar : affineSpan ℝ body) : E) ∈ body := by
    have tend := curve_cont.tendsto 0
    simp only [AffineMap.lineMap_apply_zero] at tend
    exact tend.eventually (mem_interior_iff_mem_nhds.mp open_member)
  obtain ⟨radius, positive, in_ball⟩ := Metric.eventually_nhds_iff.mp nearby
  have negative : -(radius / 2) < 0 := by linarith
  have curve_member := in_ball (y := -(radius / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_of_neg negative]
    linarith)
  have bound := bounded _ curve_member
  have evaluated : functional
      (((AffineMap.lineMap intrinsicPoint otherPoint (-(radius / 2))) : affineSpan ℝ body) : E) =
      (-(radius / 2)) * (functional other - functional intrinsicPoint) + functional intrinsicPoint := by
    simp [AffineMap.lineMap_apply, otherPoint, map_add, map_smul, map_sub]
  rw [evaluated] at bound
  have upper := bounded other member
  nlinarith

theorem IsFace.eq_inter_affineSpan {body face : Set E} (hface : IsFace body face) :
    face = body ∩ (affineSpan ℝ face : Set E) := by
  obtain ⟨base, base_member⟩ := hface.1
  obtain ⟨functional, representation⟩ := hface.2 hface.1
  have maximal : ∀ point ∈ body, functional point ≤ functional base := by
    have member := base_member
    rw [representation] at member
    exact member.2
  have flat : ∀ point ∈ face, functional point = functional base := by
    intro point member
    rw [representation] at member
    exact le_antisymm (maximal point member.1) (member.2 base (hface.subset base_member))
  apply Set.Subset.antisymm
  · exact fun point member => ⟨hface.subset member, subset_affineSpan ℝ face member⟩
  · intro point member
    rw [representation]
    exact ⟨member.1, fun other inBody => (maximal other inBody).trans_eq
      (linear_eq_on_affineSpan functional (functional base) flat point member.2).symm⟩

theorem IsCarrier.intrinsicInterior_subset {body face cell : Set E}
    (carrier : IsCarrier body face cell) (represented : HasFiniteHalfspaceRep body) :
    intrinsicInterior ℝ cell ⊆ intrinsicInterior ℝ face := by
  classical
  obtain ⟨constraints, body_eq⟩ := represented
  intro point interior
  have cell_member : point ∈ cell := _root_.intrinsicInterior_subset interior
  have face_member : point ∈ face := carrier.2.1 cell_member
  let intrinsicPoint : affineSpan ℝ face := ⟨point, subset_affineSpan ℝ face face_member⟩
  have bounded (constraint : constraints) (other : E) (member : other ∈ body) :
      constraint.1.1 other ≤ constraint.1.2 := by
    rw [body_eq] at member
    exact member constraint.1 constraint.2
  have nearby : ∀ᶠ other : affineSpan ℝ face in 𝓝 intrinsicPoint,
      ∀ constraint : constraints, constraint.1.1 other ≤ constraint.1.2 := by
    rw [Filter.eventually_all]
    intro constraint
    by_cases active : constraint.1.1 point = constraint.1.2
    · have flat_cell : ∀ other ∈ cell, constraint.1.1 other = constraint.1.2 := by
        intro other member
        exact (linear_eq_of_intrinsicInterior_max interior constraint.1.1
          (fun other member => (bounded constraint other (carrier.1.subset (carrier.2.1 member))).trans_eq active.symm)
          other member).trans active
      let supporting : Set E := {other ∈ body | constraint.1.1 other = constraint.1.2}
      have supporting_face : IsFace body supporting := by
        refine ⟨⟨point, carrier.1.subset face_member, active⟩, fun _ => ⟨constraint.1.1, ?_⟩⟩
        ext other
        constructor
        · rintro ⟨member, equality⟩
          exact ⟨member, fun third inBody => (bounded constraint third inBody).trans_eq equality.symm⟩
        · rintro ⟨member, maximal⟩
          exact ⟨member, le_antisymm (bounded constraint other member)
            (active ▸ maximal point (carrier.1.subset face_member))⟩
      have cell_inside : cell ⊆ supporting := fun other member =>
        ⟨carrier.1.subset (carrier.2.1 member), flat_cell other member⟩
      have face_inside := carrier.2.2 supporting supporting_face cell_inside
      have flat_face : ∀ other ∈ face, constraint.1.1 other = constraint.1.2 :=
        fun other member => (face_inside member).2
      exact Filter.Eventually.of_forall fun other =>
        (linear_eq_on_affineSpan constraint.1.1 constraint.1.2 flat_face other other.2).le
    · have strict : constraint.1.1 point < constraint.1.2 :=
        lt_of_le_of_ne (bounded constraint point (carrier.1.subset face_member)) active
      have continuous : Continuous (fun other : affineSpan ℝ face => constraint.1.1 (other : E)) := by
        fun_prop
      have tend : Tendsto (fun other : affineSpan ℝ face => constraint.1.1 (other : E))
          (𝓝 intrinsicPoint) (𝓝 (constraint.1.1 point)) := continuous.continuousAt
      exact (tend.eventually_lt_const strict).mono fun _ bound => bound.le
  refine mem_intrinsicInterior.mpr ⟨intrinsicPoint, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  filter_upwards [nearby] with other satisfies
  change (other : E) ∈ face
  apply (Set.ext_iff.mp carrier.1.eq_inter_affineSpan (other : E)).mpr
  refine ⟨?_, other.2⟩
  rw [body_eq]
  exact fun constraint member => satisfies ⟨constraint, member⟩

theorem sec3_carrier_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (C : Set (s.P' → ℝ)) (hC : C ∈ s.cellsS ∨ C ∈ s.cellsT ∨ C ∈ s.cellsR) :
    (∃! E, IsCarrier s.B E C) ∧
      ∀ E, IsCarrier s.B E C → intrinsicInterior ℝ C ⊆ intrinsicInterior ℝ E := by
  have properties : C.Nonempty ∧ C ⊆ s.B := by
    rcases hC with ⟨branch, _, _, hface⟩ | ⟨branch, _, _, hface⟩ | ⟨nonempty, left, hleft, right, _, rfl⟩
    · exact ⟨hface.1, fun _ member => (hface.subset member).1⟩
    · exact ⟨hface.1, fun _ member => (hface.subset member).1⟩
    · rcases hleft with ⟨branch, _, _, hface⟩
      exact ⟨nonempty, fun _ member => (hface.subset member.1).1⟩
  refine ⟨s.B_isPolytope.existsUnique_carrier properties.1 properties.2, ?_⟩
  exact fun _ carrier => carrier.intrinsicInterior_subset (chainOrderPolytope_halfspaces _ _)

end HibiLi
