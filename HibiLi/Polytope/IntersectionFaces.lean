/-
HibiLiLean — faces of an intersection arise by intersecting faces of the factors.
-/
import HibiLi.Polytope.CellHalfspaces

open Set Filter
open scoped Topology

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem eventually_lineMap_mem_of_intrinsicInterior {body : Set E} {point other : E}
    (interior : point ∈ intrinsicInterior ℝ body) (member : other ∈ body) :
    ∀ᶠ scalar : ℝ in 𝓝 0, AffineMap.lineMap point other scalar ∈ body := by
  obtain ⟨intrinsicPoint, open_member, rfl⟩ := mem_intrinsicInterior.mp interior
  let : Nonempty (affineSpan ℝ body) := ⟨intrinsicPoint⟩
  let otherPoint : affineSpan ℝ body := ⟨other, subset_affineSpan ℝ body member⟩
  have curve_cont : Continuous (fun scalar : ℝ => AffineMap.lineMap intrinsicPoint otherPoint scalar) := by
    fun_prop
  have tend := curve_cont.tendsto 0
  simp only [AffineMap.lineMap_apply_zero] at tend
  have nearby := tend.eventually (mem_interior_iff_mem_nhds.mp open_member)
  simpa [AffineMap.lineMap_apply, otherPoint] using nearby

theorem linear_eq_of_intrinsicInterior_inter_max {left right : Set E} {point : E}
    (left_interior : point ∈ intrinsicInterior ℝ left)
    (right_interior : point ∈ intrinsicInterior ℝ right)
    (functional : StrongDual ℝ E)
    (bounded : ∀ other ∈ left ∩ right, functional other ≤ functional point) :
    ∀ other ∈ left ∩ right, functional other = functional point := by
  intro other member
  have nearby : ∀ᶠ scalar : ℝ in 𝓝 0, AffineMap.lineMap point other scalar ∈ left ∩ right :=
    (eventually_lineMap_mem_of_intrinsicInterior left_interior member.1).and
      (eventually_lineMap_mem_of_intrinsicInterior right_interior member.2)
  obtain ⟨radius, positive, in_ball⟩ := Metric.eventually_nhds_iff.mp nearby
  have negative : -(radius / 2) < 0 := by linarith
  have curve_member := in_ball (y := -(radius / 2)) (by
    rw [Real.dist_eq, sub_zero, abs_of_neg negative]
    linarith)
  have lower := bounded _ curve_member
  have upper := bounded other member
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    map_add, map_smul, map_sub, smul_eq_mul] at lower
  nlinarith

theorem IsFace.inter_decomposition {left right face : Set E}
    (leftPoly : IsPolytope left) (rightPoly : IsPolytope right)
    (leftRep : HasFiniteHalfspaceRep left) (rightRep : HasFiniteHalfspaceRep right)
    (hface : IsFace (left ∩ right) face) :
    ∃ leftFace rightFace, IsFace left leftFace ∧ IsFace right rightFace ∧ face = leftFace ∩ rightFace := by
  obtain ⟨leftFace, leftCarrier, _⟩ := leftPoly.existsUnique_carrier hface.1
    (hface.subset.trans Set.inter_subset_left)
  obtain ⟨rightFace, rightCarrier, _⟩ := rightPoly.existsUnique_carrier hface.1
    (hface.subset.trans Set.inter_subset_right)
  have convex := hface.2.convex (leftPoly.convex.inter rightPoly.convex)
  obtain ⟨point, interior⟩ := hface.1.intrinsicInterior convex
  have left_interior := leftCarrier.intrinsicInterior_subset leftRep interior
  have right_interior := rightCarrier.intrinsicInterior_subset rightRep interior
  have point_face : point ∈ face := _root_.intrinsicInterior_subset interior
  obtain ⟨functional, representation⟩ := hface.2 hface.1
  have maximal := point_face
  rw [representation] at maximal
  have bound : ∀ other ∈ leftFace ∩ rightFace, functional other ≤ functional point :=
    fun other member => maximal.2 other ⟨leftCarrier.1.subset member.1, rightCarrier.1.subset member.2⟩
  have flat := linear_eq_of_intrinsicInterior_inter_max left_interior right_interior functional bound
  refine ⟨leftFace, rightFace, leftCarrier.1, rightCarrier.1, Set.Subset.antisymm ?_ ?_⟩
  · exact fun _ member => ⟨leftCarrier.2.1 member, rightCarrier.2.1 member⟩
  · intro other member
    rw [representation]
    exact ⟨⟨leftCarrier.1.subset member.1, rightCarrier.1.subset member.2⟩,
      fun third inBody => (maximal.2 third inBody).trans_eq (flat other member).symm⟩

end HibiLi
