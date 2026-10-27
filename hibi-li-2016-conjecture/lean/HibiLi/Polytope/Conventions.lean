/-
HibiLiLean — row/column and increasing/decreasing order conventions.
-/
import HibiLi.Polytope.Affine

namespace HibiLi

theorem sec2_HL_unimod_convention_proved {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q Q' : Set (ι → ℝ)) : UnimodEquivHL Q Q' ↔ UnimodEquiv Q Q' := by
  constructor
  · rintro ⟨matrix, determinant, shift, image_eq⟩
    refine ⟨matrix.transpose, by simpa using determinant, shift, ?_⟩
    simpa only [Matrix.transpose_map, Matrix.mulVec_transpose] using image_eq
  · rintro ⟨matrix, determinant, shift, image_eq⟩
    refine ⟨matrix.transpose, by simpa using determinant, shift, ?_⟩
    simpa only [Matrix.transpose_map, Matrix.vecMul_transpose] using image_eq

theorem sec2_HL_chain_convention_proved (P : Type*) [Fintype P] [PartialOrder P] :
    chainPolytopeHL P = chainPolytope P := by
  classical
  ext point
  constructor
  · rintro ⟨nonnegative, maximal_bounds⟩
    refine ⟨nonnegative, fun chain ordered => ?_⟩
    obtain ⟨maximal, isMaximal, contains⟩ := ordered.exists_maxChain
    have finite : maximal.Finite := Set.toFinite _
    have chain_subset : chain ⊆ finite.toFinset := by
      intro coord member
      exact finite.mem_toFinset.mpr (contains member)
    have bound := maximal_bounds finite.toFinset (by simpa only [Set.Finite.coe_toFinset] using isMaximal)
    exact (Finset.sum_le_sum_of_subset_of_nonneg chain_subset
      (fun coord _ _ => nonnegative coord)).trans bound
  · rintro ⟨nonnegative, bounds⟩
    exact ⟨nonnegative, fun chain maximal => bounds chain maximal.1⟩

theorem sec2_footnote_HL_convention_proved (P : Type*) [Fintype P] [PartialOrder P] [DecidableEq P] :
    orderPolytopeHL P = (fun point => (fun _ => (1 : ℝ)) - point) '' orderPolytope P ∧
    UnimodEquiv (orderPolytope P) (orderPolytopeHL P) := by
  have image_eq : orderPolytopeHL P =
      (fun point => (fun _ => (1 : ℝ)) - point) '' orderPolytope P := by
    ext point
    constructor
    · rintro ⟨bounds, monotone⟩
      refine ⟨(fun _ => (1 : ℝ)) - point, ⟨?_, ?_⟩, ?_⟩
      · intro coord
        have bound := bounds coord
        change 0 ≤ 1 - point coord ∧ 1 - point coord ≤ 1
        constructor <;> linarith
      · intro lower upper relation
        have bound := monotone lower upper relation
        change 1 - point lower ≤ 1 - point upper
        linarith
      · ext coord
        simp
    · rintro ⟨original, ⟨bounds, monotone⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · intro coord
        have bound := bounds coord
        change 0 ≤ 1 - original coord ∧ 1 - original coord ≤ 1
        constructor <;> linarith
      · intro lower upper relation
        have bound := monotone lower upper relation
        change 1 - original upper ≤ 1 - original lower
        linarith
  refine ⟨image_eq, -(1 : Matrix P P ℤ), ?_, (fun _ => 1), ?_⟩
  · simpa [Matrix.det_neg] using neg_one_pow_eq_or ℤ (Fintype.card P)
  · rw [image_eq]
    congr 1
    funext point
    have mapped : (-(1 : Matrix P P ℤ)).map (Int.cast : ℤ → ℝ) = -(1 : Matrix P P ℝ) := by
      simpa using (Int.castRingHom ℝ).mapMatrix.map_neg (1 : Matrix P P ℤ)
    rw [mapped]
    rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    simp [sub_eq_add_neg, add_comm]

end HibiLi
