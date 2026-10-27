/-
HibiLi/Example21/FiniteCounts.lean — finite face families and dimension cutoff for X.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.XVertices
import HibiLi.Polytope.FiniteFaces

namespace HibiLi

theorem fNum_eq_zero_of_card_lt {P : Type*} [Fintype P] (Q : Set (P → ℝ))
    {jj : ℕ} (hj : Fintype.card P < jj) : fNum Q jj = 0 := by
  have hempty : faces Q jj = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro F hF
    have hbound : adim F ≤ Fintype.card P := by
      calc
        adim F ≤ Module.finrank ℝ (P → ℝ) := Submodule.finrank_le _
        _ = Fintype.card P := Module.finrank_fintype_fun_eq_card ℝ
    exact (not_le_of_gt hj) (hF.2 ▸ hbound)
  simp [fNum, hempty]

namespace Example21

theorem orderPolytope_X_isPolytope : IsPolytope (orderPolytope XElem) := by
  classical
  refine ⟨(Set.finite_range orderVertex).toFinset, ?_⟩
  simpa only [Set.Finite.coe_toFinset] using orderPolytope_X_eq_convexHull

theorem chainPolytope_X_isPolytope : IsPolytope (chainPolytope XElem) := by
  classical
  refine ⟨(Set.finite_range chainVertex).toFinset, ?_⟩
  simpa only [Set.Finite.coe_toFinset] using chainPolytope_X_eq_convexHull

theorem orderPolytope_X_faces_finite (jj : ℕ) : (faces (orderPolytope XElem) jj).Finite :=
  orderPolytope_X_isPolytope.faces_finite jj

theorem chainPolytope_X_faces_finite (jj : ℕ) : (faces (chainPolytope XElem) jj).Finite :=
  chainPolytope_X_isPolytope.faces_finite jj

theorem orderPolytope_X_fNum_zero {jj : ℕ} (hj : 6 ≤ jj) :
    fNum (orderPolytope XElem) jj = 0 := by
  apply fNum_eq_zero_of_card_lt
  have hcard : Fintype.card XElem = 5 := by decide
  omega

theorem chainPolytope_X_fNum_zero {jj : ℕ} (hj : 6 ≤ jj) :
    fNum (chainPolytope XElem) jj = 0 := by
  apply fNum_eq_zero_of_card_lt
  have hcard : Fintype.card XElem = 5 := by decide
  omega

end Example21
end HibiLi
