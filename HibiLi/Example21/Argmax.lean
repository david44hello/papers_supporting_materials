/-
HibiLi/Example21/Argmax.lean — exposed faces through finite generator maximizers.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.FiniteHull

namespace HibiLi

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

def generatorArgmax (V : Set E) (ell : E →L[ℝ] ℝ) : Set E :=
  {x ∈ V | ∀ y ∈ V, ell y ≤ ell x}

theorem linear_le_on_convexHull (V : Set E) (ell : E →L[ℝ] ℝ) (bound : ℝ)
    (hV : ∀ x ∈ V, ell x ≤ bound) : ∀ x ∈ convexHull ℝ V, ell x ≤ bound := by
  exact convexHull_min hV ((convex_Iic bound).linear_preimage ell.toLinearMap)

theorem inter_toExposed_convexHull (V : Set E) (ell : E →L[ℝ] ℝ) :
    V ∩ ell.toExposed (convexHull ℝ V) = generatorArgmax V ell := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, fun y hy => hx.2.2 y (subset_convexHull ℝ V hy)⟩
  · intro hx
    exact ⟨hx.1, subset_convexHull ℝ V hx.1,
      linear_le_on_convexHull V ell (ell x) hx.2⟩

variable [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

omit [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] in
theorem generatorArgmax_nonempty {V : Set E} (hV : V.Finite) (hVN : V.Nonempty)
    (ell : E →L[ℝ] ℝ) : (generatorArgmax V ell).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := hV.isCompact.exists_isMaxOn hVN ell.continuous.continuousOn
  exact ⟨x, hx, hmax⟩

theorem toExposed_convexHull_eq {V : Set E} (hV : V.Finite) (hVN : V.Nonempty)
    (ell : E →L[ℝ] ℝ) :
    ell.toExposed (convexHull ℝ V) = convexHull ℝ (generatorArgmax V ell) := by
  obtain ⟨x, hx⟩ := generatorArgmax_nonempty hV hVN ell
  have hx' : x ∈ V ∩ ell.toExposed (convexHull ℝ V) :=
    (Set.ext_iff.mp (inter_toExposed_convexHull V ell) x).mpr hx
  have hface : IsFace (convexHull ℝ V) (ell.toExposed (convexHull ℝ V)) :=
    ⟨⟨x, hx'.2⟩, ContinuousLinearMap.toExposed.isExposed⟩
  rw [hface.eq_convexHull_inter hV, inter_toExposed_convexHull]

theorem isFace_convexHull_generatorArgmax {V : Set E} (hV : V.Finite)
    (hVN : V.Nonempty) (ell : E →L[ℝ] ℝ) :
    IsFace (convexHull ℝ V) (convexHull ℝ (generatorArgmax V ell)) := by
  refine ⟨convexHull_nonempty_iff.mpr (generatorArgmax_nonempty hV hVN ell), ?_⟩
  rw [← toExposed_convexHull_eq hV hVN ell]
  exact ContinuousLinearMap.toExposed.isExposed

theorem IsFace.exists_generatorArgmax {V F : Set E} (hV : V.Finite)
    (hF : IsFace (convexHull ℝ V) F) :
    ∃ ell : E →L[ℝ] ℝ, F = convexHull ℝ (generatorArgmax V ell) := by
  obtain ⟨ell, hell⟩ := hF.2 hF.1
  have hVN : V.Nonempty := convexHull_nonempty_iff.mp (hF.1.mono hF.2.subset)
  refine ⟨ell, ?_⟩
  calc
    F = ell.toExposed (convexHull ℝ V) := hell
    _ = convexHull ℝ (generatorArgmax V ell) := toExposed_convexHull_eq hV hVN ell

end HibiLi
