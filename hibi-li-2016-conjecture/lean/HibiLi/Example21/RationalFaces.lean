/-
HibiLi — rational halfspaces enumerate faces through their vertex supports.
-/
import HibiLi.Example21.ActiveFaces

namespace HibiLi.Example21

variable {rows κ : Type*} [Fintype rows] [Fintype κ] [DecidableEq κ]

def tightSupport (points : Fin 8 → rows → ℚ) (parent : Finset (Fin 8))
    (normal : κ → rows → ℚ) (bound : κ → ℚ) (active : Finset κ) : Finset (Fin 8) :=
  parent.filter fun idx => ∀ index ∈ active, rationalScore points (normal index) idx = bound index

def faceSupports (points : Fin 8 → rows → ℚ) (parent : Finset (Fin 8))
    (normal : κ → rows → ℚ) (bound : κ → ℚ) : Finset (Finset (Fin 8)) :=
  ((Finset.univ.powerset).image (tightSupport points parent normal bound)).erase ∅

def supportHull (points : Fin 8 → rows → ℚ) (support : Finset (Fin 8)) : Set (rows → ℝ) :=
  convexHull ℝ (realPoints points '' (support : Set (Fin 8)))

theorem tightRegion_eq_supportHull (points : Fin 8 → rows → ℚ) (parent : Finset (Fin 8))
    (normal : κ → rows → ℚ) (bound : κ → ℚ) (active : Finset κ)
    (bounded : ∀ point ∈ supportHull points parent, ∀ index,
      normalFunctional (normal index) point ≤ (bound index : ℝ))
    (nonempty : (tightRegion (supportHull points parent) (fun index => normalFunctional (normal index))
      (fun index => (bound index : ℝ)) active).Nonempty) :
    tightRegion (supportHull points parent) (fun index => normalFunctional (normal index))
      (fun index => (bound index : ℝ)) active =
      supportHull points (tightSupport points parent normal bound active) := by
  have face := tightRegion_isFace _ _ _ bounded active nonempty
  rw [face.eq_convexHull_inter (parent.finite_toSet.image (realPoints points))]
  congr 1
  ext point
  constructor
  · rintro ⟨⟨idx, hi, rfl⟩, _, equal⟩
    refine ⟨idx, Finset.mem_filter.mpr ⟨hi, fun index hc => ?_⟩, rfl⟩
    have h := equal index hc
    rw [normalFunctional_apply] at h
    dsimp only at h
    exact_mod_cast h
  · rintro ⟨idx, hi, rfl⟩
    obtain ⟨hip, hit⟩ := Finset.mem_filter.mp hi
    refine ⟨⟨idx, hip, rfl⟩, subset_convexHull ℝ _ ⟨idx, hip, rfl⟩, fun index hc => ?_⟩
    rw [normalFunctional_apply, hit index hc]

theorem supportHull_isFace_of_mem (points : Fin 8 → rows → ℚ) (parent : Finset (Fin 8))
    (normal : κ → rows → ℚ) (bound : κ → ℚ)
    (bounded : ∀ point ∈ supportHull points parent, ∀ index,
      normalFunctional (normal index) point ≤ (bound index : ℝ))
    {support : Finset (Fin 8)} (member : support ∈ faceSupports points parent normal bound) :
    IsFace (supportHull points parent) (supportHull points support) := by
  obtain ⟨notempty, member⟩ := Finset.mem_erase.mp member
  obtain ⟨active, _, rfl⟩ := Finset.mem_image.mp member
  have hn : (tightSupport points parent normal bound active).Nonempty := Finset.nonempty_iff_ne_empty.mpr notempty
  obtain ⟨idx, hi⟩ := hn
  obtain ⟨hip, hit⟩ := Finset.mem_filter.mp hi
  have nonempty : (tightRegion (supportHull points parent) (fun index => normalFunctional (normal index))
      (fun index => (bound index : ℝ)) active).Nonempty := by
    refine ⟨realPoints points idx, subset_convexHull ℝ _ ⟨idx, hip, rfl⟩, fun index hc => ?_⟩
    rw [normalFunctional_apply, hit index hc]
  rw [← tightRegion_eq_supportHull points parent normal bound active bounded nonempty]
  exact tightRegion_isFace _ _ _ bounded active nonempty

theorem allFaces_eq_supports (points : Fin 8 → rows → ℚ) (parent : Finset (Fin 8))
    (normal : κ → rows → ℚ) (bound : κ → ℚ)
    (representation : supportHull points parent =
      {point | ∀ index, normalFunctional (normal index) point ≤ (bound index : ℝ)}) :
    {F | IsFace (supportHull points parent) F} =
      supportHull points '' (faceSupports points parent normal bound : Set (Finset (Fin 8))) := by
  have bounded : ∀ point ∈ supportHull points parent, ∀ index,
      normalFunctional (normal index) point ≤ (bound index : ℝ) := by
    intro point hp
    rw [representation] at hp
    exact hp
  ext face
  constructor
  · intro hface
    obtain ⟨active, equal⟩ := IsFace.exists_active_constraints _ _ representation (convex_convexHull ℝ _) hface
    have nonempty := equal ▸ hface.1
    have same := tightRegion_eq_supportHull points parent normal bound active bounded nonempty
    refine ⟨tightSupport points parent normal bound active, ?_, (equal.trans same).symm⟩
    apply Finset.mem_erase.mpr
    constructor
    · have hn : (supportHull points (tightSupport points parent normal bound active)).Nonempty := same ▸ nonempty
      have image_nonempty := convexHull_nonempty_iff.mp hn
      obtain ⟨_, ⟨idx, hi, _⟩⟩ := image_nonempty
      exact Finset.nonempty_iff_ne_empty.mp ⟨idx, hi⟩
    · exact Finset.mem_image.mpr ⟨active, Finset.mem_powerset.mpr (Finset.subset_univ _), rfl⟩
  · rintro ⟨support, member, rfl⟩
    exact supportHull_isFace_of_mem points parent normal bound bounded member

end HibiLi.Example21
