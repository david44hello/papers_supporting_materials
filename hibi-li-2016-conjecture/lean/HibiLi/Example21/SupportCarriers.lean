/-
HibiLi — finite supports faithfully represent zero-one hulls and their carriers.
-/
import HibiLi.Example21.RationalFaces
import HibiLi.Example21.ZeroOneFaces

namespace HibiLi.Example21

variable {rows : Type*} [Fintype rows]

theorem supportHull_coordinate_bounds (points : Fin 8 → rows → ℚ)
    (zeroOne : ∀ idx, realPoints points idx ∈ zeroOneVectors rows) (support : Finset (Fin 8))
    {point : rows → ℝ} (member : point ∈ supportHull points support) (row : rows) :
    0 ≤ point row ∧ point row ≤ 1 := by
  have subset : realPoints points '' (support : Set (Fin 8)) ⊆
      {point : rows → ℝ | point row ∈ Set.Icc (0 : ℝ) 1} := by
    rintro _ ⟨idx, _, rfl⟩
    change realPoints points idx row ∈ Set.Icc (0 : ℝ) 1
    rcases zeroOne idx row with h | h <;> rw [h] <;> norm_num
  have convex : Convex ℝ {point : rows → ℝ | point row ∈ Set.Icc (0 : ℝ) 1} :=
    (convex_Icc (0 : ℝ) 1).linear_preimage
      (ContinuousLinearMap.proj row : (rows → ℝ) →L[ℝ] ℝ).toLinearMap
  exact convexHull_min subset convex member

theorem realPoint_mem_supportHull_iff (points : Fin 8 → rows → ℚ)
    (zeroOne : ∀ idx, realPoints points idx ∈ zeroOneVectors rows)
    (injective : Function.Injective (realPoints points)) (support : Finset (Fin 8)) (idx : Fin 8) :
    realPoints points idx ∈ supportHull points support ↔ idx ∈ support := by
  constructor
  · intro member
    have face := zeroOne_isFace_singleton
      (fun _ hm => supportHull_coordinate_bounds points zeroOne support hm) member (zeroOne idx)
    have extreme := isExtreme_singleton.mp face.2.isExtreme
    obtain ⟨other, ho, same⟩ := extremePoints_convexHull_subset extreme
    have equal := injective same
    exact equal ▸ ho
  · exact fun hi => subset_convexHull ℝ _ ⟨idx, hi, rfl⟩

theorem supportHull_subset_iff (points : Fin 8 → rows → ℚ)
    (zeroOne : ∀ idx, realPoints points idx ∈ zeroOneVectors rows)
    (injective : Function.Injective (realPoints points)) (left right : Finset (Fin 8)) :
    supportHull points left ⊆ supportHull points right ↔ left ⊆ right := by
  constructor
  · intro subset idx hi
    exact (realPoint_mem_supportHull_iff points zeroOne injective right idx).mp
      (subset ((realPoint_mem_supportHull_iff points zeroOne injective left idx).mpr hi))
  · intro subset
    exact convexHull_mono (Set.image_mono subset)

theorem supportHull_injective (points : Fin 8 → rows → ℚ)
    (zeroOne : ∀ idx, realPoints points idx ∈ zeroOneVectors rows)
    (injective : Function.Injective (realPoints points)) : Function.Injective (supportHull points) := by
  intro left right same
  exact Finset.Subset.antisymm
    ((supportHull_subset_iff points zeroOne injective left right).mp same.subset)
    ((supportHull_subset_iff points zeroOne injective right left).mp same.symm.subset)

def IsCarrierSupport (baseFaces : Finset (Finset (Fin 8))) (face cell : Finset (Fin 8)) : Prop :=
  face ∈ baseFaces ∧ cell ⊆ face ∧ ∀ other ∈ baseFaces, cell ⊆ other → face ⊆ other

instance (baseFaces : Finset (Finset (Fin 8))) (face cell : Finset (Fin 8)) :
    Decidable (IsCarrierSupport baseFaces face cell) := by
  unfold IsCarrierSupport
  infer_instance

theorem isCarrier_supportHull_iff (points : Fin 8 → rows → ℚ)
    (zeroOne : ∀ idx, realPoints points idx ∈ zeroOneVectors rows)
    (injective : Function.Injective (realPoints points))
    (base : Set (rows → ℝ)) (baseFaces : Finset (Finset (Fin 8)))
    (faces : {F | IsFace base F} = supportHull points '' (baseFaces : Set (Finset (Fin 8))))
    (face cell : Finset (Fin 8)) :
    IsCarrier base (supportHull points face) (supportHull points cell) ↔ IsCarrierSupport baseFaces face cell := by
  have face_iff (support : Finset (Fin 8)) : IsFace base (supportHull points support) ↔ support ∈ baseFaces := by
    change supportHull points support ∈ {F | IsFace base F} ↔ _
    rw [faces, Set.mem_image]
    constructor
    · rintro ⟨other, member, equal⟩
      exact (supportHull_injective points zeroOne injective equal) ▸ member
    · exact fun member => ⟨support, member, rfl⟩
  constructor
  · rintro ⟨hf, subset, minimal⟩
    refine ⟨(face_iff face).mp hf, (supportHull_subset_iff points zeroOne injective _ _).mp subset, ?_⟩
    intro other ho hc
    apply (supportHull_subset_iff points zeroOne injective _ _).mp
    exact minimal _ ((face_iff other).mpr ho) ((supportHull_subset_iff points zeroOne injective _ _).mpr hc)
  · rintro ⟨hf, subset, minimal⟩
    refine ⟨(face_iff face).mpr hf, (supportHull_subset_iff points zeroOne injective _ _).mpr subset, ?_⟩
    intro other ho hc
    have member : other ∈ {F | IsFace base F} := ho
    rw [faces] at member
    obtain ⟨support, hs, rfl⟩ := member
    exact (supportHull_subset_iff points zeroOne injective _ _).mpr
      (minimal support hs ((supportHull_subset_iff points zeroOne injective _ _).mp hc))

def carriedSupports (baseFaces family : Finset (Finset (Fin 8)))
    (dimension : Finset (Fin 8) → ℕ) (face : Finset (Fin 8)) (dim : ℕ) : Finset (Finset (Fin 8)) :=
  family.filter fun support => dimension support = dim ∧ IsCarrierSupport baseFaces face support

theorem carrier_count_eq (points : Fin 8 → rows → ℚ)
    (zeroOne : ∀ idx, realPoints points idx ∈ zeroOneVectors rows)
    (injective : Function.Injective (realPoints points))
    (base : Set (rows → ℝ)) (baseFaces family : Finset (Finset (Fin 8)))
    (faces : {F | IsFace base F} = supportHull points '' (baseFaces : Set (Finset (Fin 8))))
    (dimension : Finset (Fin 8) → ℕ)
    (dimensions : ∀ support ∈ family, adim (supportHull points support) = dimension support)
    (face : Finset (Fin 8)) (dim : ℕ) :
    {cell | cell ∈ supportHull points '' (family : Set (Finset (Fin 8))) ∧
      adim cell = dim ∧ IsCarrier base (supportHull points face) cell}.ncard =
      (carriedSupports baseFaces family dimension face dim).card := by
  have equal : {cell | cell ∈ supportHull points '' (family : Set (Finset (Fin 8))) ∧
      adim cell = dim ∧ IsCarrier base (supportHull points face) cell} =
      supportHull points '' (carriedSupports baseFaces family dimension face dim : Set (Finset (Fin 8))) := by
    ext cell
    constructor
    · rintro ⟨⟨support, hs, rfl⟩, hd, hc⟩
      refine ⟨support, Finset.mem_filter.mpr ⟨hs, ?_, ?_⟩, rfl⟩
      · exact (dimensions support hs).symm.trans hd
      · exact (isCarrier_supportHull_iff points zeroOne injective base baseFaces faces face support).mp hc
    · rintro ⟨support, hs, rfl⟩
      obtain ⟨hs, hd, hc⟩ := Finset.mem_filter.mp hs
      exact ⟨⟨support, hs, rfl⟩, (dimensions support hs).trans hd,
        (isCarrier_supportHull_iff points zeroOne injective base baseFaces faces face support).mpr hc⟩
  rw [equal, Set.ncard_image_of_injective _ (supportHull_injective points zeroOne injective),
    Set.ncard_coe_finset]

end HibiLi.Example21
