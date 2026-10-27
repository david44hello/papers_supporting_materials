/-
HibiLi — finite carrier counts for the central switch regions.
-/
import HibiLi.Example21.CenterFaces
import HibiLi.Example21.CenterDimension

namespace HibiLi.Example21.CenterRegions

open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem points_injective : Function.Injective (realPoints points) := by
  have rational : Function.Injective points := by decide +kernel
  intro first second same
  apply rational
  funext row
  have h := congrFun same row
  dsimp only [realPoints] at h
  exact_mod_cast h

theorem regionFaces_geometry (lower upper : Option Bool) :
    {F | IsFace (body lower upper) F} =
      supportHull points '' (regionFaces lower upper : Set (Finset (Fin 8))) := by
  rw [regionFaces_checked]
  exact faces_eq_supports lower upper

def baseFaces : Finset (Finset (Fin 8)) := regionFaces none none
def sFaces : Finset (Finset (Fin 8)) := regionFaces (some false) none ∪ regionFaces (some true) none
def tFaces : Finset (Finset (Fin 8)) := regionFaces none (some false) ∪ regionFaces none (some true)
def rFaces : Finset (Finset (Fin 8)) :=
  regionFaces (some false) (some false) ∪ regionFaces (some false) (some true) ∪
    regionFaces (some true) (some false) ∪ regionFaces (some true) (some true)

theorem baseFaces_geometry : {F | IsFace base F} =
    supportHull points '' (baseFaces : Set (Finset (Fin 8))) := regionFaces_geometry none none

theorem sFaces_geometry : familyS = supportHull points '' (sFaces : Set (Finset (Fin 8))) := by
  change {F | ∃ cut : Bool, IsFace (body (some cut) none) F} = _
  simp only [Bool.exists_bool, sFaces, Finset.coe_union, Set.image_union]
  ext F
  have first := Set.ext_iff.mp (regionFaces_geometry (some false) none) F
  have second := Set.ext_iff.mp (regionFaces_geometry (some true) none) F
  exact or_congr first second

theorem tFaces_geometry : familyT = supportHull points '' (tFaces : Set (Finset (Fin 8))) := by
  change {F | ∃ cut : Bool, IsFace (body none (some cut)) F} = _
  simp only [Bool.exists_bool, tFaces, Finset.coe_union, Set.image_union]
  ext F
  have first := Set.ext_iff.mp (regionFaces_geometry none (some false)) F
  have second := Set.ext_iff.mp (regionFaces_geometry none (some true)) F
  exact or_congr first second

theorem rFaces_geometry : familyR = supportHull points '' (rFaces : Set (Finset (Fin 8))) := by
  change {F | ∃ lower upper : Bool, IsFace (body (some lower) (some upper)) F} = _
  simp only [Bool.exists_bool, rFaces, Finset.coe_union, Set.image_union]
  ext F
  have ff := Set.ext_iff.mp (regionFaces_geometry (some false) (some false)) F
  have ft := Set.ext_iff.mp (regionFaces_geometry (some false) (some true)) F
  have tf := Set.ext_iff.mp (regionFaces_geometry (some true) (some false)) F
  have tt := Set.ext_iff.mp (regionFaces_geometry (some true) (some true)) F
  simp only [Set.mem_ofPred_eq, Set.mem_union] at *
  tauto

theorem family_dimensions_checked : ∀ support ∈ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces,
    0 < (maskCode support).val ∧ (maskCode support).val < 128 ∧ dimension support ≤ 4 := by
  decide +kernel

theorem family_dimension_eq {support : Finset (Fin 8)}
    (member : support ∈ baseFaces ∪ sFaces ∪ tFaces ∪ rFaces) :
    adim (supportHull points support) = dimension support :=
  dimension_eq support (family_dimensions_checked support member).1
    (family_dimensions_checked support member).2.1

def count (family : Finset (Finset (Fin 8))) (face : Finset (Fin 8)) (dim : ℕ) : ℕ :=
  (carriedSupports baseFaces family dimension face dim).card

theorem base_vertices : vertices none none = maskFinset 127 := by decide +kernel

theorem base_counts_checked : ∀ dim : Fin 5,
    count sFaces (maskFinset 127) dim = (if dim.val = 4 then 2 else if dim.val = 3 then 1 else 0) ∧
    count tFaces (maskFinset 127) dim = (if dim.val = 4 then 2 else if dim.val = 3 then 1 else 0) ∧
    count rFaces (maskFinset 127) dim =
      (if dim.val = 4 then 4 else if dim.val = 3 then 4 else if dim.val = 2 then 1 else 0) := by
  decide +kernel

theorem proper_counts_checked : ∀ face ∈ baseFaces, face ≠ maskFinset 127 → ∀ dim : Fin 5,
    (count rFaces face dim : ℤ) - count sFaces face dim - count tFaces face dim +
      (if dim.val = dimension face then 1 else 0) = 0 := by
  decide +kernel


end HibiLi.Example21.CenterRegions
