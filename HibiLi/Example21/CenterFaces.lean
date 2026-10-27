/-
HibiLi center-switch face supports.
-/
import HibiLi.Example21.CenterRanks
import HibiLi.Example21.SupportCarriers
import HibiLi.Example21.DiscreteFaces
namespace HibiLi.Example21.CenterRegions
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def faceMaskList (lower upper : Option Bool) : Finset (Fin 256) :=
  match lower, upper with
  | none, none => {1, 2, 3, 4, 5, 8, 10, 12, 15, 16, 17, 18, 19, 20, 21, 24, 26, 28, 31, 32, 33, 34, 35, 36, 37, 40, 42, 44, 47, 64, 65, 66, 67, 68, 69, 80, 81, 82, 83, 84, 85, 96, 97, 98, 99, 100, 101, 120, 122, 124, 127}
  | none, some false => {1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 32, 33, 36, 37, 40, 41, 44, 45, 64, 65, 68, 69, 80, 81, 84, 85, 96, 97, 100, 101, 120, 121, 124, 125}
  | none, some true => {1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 32, 33, 34, 35, 40, 41, 42, 43, 64, 65, 66, 67, 80, 81, 82, 83, 96, 97, 98, 99, 120, 121, 122, 123}
  | some false, none => {1, 2, 3, 4, 5, 8, 10, 12, 15, 32, 33, 34, 35, 36, 37, 40, 42, 44, 47, 64, 65, 66, 67, 68, 69, 72, 74, 76, 79, 96, 97, 98, 99, 100, 101, 104, 106, 108, 111}
  | some false, some false => {1, 4, 5, 8, 9, 12, 13, 32, 33, 36, 37, 40, 41, 44, 45, 64, 65, 68, 69, 72, 73, 76, 77, 96, 97, 100, 101, 104, 105, 108, 109}
  | some false, some true => {1, 2, 3, 8, 9, 10, 11, 32, 33, 34, 35, 40, 41, 42, 43, 64, 65, 66, 67, 72, 73, 74, 75, 96, 97, 98, 99, 104, 105, 106, 107}
  | some true, none => {1, 2, 3, 4, 5, 8, 10, 12, 15, 16, 17, 18, 19, 20, 21, 24, 26, 28, 31, 64, 65, 66, 67, 68, 69, 72, 74, 76, 79, 80, 81, 82, 83, 84, 85, 88, 90, 92, 95}
  | some true, some false => {1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93}
  | some true, some true => {1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27, 64, 65, 66, 67, 72, 73, 74, 75, 80, 81, 82, 83, 88, 89, 90, 91}
def regionFaces (lower upper : Option Bool) : Finset (Finset (Fin 8)) :=
  (faceMaskList lower upper).image maskFinset

def parentMask : Option Bool → Option Bool → Fin 256
  | none, none => 127
  | none, (some false) => 125
  | none, (some true) => 123
  | (some false), none => 111
  | (some false), (some false) => 109
  | (some false), (some true) => 107
  | (some true), none => 95
  | (some true), (some false) => 93
  | (some true), (some true) => 91

def tightMasks (lower upper : Option Bool) : Fin 10 → Fin 256 :=
  ![47,159,85,83,229,227,122,124,
    (if lower.isNone then 255 else 79), (if upper.isNone then 255 else 249)]

private theorem parents_checked : ∀ lower upper : Option Bool,
    vertices lower upper = maskFinset (parentMask lower upper) := by decide +kernel

private theorem scores_checked : ∀ (lower upper : Option Bool) (index : Fin 10) (idx : Fin 8),
    rationalScore points (normals lower upper index) idx = bounds index ↔
      idx ∈ maskFinset (tightMasks lower upper index) := by decide +kernel

private theorem checked00 : regionFaces none none =
    discreteFaceSupports (maskFinset (parentMask none none))
      (fun index => maskFinset (tightMasks none none index)) := by decide +kernel
private theorem checked01 : regionFaces none (some false) =
    discreteFaceSupports (maskFinset (parentMask none (some false)))
      (fun index => maskFinset (tightMasks none (some false) index)) := by decide +kernel
private theorem checked02 : regionFaces none (some true) =
    discreteFaceSupports (maskFinset (parentMask none (some true)))
      (fun index => maskFinset (tightMasks none (some true) index)) := by decide +kernel
private theorem checked10 : regionFaces (some false) none =
    discreteFaceSupports (maskFinset (parentMask (some false) none))
      (fun index => maskFinset (tightMasks (some false) none index)) := by decide +kernel
private theorem checked11 : regionFaces (some false) (some false) =
    discreteFaceSupports (maskFinset (parentMask (some false) (some false)))
      (fun index => maskFinset (tightMasks (some false) (some false) index)) := by decide +kernel
private theorem checked12 : regionFaces (some false) (some true) =
    discreteFaceSupports (maskFinset (parentMask (some false) (some true)))
      (fun index => maskFinset (tightMasks (some false) (some true) index)) := by decide +kernel
private theorem checked20 : regionFaces (some true) none =
    discreteFaceSupports (maskFinset (parentMask (some true) none))
      (fun index => maskFinset (tightMasks (some true) none index)) := by decide +kernel
private theorem checked21 : regionFaces (some true) (some false) =
    discreteFaceSupports (maskFinset (parentMask (some true) (some false)))
      (fun index => maskFinset (tightMasks (some true) (some false) index)) := by decide +kernel
private theorem checked22 : regionFaces (some true) (some true) =
    discreteFaceSupports (maskFinset (parentMask (some true) (some true)))
      (fun index => maskFinset (tightMasks (some true) (some true) index)) := by decide +kernel

theorem regionFaces_checked : ∀ lower upper : Option Bool,
    regionFaces lower upper = faceSupports points (vertices lower upper) (normals lower upper) bounds := by
  intro lower upper
  rw [faceSupports_eq_discrete points _ _ _ (fun index => maskFinset (tightMasks lower upper index))
    (scores_checked lower upper), parents_checked]
  fin_cases lower <;> fin_cases upper <;>
    first | exact checked00 | exact checked01 | exact checked02 | exact checked10 | exact checked11 |
      exact checked12 | exact checked20 | exact checked21 | exact checked22
end HibiLi.Example21.CenterRegions
