/-
HibiLi — separate rational score checking from finite face enumeration.
-/
import HibiLi.Example21.RationalFaces

namespace HibiLi.Example21

variable {rows κ : Type*} [Fintype rows] [Fintype κ] [DecidableEq κ]

def discreteFaceSupports (parent : Finset (Fin 8)) (tight : κ → Finset (Fin 8)) : Finset (Finset (Fin 8)) :=
  ((Finset.univ.powerset).image (fun active : Finset κ =>
    parent.filter fun idx => ∀ index ∈ active, idx ∈ tight index)).erase ∅

theorem faceSupports_eq_discrete (points : Fin 8 → rows → ℚ) (parent : Finset (Fin 8))
    (normal : κ → rows → ℚ) (bound : κ → ℚ) (tight : κ → Finset (Fin 8))
    (scores : ∀ index idx, rationalScore points (normal index) idx = bound index ↔ idx ∈ tight index) :
    faceSupports points parent normal bound = discreteFaceSupports parent tight := by
  unfold faceSupports discreteFaceSupports
  congr 2
  funext active
  unfold tightSupport
  simp_rw [scores]

end HibiLi.Example21
