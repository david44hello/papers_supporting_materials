/-
HibiLi — the nine regions used for the center switch.
-/
import HibiLi.Defs.Polytope

namespace HibiLi.Example21.CenterRegions

/-- Coordinates are `(a,b,g,h)`. A true lower cut means `b ≤ a`; a true upper cut means `h ≤ g`. -/
def body (lower upper : Option Bool) : Set (Fin 4 → ℝ) :=
  {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ v 0 ≤ v 2 ∧ v 0 ≤ v 3 ∧ v 1 ≤ v 2 ∧ v 1 ≤ v 3 ∧
    v 2 ≤ 1 ∧ v 3 ≤ 1 ∧
    (match lower with | none => True | some false => v 0 ≤ v 1 | some true => v 1 ≤ v 0) ∧
    (match upper with | none => True | some false => v 2 ≤ v 3 | some true => v 3 ≤ v 2)}

def allFaces (region : Set (Fin 4 → ℝ)) : Set (Set (Fin 4 → ℝ)) := {F | IsFace region F}

def base : Set (Fin 4 → ℝ) := body none none
def familyS : Set (Set (Fin 4 → ℝ)) := {F | ∃ cut : Bool, IsFace (body (some cut) none) F}
def familyT : Set (Set (Fin 4 → ℝ)) := {F | ∃ cut : Bool, IsFace (body none (some cut)) F}
def familyR : Set (Set (Fin 4 → ℝ)) :=
  {F | ∃ lower upper : Bool, IsFace (body (some lower) (some upper)) F}

end HibiLi.Example21.CenterRegions
