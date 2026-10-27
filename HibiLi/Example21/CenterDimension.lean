/-
HibiLi — all center-switch regions have full dimension.
-/
import HibiLi.Example21.CenterRanks

namespace HibiLi.Example21.CenterRegions

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem body_adim (lower upper : Option Bool) : adim (body lower upper) = 4 := by
  have checked : ∀ lower upper : Option Bool,
      0 < (maskCode (vertices lower upper)).val ∧ (maskCode (vertices lower upper)).val < 128 ∧
      dimension (vertices lower upper) = 4 := by decide +kernel
  obtain ⟨positive, bounded, dim⟩ := checked lower upper
  rw [body_eq_hull, dimension_eq _ positive bounded, dim]

end HibiLi.Example21.CenterRegions
