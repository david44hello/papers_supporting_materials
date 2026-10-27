/-
HibiLi — computable encoding of eight-point supports.
-/
import HibiLi.Example21.Masks

namespace HibiLi.Example21

def maskCode (support : Finset (Fin 8)) : Fin 256 :=
  ⟨(∑ idx ∈ support, 2 ^ idx.val) % 256, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskFinset_maskCode : ∀ support : Finset (Fin 8), maskFinset (maskCode support) = support := by
  decide +kernel

theorem maskCode_maskFinset (mask : Fin 256) : maskCode (maskFinset mask) = mask :=
  maskFinset_injective (maskFinset_maskCode _)

end HibiLi.Example21
