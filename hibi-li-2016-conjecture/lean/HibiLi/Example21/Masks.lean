/-
HibiLi/Example21/Masks.lean — exact enumeration of all eight-generator subsets.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.DimensionCertificate

namespace HibiLi.Example21

def maskFinset (mask : Fin 256) : Finset (Fin 8) :=
  Finset.univ.filter fun idx => mask.val.testBit idx.val

theorem maskFinset_injective : Function.Injective maskFinset := by
  intro first second heq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro idx
  by_cases hi : idx < 8
  · have hh := Finset.ext_iff.mp heq ⟨idx, hi⟩
    simpa [maskFinset] using hh
  · have hi' : 8 ≤ idx := Nat.le_of_not_gt hi
    have hp : 256 ≤ 2 ^ idx := by
      calc
        256 = 2 ^ 8 := by norm_num
        _ ≤ 2 ^ idx := Nat.pow_le_pow_right (by decide) hi'
    rw [Nat.testBit_eq_false_of_lt (first.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (second.isLt.trans_le hp)]

theorem maskFinset_surjective : Function.Surjective maskFinset := by
  have hcard : Fintype.card (Fin 256) = Fintype.card (Finset (Fin 8)) := by simp
  exact ((Fintype.bijective_iff_injective_and_card maskFinset).mpr
    ⟨maskFinset_injective, hcard⟩).2

noncomputable def maskEquiv : Fin 256 ≃ Finset (Fin 8) :=
  Equiv.ofBijective maskFinset ⟨maskFinset_injective, maskFinset_surjective⟩

end HibiLi.Example21
