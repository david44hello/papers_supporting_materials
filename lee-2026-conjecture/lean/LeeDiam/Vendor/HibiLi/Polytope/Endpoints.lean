/-
HibiLiLean — chain-order endpoint identities (sanity S1).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Defs.Poset

namespace HibiLi

variable (P : Type*) [PartialOrder P]

@[simp] theorem chainOrderPolytope_univ :
    chainOrderPolytope P Set.univ = chainPolytope P := by
  ext point
  simp [chainOrderPolytope, chainPolytope]

@[simp] theorem chainOrderPolytope_empty :
    chainOrderPolytope P ∅ = orderPolytope P := by
  ext point
  constructor
  · intro member
    exact ⟨fun coord => member.2.1 coord (by simp),
      fun lower upper relation => member.2.2.1 lower upper (by simp) (by simp) relation⟩
  · rintro ⟨bounds, monotone⟩
    refine ⟨by simp, fun coord _ => bounds coord,
      fun lower upper _ _ relation => monotone lower upper relation, ?_, ?_⟩
    · intro coord _ chain subset _ _
      have empty : chain = ∅ := Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp subset)
      simpa [empty] using (bounds coord).1
    · intro chain subset _
      have empty : chain = ∅ := Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp subset)
      simp [empty]

end HibiLi
