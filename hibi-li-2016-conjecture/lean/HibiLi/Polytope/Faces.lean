/-
HibiLiLean — basic nonempty-face and carrier facts.
-/
import HibiLi.Defs.Polytope

namespace HibiLi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsFace.subset {body face : Set E} (hface : IsFace body face) : face ⊆ body :=
  hface.2.subset

theorem IsFace.refl {body : Set E} (nonempty : body.Nonempty) : IsFace body body :=
  ⟨nonempty, IsExposed.refl body⟩

theorem IsFace.inter {body left right : Set E} (hleft : IsFace body left)
    (hright : IsFace body right) (nonempty : (left ∩ right).Nonempty) :
    IsFace body (left ∩ right) :=
  ⟨nonempty, hleft.2.inter hright.2⟩

theorem IsFace.mono {body face middle : Set E} (hface : IsFace body face)
    (middle_subset : middle ⊆ body) (face_subset : face ⊆ middle) : IsFace middle face :=
  ⟨hface.1, hface.2.mono middle_subset face_subset⟩

theorem IsCarrier.unique {body cell left right : Set E}
    (hleft : IsCarrier body left cell) (hright : IsCarrier body right cell) : left = right :=
  Set.Subset.antisymm (hleft.2.2 right hright.1 hright.2.1)
    (hright.2.2 left hleft.1 hleft.2.1)

end HibiLi
