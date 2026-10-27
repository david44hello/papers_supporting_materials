/-
HibiLi/Proofs/SPaperDefFull.lean — the paper's full definition of `S` and `T` (paper v1.00 lines 274–277): the maximal
full-dimensional convex subsets of `B` on which `L` (resp. `U`) is affine, together with all their nonempty faces.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Lemma36
import HibiLi.Polytope.TopCells

namespace HibiLi.Proofs

open HibiLi

/-- **Definition of `S` and `T`, both halves** (paper lines 274–277): "the maximal full-dimensional convex subsets of
`B` on which `L` is affine, together with all their nonempty faces", and the same for `T` with `U`.  The
full-dimensional half is `sec3_S_paper_def_proved`; a full-dimensional face of an affinity domain is the domain
itself (`IsFace.eq_of_adim_eq`), and every full-dimensional affinity domain is a face of itself. -/
theorem sec3_S_paper_def_full_proved {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    s.cellsS = {C | ∃ A, (A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧ AffineOn s.L A ∧
        ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.L D → D = A) ∧ IsFace A C} ∧
    s.cellsT = {C | ∃ A, (A ⊆ s.B ∧ Convex ℝ A ∧ adim A = Fintype.card s.P' ∧ AffineOn s.U A ∧
        ∀ D, A ⊆ D → D ⊆ s.B → Convex ℝ D → AffineOn s.U D → D = A) ∧ IsFace A C} := by
  constructor
  · ext C
    constructor
    · rintro ⟨K, hK, hdim, hface⟩
      have hA : s.domL K ∈ s.cellsS := ⟨K, hK, hdim, IsFace.refl (hface.1.mono hface.subset)⟩
      exact ⟨s.domL K, (sec3_S_paper_def_proved s _).1.mp ⟨hA, hdim⟩, hface⟩
    · rintro ⟨A, hmax, hface⟩
      obtain ⟨⟨K, hK, hdim, hAface⟩, hAdim⟩ := (sec3_S_paper_def_proved s A).1.mpr hmax
      have hAK : A = s.domL K := hAface.eq_of_adim_eq (hAdim.trans hdim.symm)
      subst hAK
      exact ⟨K, hK, hdim, hface⟩
  · ext C
    constructor
    · rintro ⟨j, hj, hdim, hface⟩
      have hA : s.domU j ∈ s.cellsT := ⟨j, hj, hdim, IsFace.refl (hface.1.mono hface.subset)⟩
      exact ⟨s.domU j, (sec3_S_paper_def_proved s _).2.mp ⟨hA, hdim⟩, hface⟩
    · rintro ⟨A, hmax, hface⟩
      obtain ⟨⟨j, hj, hdim, hAface⟩, hAdim⟩ := (sec3_S_paper_def_proved s A).2.mpr hmax
      have hAj : A = s.domU j := hAface.eq_of_adim_eq (hAdim.trans hdim.symm)
      subst hAj
      exact ⟨j, hj, hdim, hface⟩

end HibiLi.Proofs
