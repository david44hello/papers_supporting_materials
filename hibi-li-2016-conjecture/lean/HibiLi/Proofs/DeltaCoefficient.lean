/- Counts are cast to integers BEFORE subtraction. Degenerate check:
for k=0 no face contains a nonzero vertical segment; above ambient dimension
both face counts vanish. The partition/cancellation proof covers both cases.
The final paper row instantiates hFourier with the cited Fourier Lemma 4.1. -/
import HibiLi.Proofs.VerticalCount
import HibiLi.Proofs.FacePoly
import HibiLi.Polytope.FiniteFaces
import HibiLi.Polytope.Dimension

namespace HibiLi.Proofs

theorem fNum_vertical_partition {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (Q : Set (P → ℝ)) (hQ : IsPolytope Q) (k : ℕ) :
    {F | IsFace Q F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard +
      {F | IsFace Q F ∧ adim F = k ∧ HasVertical s F}.ncard = fNum Q k := by
  classical
  have finiteN : {F | IsFace Q F ∧ adim F = k ∧ ¬ HasVertical s F}.Finite :=
    hQ.finite_faces.subset fun _ h => h.1
  have finiteV : {F | IsFace Q F ∧ adim F = k ∧ HasVertical s F}.Finite :=
    hQ.finite_faces.subset fun _ h => h.1
  have disjoint : Disjoint {F | IsFace Q F ∧ adim F = k ∧ ¬ HasVertical s F}
      {F | IsFace Q F ∧ adim F = k ∧ HasVertical s F} :=
    Set.disjoint_left.mpr fun _ hN hV => hN.2.2 hV.2.2
  rw [← Set.ncard_union_eq disjoint finiteN finiteV]
  apply congrArg Set.ncard
  ext F
  simp only [faces, Set.mem_union, Set.mem_ofPred_eq]
  tauto

/-- l.439-440: F_B+F_R-F_S-F_T compares the nonvertical face counts after and before the switch. -/
theorem sec3_nonvertical_coefficient_of {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (hFourier : facePoly (chainOrderPolytope P (insert s.q s.I)) -
      facePoly (chainOrderPolytope P s.I) =
        facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT) (k : ℕ) :
    ({F | IsFace (chainOrderPolytope P (insert s.q s.I)) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard : ℤ) -
      ({F | IsFace (chainOrderPolytope P s.I) F ∧ adim F = k ∧ ¬ HasVertical s F}.ncard : ℤ) =
        (facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT).coeff k := by
  have before := fNum_vertical_partition s (chainOrderPolytope P s.I)
    (chainOrderPolytope_isPolytope P s.I) k
  have after := fNum_vertical_partition s (chainOrderPolytope P (insert s.q s.I))
    (chainOrderPolytope_isPolytope P (insert s.q s.I)) k
  have vertical := sec3_informal_vertical_count s k
  have total := congrArg (fun p : Polynomial ℤ => p.coeff k) hFourier
  rw [Polynomial.coeff_sub, facePoly_coeff, facePoly_coeff] at total
  omega

end HibiLi.Proofs

#print axioms HibiLi.Proofs.sec3_nonvertical_coefficient_of
