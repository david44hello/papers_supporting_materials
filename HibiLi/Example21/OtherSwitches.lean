/-
HibiLi — the four outer switches in Proposition 5.1.
-/
import HibiLi.Defs.Examples
import HibiLi.Polytope.AffinityComplex
import HibiLi.Polytope.Dimension

namespace HibiLi

open Finset Polynomial

namespace Switch

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

theorem lowBranches_eq_singleton_empty (hmin : ∀ p : P, ¬ p < s.q) :
    s.lowBranches = {∅} := by
  classical
  ext K
  simp only [lowBranches, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨_, _, below⟩
    exact Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => hmin p (below p hp))
  · rintro rfl
    simp [IsChainSet]

theorem upBranches_eq_singleton_none (hmax : ∀ p : P, ¬ s.q < p) :
    s.upBranches = {none} := by
  classical
  have empty : (univ.filter (fun r : s.P' => s.q < r.1)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p _
    exact hmax p
  simp [upBranches, empty]

theorem L_eq_zero_of_minimal (hmin : ∀ p : P, ¬ p < s.q) (u : s.P' → ℝ) : s.L u = 0 := by
  simp [L, s.lowBranches_eq_singleton_empty hmin, chainSum]

theorem U_eq_one_of_maximal (hmax : ∀ p : P, ¬ s.q < p) (u : s.P' → ℝ) : s.U u = 1 := by
  simp [U, s.upBranches_eq_singleton_none hmax, upVal]

theorem cellsS_eq_faces_of_minimal (hmin : ∀ p : P, ¬ p < s.q) :
    s.cellsS = {C | IsFace s.B C} := by
  classical
  have dom : s.domL ∅ = s.B := by
    ext u
    simp [domL, s.L_eq_zero_of_minimal hmin, chainSum]
  ext C
  simp [cellsS, s.lowBranches_eq_singleton_empty hmin, dom,
    show adim s.B = Fintype.card s.P' from chainOrderPolytope_adim _ _]

theorem cellsT_eq_faces_of_maximal (hmax : ∀ p : P, ¬ s.q < p) :
    s.cellsT = {C | IsFace s.B C} := by
  classical
  have dom : s.domU none = s.B := by
    ext u
    simp [domU, s.U_eq_one_of_maximal hmax, upVal]
  ext C
  simp [cellsT, s.upBranches_eq_singleton_none hmax, dom,
    show adim s.B = Fintype.card s.P' from chainOrderPolytope_adim _ _]

theorem cellsR_eq_T_of_S_faces (hS : s.cellsS = {C | IsFace s.B C}) : s.cellsR = s.cellsT := by
  ext C
  constructor
  · rintro ⟨hne, A, hA, D, hD, rfl⟩
    have faceA : IsFace s.B A := by simpa [hS] using hA
    have subsetD : D ⊆ s.B := by
      obtain ⟨j, _, _, hj⟩ := hD
      exact hj.subset.trans fun _ hu => hu.1
    have faceAD : IsFace D (A ∩ D) := by
      simpa only [Set.inter_comm] using
        faceA.inter_subset subsetD (by simpa only [Set.inter_comm] using hne)
    exact s.cellsT_face_closed hD faceAD
  · intro hC
    have faceC := hC
    obtain ⟨j, _, _, hj⟩ := faceC
    have subsetC : C ⊆ s.B := hj.subset.trans fun _ hu => hu.1
    refine ⟨hj.1, s.B, ?_, C, hC, ?_⟩
    · rw [hS]
      exact IsFace.refl (hj.1.mono subsetC)
    · exact (Set.inter_eq_right.mpr subsetC).symm

theorem cellsR_eq_S_of_T_faces (hT : s.cellsT = {C | IsFace s.B C}) : s.cellsR = s.cellsS := by
  ext C
  constructor
  · rintro ⟨hne, A, hA, D, hD, rfl⟩
    have faceD : IsFace s.B D := by simpa [hT] using hD
    have subsetA : A ⊆ s.B := by
      obtain ⟨K, _, _, hK⟩ := hA
      exact hK.subset.trans fun _ hu => hu.1
    exact s.cellsS_face_closed hA (faceD.inter_subset subsetA hne)
  · intro hC
    have faceC := hC
    obtain ⟨K, _, _, hK⟩ := faceC
    have subsetC : C ⊆ s.B := hK.subset.trans fun _ hu => hu.1
    refine ⟨hK.1, C, hC, s.B, ?_, ?_⟩
    · rw [hT]
      exact IsFace.refl (hK.1.mono subsetC)
    · exact (Set.inter_eq_left.mpr subsetC).symm

end Switch

theorem cellPoly_faces {ι : Type*} [Fintype ι] (B : Set (ι → ℝ)) :
    cellPoly {C | IsFace B C} = facePoly B := rfl

namespace Example21

local instance : DecidableLT XElem := decidableLTOfDecidableLE

lemma outer_minimal (s : Switch XElem) (hq : s.q = XElem.a ∨ s.q = XElem.b) :
    ∀ p : XElem, ¬ p < s.q := by
  rcases hq with hq | hq <;> rw [hq] <;> decide

lemma outer_maximal (s : Switch XElem) (hq : s.q = XElem.g ∨ s.q = XElem.h) :
    ∀ p : XElem, ¬ s.q < p := by
  rcases hq with hq | hq <;> rw [hq] <;> decide

end Example21

/-- Fourier's identity is supplied explicitly by the caller. -/
theorem prop_5_1_other_switches_of (s : Switch XElem)
    (identity : facePoly (chainOrderPolytope XElem (insert s.q s.I)) -
      facePoly (chainOrderPolytope XElem s.I) =
      facePoly s.B + cellPoly s.cellsR - cellPoly s.cellsS - cellPoly s.cellsT) :
    ((s.q = XElem.a ∨ s.q = XElem.b) → ∀ u ∈ s.B, s.L u = 0) ∧
    ((s.q = XElem.g ∨ s.q = XElem.h) → ∀ u ∈ s.B, s.U u = 1) ∧
    (s.q ≠ XElem.c → facePoly (chainOrderPolytope XElem (insert s.q s.I)) =
      facePoly (chainOrderPolytope XElem s.I)) := by
  refine ⟨fun hq u _ => s.L_eq_zero_of_minimal (Example21.outer_minimal s hq) u,
    fun hq u _ => s.U_eq_one_of_maximal (Example21.outer_maximal s hq) u, ?_⟩
  intro hq
  have outer : (s.q = XElem.a ∨ s.q = XElem.b) ∨ (s.q = XElem.g ∨ s.q = XElem.h) := by
    cases heq : s.q <;> simp_all
  apply sub_eq_zero.mp
  rw [identity]
  rcases outer with lower | upper
  · have hS := s.cellsS_eq_faces_of_minimal (Example21.outer_minimal s lower)
    rw [s.cellsR_eq_T_of_S_faces hS, hS, cellPoly_faces]
    ring
  · have hT := s.cellsT_eq_faces_of_maximal (Example21.outer_maximal s upper)
    rw [s.cellsR_eq_S_of_T_faces hT, hT, cellPoly_faces]
    ring

end HibiLi
