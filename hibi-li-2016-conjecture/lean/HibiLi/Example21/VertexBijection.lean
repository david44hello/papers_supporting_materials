/-
HibiLi/Example21/VertexBijection.lean — upper sets, antichains, and geometric vertices.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Example21.ZeroOneFaces

namespace HibiLi

variable {P : Type*} [Fintype P] [PartialOrder P]

noncomputable def setVector (S : Set P) : P → ℝ := S.indicator (fun _ => 1)

@[simp] theorem setVector_eq_one (S : Set P) (pp : P) : setVector S pp = 1 ↔ pp ∈ S := by
  classical
  by_cases hp : pp ∈ S <;> simp [setVector, hp]

theorem setVector_zeroOne (S : Set P) : setVector S ∈ zeroOneVectors P := by
  classical
  intro pp
  by_cases hp : pp ∈ S <;> simp [setVector, hp]

theorem setVector_support {v : P → ℝ} (hv : v ∈ zeroOneVectors P) :
    setVector {pp | v pp = 1} = v := by
  classical
  ext pp
  rcases hv pp with hz | ho
  · simp [setVector, hz]
  · simp [setVector, ho]

theorem setVector_upper_mem {S : Set P} (hS : IsUpperSet S) : setVector S ∈ orderPolytope P := by
  classical
  constructor
  · intro pp
    by_cases hp : pp ∈ S <;> simp [setVector, hp]
  · intro pp qq hpq
    by_cases hp : pp ∈ S
    · have hq := hS hpq hp
      simp [setVector, hp, hq]
    · by_cases hq : qq ∈ S <;> simp [setVector, hp, hq]

theorem support_upper {v : P → ℝ} (hv : v ∈ orderPolytope P) :
    IsUpperSet {pp | v pp = 1} := by
  intro pp qq hpq hp
  have hmono := hv.2 pp qq hpq
  have hbound := (hv.1 qq).2
  change v pp = 1 at hp
  change v qq = 1
  linarith

theorem support_antichain {v : P → ℝ} (hv : v ∈ chainPolytope P) :
    IsAntichain (· ≤ ·) {pp | v pp = 1} := by
  classical
  intro pp hp qq hq hne hle
  have hchain : IsChainSet P {pp, qq} := by
    simp only [IsChainSet, Finset.coe_insert, Finset.coe_singleton]
    exact (IsChain.singleton (r := (· ≤ ·)) (a := qq)).insert
      (fun rr hr _ => by rcases Set.mem_singleton_iff.mp hr with rfl; exact Or.inl hle)
  have hh := hv.2 {pp, qq} hchain
  change v pp = 1 at hp
  change v qq = 1 at hq
  norm_num [hne, hp, hq] at hh

theorem setVector_antichain_mem {S : Set P} (hS : IsAntichain (· ≤ ·) S) :
    setVector S ∈ chainPolytope P := by
  apply zeroOne_antichain_mem_chainPolytope (setVector_zeroOne S)
  simpa using hS

noncomputable def upperVectorEquiv :
    {S : Set P // IsUpperSet S} ≃ ↥(orderPolytope P ∩ zeroOneVectors P) where
  toFun S := ⟨setVector S.1, setVector_upper_mem S.2, setVector_zeroOne S.1⟩
  invFun v := ⟨{pp | v.1 pp = 1}, support_upper v.2.1⟩
  left_inv S := by
    apply Subtype.ext
    ext pp
    exact setVector_eq_one S.1 pp
  right_inv v := Subtype.ext (setVector_support v.2.2)

noncomputable def antichainVectorEquiv :
    {S : Set P // IsAntichain (· ≤ ·) S} ≃ ↥(chainPolytope P ∩ zeroOneVectors P) where
  toFun S := ⟨setVector S.1, setVector_antichain_mem S.2, setVector_zeroOne S.1⟩
  invFun v := ⟨{pp | v.1 pp = 1}, support_antichain v.2.1⟩
  left_inv S := by
    apply Subtype.ext
    ext pp
    exact setVector_eq_one S.1 pp
  right_inv v := Subtype.ext (setVector_support v.2.2)

noncomputable def upperAntichainEquiv :
    {S : Set P // IsUpperSet S} ≃ {S : Set P // IsAntichain (· ≤ ·) S} where
  toFun S := ⟨{pp | Minimal (· ∈ S.1) pp}, setOfPred_minimal_antichain _⟩
  invFun S := ⟨(upperClosure S.1 : Set P), (upperClosure S.1).upper⟩
  left_inv S := by
    apply Subtype.ext
    ext pp
    constructor
    · rintro ⟨qq, hq, hqp⟩
      exact S.2 hqp hq.prop
    · intro hp
      obtain ⟨qq, hqp, hq⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ S.1) pp hp
      exact ⟨qq, hq, hqp⟩
  right_inv S := by
    apply Subtype.ext
    ext pp
    exact S.2.minimal_mem_upperClosure_iff_mem

theorem sec1_same_vertices_proved (P : Type*) [Fintype P] [PartialOrder P] :
    fNum (orderPolytope P) 0 = fNum (chainPolytope P) 0 := by
  have horder := fNum_zero_eq_ncard (Q := orderPolytope P) Set.inter_subset_right
    (orderPolytope_eq_convexHull_zeroOne P) (fun _ hw => hw.1)
  have hchain := fNum_zero_eq_ncard (Q := chainPolytope P) Set.inter_subset_right
    (chainPolytope_eq_convexHull_zeroOne P) (fun v hv pp => by
      refine ⟨hv.1 pp, ?_⟩
      have hh := hv.2 {pp} (by simpa [IsChainSet] using (IsChain.singleton (r := (· ≤ ·)) (a := pp)))
      simpa using hh)
  rw [horder, hchain, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr ((upperVectorEquiv (P := P)).symm.trans
    (upperAntichainEquiv.trans antichainVectorEquiv))

end HibiLi
