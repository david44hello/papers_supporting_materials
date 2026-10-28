/-
HibiLi/Example21/ChainIntervals.lean — weighted lower chains give disjoint intervals.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Vendor.HibiLi.Example21.ZeroOne

namespace HibiLi

variable {P : Type*} [Fintype P] [PartialOrder P]

noncomputable def lowerChains (pp : P) : Finset (Finset P) := by
  classical
  exact Finset.univ.filter fun K => IsChainSet P K ∧ ∀ qq ∈ K, qq < pp

theorem lowerChains_nonempty (pp : P) : (lowerChains pp).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp only [lowerChains, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨by simpa only [IsChainSet, Finset.coe_empty] using (IsChain.empty (r := (· ≤ ·))), by simp⟩

noncomputable def chainStart (x : P → ℝ) (pp : P) : ℝ :=
  (lowerChains pp).sup' (lowerChains_nonempty pp) (fun K => ∑ qq ∈ K, x qq)

noncomputable def chainFinish (x : P → ℝ) (pp : P) : ℝ := chainStart x pp + x pp

theorem chainStart_attained (x : P → ℝ) (pp : P) :
    ∃ K : Finset P, IsChainSet P K ∧ (∀ qq ∈ K, qq < pp) ∧ chainStart x pp = ∑ qq ∈ K, x qq := by
  classical
  obtain ⟨K, hK, hsum⟩ := Finset.exists_mem_eq_sup' (lowerChains_nonempty pp)
    (fun K => ∑ qq ∈ K, x qq)
  have hconditions : IsChainSet P K ∧ ∀ qq ∈ K, qq < pp := by
    simpa [lowerChains] using hK
  exact ⟨K, hconditions.1, hconditions.2, hsum⟩

theorem chainStart_nonneg (x : P → ℝ) (pp : P) : 0 ≤ chainStart x pp := by
  classical
  have hempty : (∅ : Finset P) ∈ lowerChains pp := by
    simp only [lowerChains, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by simpa only [IsChainSet, Finset.coe_empty] using (IsChain.empty (r := (· ≤ ·))), by simp⟩
  calc
    0 = ∑ qq ∈ (∅ : Finset P), x qq := by simp
    _ ≤ chainStart x pp := Finset.le_sup' (fun K : Finset P => ∑ qq ∈ K, x qq) hempty

omit [Fintype P] in
theorem lowerChain_insert [DecidableEq P] {K : Finset P} {pp : P} (hchain : IsChainSet P K)
    (hlower : ∀ qq ∈ K, qq < pp) : IsChainSet P (insert pp K) := by
  classical
  change IsChain (· ≤ ·) ((insert pp K : Finset P) : Set P)
  rw [Finset.coe_insert]
  exact hchain.insert (fun qq hq _ => Or.inr (hlower qq hq).le)

theorem chainFinish_le_one {x : P → ℝ} (hx : x ∈ chainPolytope P) (pp : P) :
    chainFinish x pp ≤ 1 := by
  classical
  obtain ⟨K, hchain, hlower, hsum⟩ := chainStart_attained x pp
  have hn : pp ∉ K := fun hp => (hlower pp hp).false
  have hh := hx.2 (insert pp K) (lowerChain_insert hchain hlower)
  simpa [Finset.sum_insert hn, chainFinish, hsum, add_comm] using hh

theorem chainFinish_le_chainStart {x : P → ℝ} {pp qq : P} (hpq : pp < qq) :
    chainFinish x pp ≤ chainStart x qq := by
  classical
  obtain ⟨K, hchain, hlower, hsum⟩ := chainStart_attained x pp
  have hn : pp ∉ K := fun hp => (hlower pp hp).false
  have hK : insert pp K ∈ lowerChains qq := by
    simp only [lowerChains, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨lowerChain_insert hchain hlower, ?_⟩
    intro rr hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hpq
    · exact (hlower rr hr).trans hpq
  calc
    chainFinish x pp = ∑ rr ∈ insert pp K, x rr := by
      rw [chainFinish, hsum, Finset.sum_insert hn]
      ring
    _ ≤ chainStart x qq := Finset.le_sup' (fun K : Finset P => ∑ rr ∈ K, x rr) hK

end HibiLi
