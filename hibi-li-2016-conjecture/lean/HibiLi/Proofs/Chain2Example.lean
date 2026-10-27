/-
HibiLi/Proofs/Chain2Example.lean — paper Section 3, the two-chain example: the switch on `a < b` with `I = {a}`, `q = b`
has `B = [0,1]`, `L(u) = u`, `U(u) = 1`, and its endpoints are `O(P)` and `C(P)` (statement `sec3_chain2_example` of
HibiLi/Paper/Statements.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Switch
import HibiLi.Defs.Examples
import HibiLi.Polytope.Endpoints

namespace HibiLi.Proofs

open HibiLi

/-- The switch of the two-chain `0 < 1` with ideal `I = {0}` and switched element `q = 1`. -/
def chain2Switch : Switch Chain2 where
  I := {0}
  isLowerSet := by
    intro upper lower below member
    rw [Set.mem_singleton_iff] at member ⊢
    subst member
    exact Fin.le_zero_iff.mp below
  q := 1
  q_notMem := by simp
  q_minimal := by
    intro lower below
    fin_cases lower
    · rfl
    · exact absurd below (by decide)

/-- Every element of `P' = P \ {q}` is `0`. -/
theorem chain2Switch_P'_val (p : chain2Switch.P') : p.1 = 0 := by
  obtain ⟨val, ne⟩ := p
  change val ≠ 1 at ne
  fin_cases val
  · rfl
  · exact absurd rfl ne

theorem chain2Switch_P'_eq (p r : chain2Switch.P') : p = r :=
  Subtype.ext ((chain2Switch_P'_val p).trans (chain2Switch_P'_val r).symm)

theorem chain2Switch_mem_I' (p : chain2Switch.P') : p ∈ chain2Switch.I' := by
  change p.1 ∈ ({0} : Set Chain2)
  exact chain2Switch_P'_val p

/-- A finset of the one-point type `P'` is empty or the singleton `{p}`. -/
theorem chain2Switch_finset (K : Finset chain2Switch.P') (p : chain2Switch.P') : K = ∅ ∨ K = {p} := by
  rcases K.eq_empty_or_nonempty with empty | ⟨member, inK⟩
  · exact Or.inl empty
  · exact Or.inr (Finset.eq_singleton_iff_unique_mem.mpr
      ⟨chain2Switch_P'_eq member p ▸ inK, fun other _ => chain2Switch_P'_eq other p⟩)

theorem chain2Switch_B : chain2Switch.B = {u | ∀ p, 0 ≤ u p ∧ u p ≤ 1} := by
  ext u
  constructor
  · rintro ⟨nonneg, -, -, -, chain_bound⟩ p
    refine ⟨nonneg p (chain2Switch_mem_I' p), ?_⟩
    have := chain_bound {p} (by simpa using chain2Switch_mem_I' p) (by simp [IsChainSet])
    simpa using this
  · intro bounds
    refine ⟨fun p _ => (bounds p).1, fun r notMem => (notMem (chain2Switch_mem_I' r)).elim,
      fun r _ notMem _ _ => (notMem (chain2Switch_mem_I' r)).elim,
      fun r notMem => (notMem (chain2Switch_mem_I' r)).elim, ?_⟩
    intro K _ _
    rcases K.eq_empty_or_nonempty with rfl | ⟨p, _⟩
    · simp
    · rcases chain2Switch_finset K p with rfl | rfl
      · simp
      · simpa using (bounds p).2

theorem chain2Switch_L (u : chain2Switch.P' → ℝ) (hu : u ∈ chain2Switch.B) (p : chain2Switch.P') :
    chain2Switch.L u = u p := by
  rw [chain2Switch_B] at hu
  apply le_antisymm
  · apply Finset.sup'_le
    intro K _
    rcases chain2Switch_finset K p with rfl | rfl
    · simpa [Switch.chainSum] using (hu p).1
    · simp [Switch.chainSum]
  · have singleton_low : ({p} : Finset chain2Switch.P') ∈ chain2Switch.lowBranches := by
      simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_singleton,
        Set.singleton_subset_iff, Finset.mem_singleton, forall_eq]
      refine ⟨chain2Switch_mem_I' p, by simp [IsChainSet], ?_⟩
      change p.1 < 1
      rw [chain2Switch_P'_val p]
      decide
    exact Finset.le_sup'_of_le _ singleton_low (by simp [Switch.chainSum])

theorem chain2Switch_U (u : chain2Switch.P' → ℝ) : chain2Switch.U u = 1 := by
  apply le_antisymm
  · exact Finset.inf'_le (fun branch => chain2Switch.upVal branch u)
      (show none ∈ chain2Switch.upBranches by simp [Switch.upBranches])
  · apply Finset.le_inf'
    intro branch member
    simp only [Switch.upBranches, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at member
    rcases member with rfl | ⟨r, above, rfl⟩
    · exact le_rfl
    · change (1 : Chain2) < r.1 at above
      rw [chain2Switch_P'_val r] at above
      exact absurd above (by decide)

theorem chainOrderPolytope_chain2_zero : chainOrderPolytope Chain2 {0} = orderPolytope Chain2 := by
  ext x
  constructor
  · rintro ⟨nonneg, bounds, -, below, -⟩
    have low : 0 ≤ x 0 := nonneg 0 rfl
    have high := bounds 1 (by simp)
    have order : x 0 ≤ x 1 := by
      simpa using below 1 (by simp) {0} (by simp) (by simp [IsChainSet]) (by simp)
    refine ⟨fun p => ?_, fun p r relation => ?_⟩
    · fin_cases p
      · exact ⟨low, order.trans high.2⟩
      · exact high
    · fin_cases p <;> fin_cases r
      · exact le_rfl
      · exact order
      · exact absurd relation (by decide)
      · exact le_rfl
  · rintro ⟨bounds, monotone⟩
    refine ⟨fun p _ => (bounds p).1, fun r _ => bounds r, fun r r' _ _ relation => monotone r r' relation,
      ?_, ?_⟩
    · intro r _ K subset _ _
      rcases Finset.subset_singleton_iff.mp (Finset.coe_subset_singleton.mp subset) with rfl | rfl
      · simpa using (bounds r).1
      · simpa using monotone 0 r (Fin.zero_le r)
    · intro K subset _
      rcases Finset.subset_singleton_iff.mp (Finset.coe_subset_singleton.mp subset) with rfl | rfl
      · simp
      · simpa using (bounds 0).2

theorem sec3_chain2_example_proved :
    ∃ s : Switch Chain2, s.I = {0} ∧ s.q = 1 ∧ s.B = {u | ∀ p, 0 ≤ u p ∧ u p ≤ 1} ∧
      (∀ u ∈ s.B, ∀ p, s.L u = u p ∧ s.U u = 1) ∧
      chainOrderPolytope Chain2 s.I = orderPolytope Chain2 ∧
      chainOrderPolytope Chain2 (insert s.q s.I) = chainPolytope Chain2 := by
  refine ⟨chain2Switch, rfl, rfl, chain2Switch_B,
    fun u hu p => ⟨chain2Switch_L u hu p, chain2Switch_U u⟩, chainOrderPolytope_chain2_zero, ?_⟩
  have whole : insert chain2Switch.q chain2Switch.I = Set.univ := by
    ext p
    change p = 1 ∨ p = 0 ↔ True
    fin_cases p <;> simp
  rw [whole, chainOrderPolytope_univ]

end HibiLi.Proofs
