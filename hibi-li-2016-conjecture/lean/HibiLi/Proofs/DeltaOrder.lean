/- Degenerate checks: empty I and final prefix are allowed;
the inserted chain may start empty; kappa=0 gives the vertex itself. -/
import HibiLi.Proofs.LinExtRows
import HibiLi.Proofs.StepRows
import HibiLi.Proofs.CoverageTail

namespace HibiLi.Proofs

/-- l.879-881: any concatenation of extensions of I, then q, then J' is a linear extension. -/
theorem sec4_linext_concat {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)
    (e : Fin (Fintype.card P) ≃ P)
    (hI : ∀ i, e i ∈ s.I ↔ (i : ℕ) < s.I.ncard)
    (hq : (e.symm s.q : ℕ) = s.I.ncard)
    (heI : ∀ i j, e i ∈ s.I → e j ∈ s.I → e i < e j → i < j)
    (heJ : ∀ i j, e i ∉ s.I → e j ∉ s.I → e i ≠ s.q → e j ≠ s.q → e i < e j → i < j) :
    ∀ i j, e i < e j → i < j := by
  intro i j hij
  by_cases hj : e j ∈ s.I
  · exact heI i j (s.isLowerSet hij.le hj) hj hij
  · by_cases hi : e i ∈ s.I
    · have := (hI i).mp hi
      have := mt (hI j).mpr hj
      exact Fin.lt_def.mpr (by omega)
    · by_cases hiq : e i = s.q
      · have hieq : i = e.symm s.q := by simpa using congrArg e.symm hiq
        have hjne : j ≠ e.symm s.q := fun h => hij.ne (by simp [h, hiq])
        have hjge := mt (hI j).mpr hj
        have hjvalne : (j : ℕ) ≠ (e.symm s.q : ℕ) := fun h => hjne (Fin.ext h)
        rw [hieq]
        exact Fin.lt_def.mpr (by omega)
      · have hjq : e j ≠ s.q := fun h => hi (s.q_minimal (e i) (h ▸ hij))
        exact heJ i j hi hj hiq hjq hij

open Classical in
/-- l.336-337: q is maximal in I union {q}, and adjoining it to every eligible chain gives such a chain. -/
theorem sec3_chains_through_q_converse {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P) :
    (∀ p ∈ insert s.q s.I, ¬ s.q < p) ∧
    ∀ K : Finset P, ↑K ⊆ s.I → IsChainSet P K → (∀ p ∈ K, p < s.q) →
      IsChainSet P (insert s.q K) ∧ ↑(insert s.q K) ⊆ insert s.q s.I := by
  classical
  refine ⟨?_, ?_⟩
  · rintro p (rfl | hp) hlt
    · exact lt_irrefl _ hlt
    · exact s.q_notMem (s.isLowerSet hlt.le hp)
  · intro K hKI hchain hbelow
    constructor
    · intro p hp r hr hne
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rcases Finset.mem_insert.mp hr with rfl | hr
        · exact (hne rfl).elim
        · exact Or.inr (hbelow r hr).le
      · rcases Finset.mem_insert.mp hr with rfl | hr
        · exact Or.inl (hbelow p hp).le
        · exact hchain hp hr hne
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (hKI hp)

/-- l.879-883,982-985: every prefix is an order ideal, including the full prefix. -/
theorem sec4_linext_prefix_isLowerSet {P : Type*} [Fintype P] [PartialOrder P]
    (e : Fin (Fintype.card P) ≃ P) (he : ∀ i j, e i < e j → i < j) (j : ℕ) :
    IsLowerSet {p | (e.symm p : ℕ) < j} := by
  intro a b hba ha
  rcases hba.lt_or_eq with h | rfl
  · have hij := he (e.symm b) (e.symm a) (by simpa using h)
    exact lt_trans (Fin.lt_def.mp hij) ha
  · exact ha

/-- l.852-855: the facet and vertex bounds hold also for kappa=0. -/
theorem lemma_4_7_facet_counts_all {ι : Type*} [Fintype ι] (Q D : Set (ι → ℝ))
    (hQ : IsPolytope Q) (hD : IsFace Q D) (facet : adim D + 1 = adim Q)
    (v : ι → ℝ) (hv : IsFace Q {v}) (κ : ℕ) :
    Nat.choose (adim Q) (κ + 1) ≤ {F | IsFace Q F ∧ adim F = κ ∧ F ⊆ D}.ncard ∧
    Nat.choose (adim Q) κ ≤ {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F}.ncard := by
  refine ⟨(lemma_4_7_facet_counts Q D hQ hD facet v hv κ).1, ?_⟩
  by_cases below : κ ≤ adim Q
  · have lower := lemma_4_8_proved Q hQ {v} hv κ (by simpa [adim_singleton] using below)
    have same : {G | IsFace Q G ∧ {v} ⊆ G ∧ adim G = adim ({v} : Set (ι → ℝ)) + κ} =
        {F | IsFace Q F ∧ adim F = κ ∧ v ∈ F} := by
      ext F
      simp only [Set.mem_ofPred_eq, Set.singleton_subset_iff, adim_singleton, zero_add]
      tauto
    rw [same] at lower
    simpa only [adim_singleton, Nat.sub_zero] using lower
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

end HibiLi.Proofs

#print axioms HibiLi.Proofs.sec4_linext_concat
#print axioms HibiLi.Proofs.sec3_chains_through_q_converse
#print axioms HibiLi.Proofs.sec4_linext_prefix_isLowerSet
#print axioms HibiLi.Proofs.lemma_4_7_facet_counts_all
