/-
HibiLi/Proofs/OrderTheory.lean — the order-theoretic part of Section 4.2: existence of `q` and Lemma 4.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib

namespace HibiLi.Proofs

variable {P : Type*} [Fintype P] [PartialOrder P]

omit [Fintype P] in
/-- Two incomparable elements strictly above `r` exist iff `Ioi r` is not a chain. -/
lemma not_isChain_Ioi_iff {r : P} :
    ¬ IsChain (· ≤ ·) (Set.Ioi r) ↔ ∃ x y, r < x ∧ r < y ∧ ¬ x ≤ y ∧ ¬ y ≤ x := by
  constructor
  · intro h
    simp only [IsChain, Set.Pairwise, not_forall, exists_prop] at h
    obtain ⟨x, hx, y, hy, hxy, hc⟩ := h
    exact ⟨x, y, hx, hy, fun h' => hc (Or.inl h'), fun h' => hc (Or.inr h')⟩
  · rintro ⟨x, y, hx, hy, hxy, hyx⟩ hch
    rcases hch.total hx hy with h | h
    · exact hxy h
    · exact hyx h

/-- In a finite poset, below any `x > q` there is an upper cover of `q`. -/
lemma exists_covBy_le_of_lt {q x : P} (h : q < x) : ∃ g, q ⋖ g ∧ g ≤ x := by
  classical
  let S : Finset P := Finset.univ.filter (fun z => q < z ∧ z ≤ x)
  have hS : S.Nonempty := ⟨x, by simp [S, h]⟩
  obtain ⟨g, hgS, hmin⟩ := S.exists_minimal hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hgS
  refine ⟨g, ⟨hgS.1, fun z hqz hzg => ?_⟩, hgS.2⟩
  have hzS : z ∈ S := by simp [S, hqz, le_trans hzg.le hgS.2]
  exact hzg.not_ge (hmin hzS hzg.le)

/-- Paper lines 679–681: a `q ≥ c`, maximal among the elements whose strict upper set is not a chain, exists. -/
theorem q_exists {c g h : P} (hcg : c < g) (hch : c < h) (hgh : ¬ g ≤ h) (hhg : ¬ h ≤ g) :
    ∃ q, c ≤ q ∧ ¬ IsChain (· ≤ ·) (Set.Ioi q) ∧ ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r) := by
  classical
  let M : Finset P := Finset.univ.filter (fun r => c ≤ r ∧ ¬ IsChain (· ≤ ·) (Set.Ioi r))
  have hcM : c ∈ M := by
    simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, le_refl]
    exact not_isChain_Ioi_iff.mpr ⟨g, h, hcg, hch, hgh, hhg⟩
  obtain ⟨q, hqM, hmax⟩ := M.exists_maximal ⟨c, hcM⟩
  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and] at hqM
  refine ⟨q, hqM.1, hqM.2, fun r hqr => by_contra fun hr => ?_⟩
  have hrM : r ∈ M := by simp [M, le_trans hqM.1 hqr.le, hr]
  exact hqr.not_ge (hmax hrM hqr.le)

/-- **Lemma 4.3.** -/
theorem lemma_4_3 {a b c q : P} (hac : a < c) (hbc : b < c) (hcq : c ≤ q)
    (hq : ¬ IsChain (· ≤ ·) (Set.Ioi q)) (hmax : ∀ r, q < r → IsChain (· ≤ ·) (Set.Ioi r)) :
    (∃ g' h', q ⋖ g' ∧ q ⋖ h' ∧ g' ≠ h' ∧ ¬ g' ≤ h' ∧ ¬ h' ≤ g') ∧
    IsLowerSet (Set.Ici q)ᶜ ∧ (∀ p, p < q → p ∈ (Set.Ici q)ᶜ) ∧
    a ∈ (Set.Ici q)ᶜ ∧ b ∈ (Set.Ici q)ᶜ ∧ a < q ∧ b < q := by
  obtain ⟨x, y, hqx, hqy, hxy, hyx⟩ := not_isChain_Ioi_iff.mp hq
  obtain ⟨g', hg', hg'x⟩ := exists_covBy_le_of_lt hqx
  obtain ⟨h', hh', hh'y⟩ := exists_covBy_le_of_lt hqy
  -- the two covers differ: a common cover would have the incomparable pair strictly above it
  have hne : g' ≠ h' := by
    rintro rfl
    have hgx : g' < x := lt_of_le_of_ne hg'x (by rintro rfl; exact hxy hh'y)
    have hgy : g' < y := lt_of_le_of_ne hh'y (by rintro rfl; exact hyx hg'x)
    exact not_isChain_Ioi_iff.mpr ⟨x, y, hgx, hgy, hxy, hyx⟩ (hmax g' hg'.lt)
  -- two distinct upper covers of `q` are incomparable
  have hinc : ∀ {u v : P}, q ⋖ u → q ⋖ v → u ≠ v → ¬ u ≤ v := fun hu hv huv hle =>
    huv (eq_of_le_of_not_lt hle fun hlt => hv.2 hu.lt hlt)
  have haq : a < q := lt_of_lt_of_le hac hcq
  have hbq : b < q := lt_of_lt_of_le hbc hcq
  refine ⟨⟨g', h', hg', hh', hne, hinc hg' hh' hne, hinc hh' hg' (Ne.symm hne)⟩, ?_, ?_, ?_, ?_, haq, hbq⟩
  · intro u v hvu hu hqv
    exact hu (le_trans hqv hvu)
  · intro p hp hqp
    exact absurd (lt_of_lt_of_le hp hqp) (lt_irrefl _)
  · intro hqa
    exact absurd (lt_of_le_of_lt hqa haq) (lt_irrefl _)
  · intro hqb
    exact absurd (lt_of_le_of_lt hqb hbq) (lt_irrefl _)

end HibiLi.Proofs
