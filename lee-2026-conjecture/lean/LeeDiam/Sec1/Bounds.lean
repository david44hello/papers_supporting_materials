/-
LeeDiam/Sec1/Bounds.lean — general facts on the two diameters used by Section 1 (l. 61) and Section 7 (l. 225): two
incomparable elements force both diameters `≥ 2`; the empty poset; a nonempty chain has `diam C = 1`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.
-/
import LeeDiam.Bridge.Graphs
import LeeDiam.Sec4.BandOrder

namespace LeeDiam.S1

variable {P : Type} [Fintype P] [PartialOrder P]

/-- An extended natural that is neither `0` nor `1` is at least `2`. -/
theorem two_le_of_ne {x : ℕ∞} (h0 : x ≠ 0) (h1 : x ≠ 1) : 2 ≤ x := by
  have h1le : 1 ≤ x := Order.one_le_iff_ne_zero.2 h0
  have hlt : 1 < x := lt_of_le_of_ne h1le (Ne.symm h1)
  have h2 := (ENat.add_one_le_iff (ENat.natCast_ne_top 1)).2 (by exact_mod_cast hlt)
  norm_num at h2
  exact h2

/-- Two incomparable elements give `diam O(P) ≥ 2`: the ideals `↓p`, `↓q` are not nested. -/
theorem two_le_orderDiam {p q : P} (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) : 2 ≤ orderDiam P := by
  have hI : IsIdeal {x : P | x ≤ p} := fun _ _ hba ha => hba.trans ha
  have hJ : IsIdeal {x : P | x ≤ q} := fun _ _ hba ha => hba.trans ha
  rw [orderDiam_eq]
  refine le_trans (two_le_of_ne ?_ ?_) ((idealGraph P).edist_le_ediam (u := ⟨_, hI⟩) (v := ⟨_, hJ⟩))
  · rw [Ne, SimpleGraph.edist_eq_zero_iff]
    intro h
    have hIJ : {x : P | x ≤ p} = {x : P | x ≤ q} := congrArg Subtype.val h
    have hp : p ∈ ({x : P | x ≤ q}) := by
      rw [← hIJ]
      exact le_refl p
    exact hpq hp
  · rw [Ne, SimpleGraph.edist_eq_one_iff_adj]
    rintro (⟨hsub, -⟩ | ⟨hsub, -⟩)
    · exact hpq (hsub (le_refl p))
    · exact hqp (hsub (le_refl q))

omit [Fintype P] in
theorem isAntichainSet_singleton' (x : P) : IsAntichainSet ({x} : Set P) :=
  fun _ hu _ hv hne _ => hne (hu.trans hv.symm)

/-- Two incomparable elements give `diam C(P) ≥ 2`: `{p} △ {q} = {p, q}` is not connected. -/
theorem two_le_chainDiam {p q : P} (hpq : ¬ p ≤ q) (hqp : ¬ q ≤ p) : 2 ≤ chainDiam P := by
  have hne : p ≠ q := fun e => hpq (e ▸ le_refl p)
  rw [chainDiam_eq]
  refine le_trans (two_le_of_ne ?_ ?_) ((antichainGraph P).edist_le_ediam
    (u := ⟨_, isAntichainSet_singleton' p⟩) (v := ⟨_, isAntichainSet_singleton' q⟩))
  · rw [Ne, SimpleGraph.edist_eq_zero_iff]
    intro h
    have hIJ : ({p} : Set P) = {q} := congrArg Subtype.val h
    have hp : p ∈ ({q} : Set P) := by
      rw [← hIJ]
      exact Set.mem_singleton p
    exact hne hp
  · rw [Ne, SimpleGraph.edist_eq_one_iff_adj]
    intro hconn
    have hpG : p ∈ symmDiff ({p} : Set P) {q} := Set.mem_symmDiff.2 (Or.inl ⟨rfl, hne⟩)
    have hqG : q ∈ symmDiff ({p} : Set P) {q} := Set.mem_symmDiff.2 (Or.inr ⟨rfl, Ne.symm hne⟩)
    obtain ⟨u, hu, v, hv, rfl, hvu, huv⟩ := S4.isConnSet_cross hconn (fun x => x = p) hpG hqG rfl (Ne.symm hne)
    have hvq : v = q := by
      rcases Set.mem_symmDiff.1 hv with ⟨hv1, -⟩ | ⟨hv1, -⟩
      · exact absurd hv1 hvu
      · exact hv1
    subst hvq
    rcases huv with h | h
    exacts [hpq h.le, hqp h.le]

/-- The empty poset: both diameters are `0`. -/
theorem diam_empty (hP : IsEmpty P) : orderDiam P = 0 ∧ chainDiam P = 0 := by
  constructor
  · refine le_antisymm ((orderDiam_le_iff 0).2 fun I J hI hJ => ?_) zero_le
    have hIJ : I = J := by rw [Set.eq_empty_of_isEmpty I, Set.eq_empty_of_isEmpty J]
    subst hIJ
    rw [dO_eq, SimpleGraph.edist_self]
  · refine le_antisymm ((chainDiam_le_iff 0).2 fun A B hA hB => ?_) zero_le
    have hAB : A = B := by rw [Set.eq_empty_of_isEmpty A, Set.eq_empty_of_isEmpty B]
    subst hAB
    rw [dC_eq, SimpleGraph.edist_self]

/-- A nonempty poset has `diam C(P) ≥ 1`: `∅ ≠ {x}`. -/
theorem one_le_chainDiam (hP : Nonempty P) : 1 ≤ chainDiam P := by
  obtain ⟨x⟩ := hP
  have hemp : IsAntichainSet (∅ : Set P) := fun _ h => absurd h (Set.notMem_empty _)
  rw [chainDiam_eq]
  refine le_trans ?_ ((antichainGraph P).edist_le_ediam (u := ⟨∅, hemp⟩) (v := ⟨_, isAntichainSet_singleton' x⟩))
  refine Order.one_le_iff_ne_zero.2 ?_
  rw [Ne, SimpleGraph.edist_eq_zero_iff]
  intro h
  have hIJ : (∅ : Set P) = {x} := congrArg Subtype.val h
  have hx : x ∈ (∅ : Set P) := by
    rw [hIJ]
    exact Set.mem_singleton x
  exact Set.notMem_empty x hx

omit [Fintype P] in
/-- A set of pairwise comparable elements is connected (if nonempty). -/
theorem isConnSet_of_chain {D : Set P} {x0 : P} (hx0 : x0 ∈ D)
    (hD : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Comp x y) : IsConnSet D :=
  S4.isConnSet_of_rtg hx0 fun y hy => by
    by_cases hyx : x0 = y
    · rw [hyx]
    · exact Relation.ReflTransGen.single ⟨hx0, hy, hD x0 hx0 y hy hyx⟩

/-- A nonempty chain has `diam C(P) = 1`: its antichains are `∅` and the singletons, and any two of them are adjacent. -/
theorem chainDiam_chain (hP : Nonempty P) (hc : IsChain (· ≤ ·) (Set.univ : Set P)) : chainDiam P = 1 := by
  have hcomp : ∀ x y : P, x ≠ y → Comp x y := fun x y hxy => by
    rcases hc (Set.mem_univ x) (Set.mem_univ y) hxy with h | h
    exacts [Or.inl (lt_of_le_of_ne h hxy), Or.inr (lt_of_le_of_ne h (Ne.symm hxy))]
  refine le_antisymm ((chainDiam_le_iff 1).2 fun A B hA hB => ?_) (one_le_chainDiam hP)
  by_cases hAB : A = B
  · subst hAB
    rw [dC_eq, SimpleGraph.edist_self]
    exact zero_le
  · obtain ⟨x0, hx0⟩ : (symmDiff A B).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty, ← Set.bot_eq_empty, symmDiff_eq_bot] at hcon
      exact hAB hcon
    rw [dC_eq]
    exact le_of_eq ((SimpleGraph.edist_eq_one_iff_adj).2
      (isConnSet_of_chain hx0 fun x _ y _ hxy => hcomp x y hxy))

/-- A nonempty poset with `diam O(P) ≤ 1` is a chain (two incomparable elements would give `diam O(P) ≥ 2`). -/
theorem chain_of_orderDiam_le_one (h : orderDiam P ≤ 1) : IsChain (· ≤ ·) (Set.univ : Set P) := by
  intro x _ y _ hxy
  by_contra hcon
  push Not at hcon
  have h2 := two_le_orderDiam hcon.1 hcon.2
  exact absurd (h2.trans h) (by norm_num)

end LeeDiam.S1
