/-
HibiLi/Proofs/Ex47.lean — proof of paper Example 4.7 (the switch of Section 4.2 on `P_6 = X` with a bottom adjoined).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.PaperDefs
import HibiLi.Proofs.Lemma44
import HibiLi.Proofs.SwitchFacts
import HibiLi.Polytope.Dimension

namespace HibiLi.Proofs

open HibiLi Polynomial Finset

namespace Ex47

/-- `<` on `X` is decidable (from the decidable `≤`), so `decide` settles finite statements about `WithBot X`. -/
local instance : DecidableLT XElem := decidableLTOfDecidableLE

/-- Above `c` sit exactly the incomparable `g, h`. -/
lemma not_chain_Ioi_c : ¬ IsChain (· ≤ ·) (Set.Ioi ((XElem.c : XElem) : WithBot XElem)) := by
  intro hch
  rcases hch (x := ((XElem.g : XElem) : WithBot XElem)) (y := ((XElem.h : XElem) : WithBot XElem))
    (by decide) (by decide) (by decide) with h | h <;> revert h <;> decide

/-- Above `g` or `h` there is nothing. -/
lemma chain_Ioi_above_c :
    ∀ r : WithBot XElem, ((XElem.c : XElem) : WithBot XElem) < r → IsChain (· ≤ ·) (Set.Ioi r) := by
  intro r hr
  have hempty : Set.Ioi r = ∅ := by
    ext z
    simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
    revert r z
    decide
  rw [hempty]
  exact IsChain.empty

/-- The switch of Example 4.7: the copy `a, b < c < g, h` of `X`, `q = c`, `g' = g`, `h' = h`. -/
def xs : XSwitch (WithBot XElem) where
  a := ((XElem.a : XElem) : WithBot XElem)
  b := ((XElem.b : XElem) : WithBot XElem)
  c := ((XElem.c : XElem) : WithBot XElem)
  g := ((XElem.g : XElem) : WithBot XElem)
  h := ((XElem.h : XElem) : WithBot XElem)
  isX := by unfold IsXCopy; decide
  q := ((XElem.c : XElem) : WithBot XElem)
  c_le_q := le_rfl
  q_not_chain := not_chain_Ioi_c
  q_max := chain_Ioi_above_c
  g' := ((XElem.g : XElem) : WithBot XElem)
  h' := ((XElem.h : XElem) : WithBot XElem)
  q_covby_g' := by unfold CovBy; decide
  q_covby_h' := by unfold CovBy; decide
  g'_ne_h' := by decide
  g'_h'_incomp := by decide

/-- `I = P \ ↑c = {⊥, a, b}`. -/
lemma I_eq : xs.toSwitch.I =
    {⊥, ((XElem.a : XElem) : WithBot XElem), ((XElem.b : XElem) : WithBot XElem)} := by
  ext z
  show ¬ ((XElem.c : XElem) : WithBot XElem) ≤ z ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert z
  decide

lemma mem_I_iff (z : WithBot XElem) : z ∈ xs.toSwitch.I ↔
    z = ⊥ ∨ z = ((XElem.a : XElem) : WithBot XElem) ∨ z = ((XElem.b : XElem) : WithBot XElem) := by
  rw [I_eq]; rfl

/-- Every coordinate of `I` is `⊥`, `a` or `b`, as an element of `P'`. -/
lemma eq_of_mem_I {p p0 : xs.toSwitch.P'} (hp0 : p0.1 = ⊥) (hp : p.1 ∈ xs.toSwitch.I) :
    p = p0 ∨ p = xs.pa ∨ p = xs.pb := by
  rcases (mem_I_iff p.1).1 hp with h | h | h
  · exact Or.inl (Subtype.ext (h.trans hp0.symm))
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

/-- The only elements of `P` above `c` are `g, h`. -/
lemma eq_of_c_lt : ∀ z : WithBot XElem, ((XElem.c : XElem) : WithBot XElem) < z →
    z = ((XElem.g : XElem) : WithBot XElem) ∨ z = ((XElem.h : XElem) : WithBot XElem) := by
  decide

/-- Elements of `J = P \ I` other than `g, h` are `c` itself. -/
lemma eq_c_of_c_le : ∀ z : WithBot XElem, ((XElem.c : XElem) : WithBot XElem) ≤ z →
    z ≠ ((XElem.g : XElem) : WithBot XElem) → z ≠ ((XElem.h : XElem) : WithBot XElem) →
    z = ((XElem.c : XElem) : WithBot XElem) := by
  decide

lemma bot_mem_I {p0 : xs.toSwitch.P'} (hp0 : p0.1 = ⊥) : p0.1 ∈ xs.toSwitch.I := by
  rw [hp0, mem_I_iff]; exact Or.inl rfl

lemma ab_mem_I {p : xs.toSwitch.P'} (hp : p = xs.pa ∨ p = xs.pb) : p.1 ∈ xs.toSwitch.I := by
  rw [mem_I_iff]; rcases hp with rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- The chains `{⊥, a}` and `{⊥, b}` are branches of `L`. -/
lemma pair_mem_lowBranches {p0 p : xs.toSwitch.P'} (hp0 : p0.1 = ⊥) (hp : p = xs.pa ∨ p = xs.pb) :
    ({p0, p} : Finset xs.toSwitch.P') ∈ xs.toSwitch.lowBranches := by
  classical
  have hpq : p.1 < xs.q := by rcases hp with rfl | rfl <;> decide
  have h0q : p0.1 < xs.q := by rw [hp0]; exact WithBot.bot_lt_coe _
  simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_pair,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  refine ⟨Set.pair_subset (bot_mem_I hp0) (ab_mem_I hp), ?_, h0q, hpq⟩
  show IsChain (· ≤ ·) (({p0, p} : Finset xs.toSwitch.P') : Set xs.toSwitch.P')
  rw [Finset.coe_pair]
  exact IsChain.pair (show p0 ≤ p from show p0.1 ≤ p.1 by rw [hp0]; exact bot_le)

lemma chainSum_pair (u : xs.toSwitch.P' → ℝ) {p0 p : xs.toSwitch.P'} (hp0 : p0.1 = ⊥)
    (hp : p = xs.pa ∨ p = xs.pb) : xs.toSwitch.chainSum {p0, p} u = u p0 + u p :=
  Finset.sum_pair fun h => by
    rcases hp with rfl | rfl <;> exact absurd (congrArg Subtype.val h) (by rw [hp0]; decide)

/-- A branch of `L` contained in `{⊥, p}` sums to at most `x_⊥ + x_p` (nonnegativity on `I`). -/
lemma chainSum_le_pair {u : xs.toSwitch.P' → ℝ} (hu : u ∈ xs.toSwitch.B) {p0 p : xs.toSwitch.P'}
    (hp0 : p0.1 = ⊥) (hp : p = xs.pa ∨ p = xs.pb) {K : Finset xs.toSwitch.P'} (hK : K ⊆ {p0, p}) :
    xs.toSwitch.chainSum K u ≤ u p0 + u p := by
  calc xs.toSwitch.chainSum K u ≤ ∑ i ∈ {p0, p}, u i :=
        Finset.sum_le_sum_of_subset_of_nonneg hK fun i hi _ => by
          rcases Finset.mem_insert.1 hi with rfl | hi
          · exact hu.1 _ (bot_mem_I hp0)
          · rw [Finset.mem_singleton.1 hi]; exact hu.1 _ (ab_mem_I hp)
    _ = u p0 + u p := chainSum_pair u hp0 hp

/-- Every branch of `L` lies in `{⊥, a}` or in `{⊥, b}` (`a, b` are incomparable). -/
lemma subset_pair {p0 : xs.toSwitch.P'} (hp0 : p0.1 = ⊥) {K : Finset xs.toSwitch.P'}
    (hK : K ∈ xs.toSwitch.lowBranches) : K ⊆ {p0, xs.pa} ∨ K ⊆ {p0, xs.pb} := by
  classical
  simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hK
  obtain ⟨hKI, hKc, -⟩ := hK
  have hmem : ∀ p ∈ K, p = p0 ∨ p = xs.pa ∨ p = xs.pb := fun p hp => eq_of_mem_I hp0 (hKI hp)
  by_cases hb : xs.pb ∈ K
  · refine Or.inr fun p hp => ?_
    rcases hmem p hp with rfl | rfl | rfl
    · simp
    · rcases hKc hp hb (by decide) with h | h
      · exact absurd (show xs.pa.1 ≤ xs.pb.1 from h) (by decide)
      · exact absurd (show xs.pb.1 ≤ xs.pa.1 from h) (by decide)
    · simp
  · refine Or.inl fun p hp => ?_
    rcases hmem p hp with rfl | rfl | rfl
    · simp
    · simp
    · exact absurd hp hb

/-- `L = max(α, β) + x_⊥` on `B`. -/
lemma L_eq {u : xs.toSwitch.P' → ℝ} (hu : u ∈ xs.toSwitch.B) {p0 : xs.toSwitch.P'} (hp0 : p0.1 = ⊥) :
    xs.toSwitch.L u = max (u xs.pa) (u xs.pb) + u p0 := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun K hK => ?_
    rcases subset_pair hp0 hK with h | h
    · linarith [chainSum_le_pair hu hp0 (Or.inl rfl) h, le_max_left (u xs.pa) (u xs.pb)]
    · linarith [chainSum_le_pair hu hp0 (Or.inr rfl) h, le_max_right (u xs.pa) (u xs.pb)]
  · have hval : ∀ {p}, (p = xs.pa ∨ p = xs.pb) → u p0 + u p ≤ xs.toSwitch.L u := fun hp =>
      (chainSum_pair u hp0 hp).symm.le.trans
        (Finset.le_sup' (fun K => xs.toSwitch.chainSum K u) (pair_mem_lowBranches hp0 hp))
    rcases le_total (u xs.pa) (u xs.pb) with h | h
    · rw [max_eq_right h]; linarith [hval (Or.inr rfl)]
    · rw [max_eq_left h]; linarith [hval (Or.inl rfl)]

/-- `U = min(γ, η)` on `B`: the branches of `U` are `1`, `y_g`, `y_h`, and `y_g ≤ 1`. -/
lemma U_eq {u : xs.toSwitch.P' → ℝ} (hu : u ∈ xs.toSwitch.B) : xs.toSwitch.U u = min (u xs.pg) (u xs.ph) := by
  classical
  have hmem : ∀ {r : xs.toSwitch.P'}, xs.q < r.1 → some r ∈ xs.toSwitch.upBranches := fun hr => by
    simp only [Switch.upBranches, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact Or.inr ⟨_, hr, rfl⟩
  apply le_antisymm
  · exact le_min (Finset.inf'_le (fun j => xs.toSwitch.upVal j u) (hmem (r := xs.pg) (by decide)))
      (Finset.inf'_le (fun j => xs.toSwitch.upVal j u) (hmem (r := xs.ph) (by decide)))
  · refine Finset.le_inf' _ _ fun j hj => ?_
    simp only [Switch.upBranches, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hj
    rcases hj with rfl | ⟨r, hr, rfl⟩
    · exact (min_le_left _ _).trans (hu.2.1 xs.pg (show xs.pg.1 ∉ xs.toSwitch.I by rw [mem_I_iff]; decide)).2
    · rcases eq_of_c_lt r.1 hr with h | h
      · rw [show r = xs.pg from Subtype.ext h]; exact min_le_left _ _
      · rw [show r = xs.ph from Subtype.ext h]; exact min_le_right _ _

/-- `E₀ = {u ∈ B : x_⊥ = 0}`. -/
lemma E0_eq_bot : xs.E0 = {u | u ∈ xs.toSwitch.B ∧ ∀ p0 : xs.toSwitch.P', p0.1 = ⊥ → u p0 = 0} := by
  ext u
  constructor
  · rintro ⟨hB, hz, -⟩
    exact ⟨hB, fun p0 hp0 => hz p0 (bot_mem_I hp0) (by rw [hp0]; decide) (by rw [hp0]; decide)⟩
  · rintro ⟨hB, h0⟩
    refine ⟨hB, fun p hp ha hb => h0 p ?_, fun r hr hg hh => absurd (eq_c_of_c_le r.1 (not_not.mp hr) hg hh) r.2⟩
    rcases (mem_I_iff p.1).1 hp with h | h | h
    · exact h
    · exact absurd h ha
    · exact absurd h hb

/-- `dim E₀ + 1 = dim B` (`4 + 1 = 5 = |P'|`). -/
lemma adim_E0_succ : adim xs.E0 + 1 = adim xs.toSwitch.B := by
  rw [(lemma_4_4_proved xs xs.pa xs.pb xs.pg xs.ph rfl rfl rfl rfl).2.1, Switch.B,
    chainOrderPolytope_adim, card_P']
  rfl

end Ex47

open Ex47 in
/-- **Example 4.7** (paper lines 612–620), given Proposition 5.2 for `n = 6` (the last conjunct). -/
theorem ex_4_7_of
    (h52 : facePoly (chainPolytope (WithBot XElem)) - facePoly (orderPolytope (WithBot XElem)) = gapPoly 6) :
    ¬ IsChain (· ≤ ·) (Set.Ioi ((XElem.c : XElem) : WithBot XElem)) ∧
    (∀ r : WithBot XElem, ((XElem.c : XElem) : WithBot XElem) < r → IsChain (· ≤ ·) (Set.Ioi r)) ∧
    (∃ x : XSwitch (WithBot XElem), x.q = ((XElem.c : XElem) : WithBot XElem) ∧
      x.toSwitch.I = {⊥, ((XElem.a : XElem) : WithBot XElem), ((XElem.b : XElem) : WithBot XElem)} ∧
      (∀ u ∈ x.toSwitch.B, ∀ p0 : x.toSwitch.P', p0.1 = ⊥ →
        x.toSwitch.L u = max (u x.pa) (u x.pb) + u p0 ∧ x.toSwitch.U u = min (u x.pg) (u x.ph)) ∧
      x.E0 = {u | u ∈ x.toSwitch.B ∧ ∀ p0 : x.toSwitch.P', p0.1 = ⊥ → u p0 = 0} ∧
      adim x.E0 + 1 = adim x.toSwitch.B) ∧
    (X ^ 2 * (1 + X) ^ 2 + X ^ 3 * (1 + X) ^ 2 : ℤ[X]) = X ^ 2 * (1 + X) ^ 3 ∧
    facePoly (chainPolytope (WithBot XElem)) - facePoly (orderPolytope (WithBot XElem)) = gapPoly 6 :=
  ⟨not_chain_Ioi_c, chain_Ioi_above_c,
    ⟨xs, rfl, I_eq, fun _ hu _ hp0 => ⟨L_eq hu hp0, U_eq hu⟩, E0_eq_bot, adim_E0_succ⟩, by ring, h52⟩
