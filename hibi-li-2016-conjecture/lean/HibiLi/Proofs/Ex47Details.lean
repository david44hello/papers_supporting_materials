/-
HibiLi/Proofs/Ex47Details.lean — the details of paper Example 4.7: ζ = (x_⊥), ζ(u₀) = 0, λ_a = λ_b = x_⊥ on B, and
the bounds δ_{E₀} ≥ t²(1+t)², δ_B ≥ t³(1+t)² from Lemma 4.2 at the crossing points of Lemma 4.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Proofs.Ex47
import HibiLi.Proofs.Lemma36
import HibiLi.Proofs.Lemma46

namespace HibiLi.Proofs

open HibiLi Polynomial Finset

namespace Ex47Details

/-- `<` on `X` is decidable (from the decidable `≤`), so `decide` settles finite statements about `WithBot X`. -/
local instance : DecidableLT XElem := decidableLTOfDecidableLE

/-- The six elements of `WithBot X`. -/
lemma cover : ∀ z : WithBot XElem, z = ⊥ ∨ z = ((XElem.c : XElem) : WithBot XElem) ∨
    (z = ((XElem.a : XElem) : WithBot XElem) ∨ z = ((XElem.b : XElem) : WithBot XElem)) ∨
    (z = ((XElem.g : XElem) : WithBot XElem) ∨ z = ((XElem.h : XElem) : WithBot XElem)) := by
  decide

/-- Two incomparable elements below `c` are `a, b` (in some order). -/
lemma ab_cover : ∀ a b : WithBot XElem, a < ((XElem.c : XElem) : WithBot XElem) →
    b < ((XElem.c : XElem) : WithBot XElem) → ¬ a ≤ b → ¬ b ≤ a →
    ∀ z, (z = ((XElem.a : XElem) : WithBot XElem) ∨ z = ((XElem.b : XElem) : WithBot XElem)) → z = a ∨ z = b := by
  decide

/-- Two distinct elements above `c` are `g, h` (in some order). -/
lemma gh_cover : ∀ g h : WithBot XElem, ((XElem.c : XElem) : WithBot XElem) < g →
    ((XElem.c : XElem) : WithBot XElem) < h → g ≠ h →
    ∀ z, (z = ((XElem.g : XElem) : WithBot XElem) ∨ z = ((XElem.h : XElem) : WithBot XElem)) → z = g ∨ z = h := by
  decide

/-- `Finset.mem_erase` for any `DecidableEq` instance (Lemma 4.6's forms use the classical one). -/
lemma mem_erase_iff {α : Type*} (inst : DecidableEq α) {s : Finset α} {a b : α} :
    b ∈ @Finset.erase α inst s a ↔ b ≠ a ∧ b ∈ s :=
  Finset.mem_erase

variable (x : XSwitch (WithBot XElem)) (hq : x.q = ((XElem.c : XElem) : WithBot XElem))
include hq

/-- The only non-special coordinate of `P'` is `⊥`. -/
lemma eq_bot_of_not_special {p : x.toSwitch.P'} (hs : p ∉ x.special) : p.1 = ⊥ := by
  obtain ⟨ha, hb, hg, hh⟩ := (Lemma45.not_special x).mp hs
  have hab := ab_cover x.a x.b (hq ▸ x.a_lt_q) (hq ▸ x.b_lt_q) x.isX.2.2.2.2.1 x.isX.2.2.2.2.2.1 p.1
  have hgh := gh_cover x.g' x.h' (hq ▸ x.q_covby_g'.lt) (hq ▸ x.q_covby_h'.lt) x.g'_ne_h' p.1
  rcases cover p.1 with h | h | h | h
  · exact h
  · exact absurd (h.trans hq.symm) p.2
  · rcases hab h with e | e
    · exact absurd (Subtype.ext e) ha
    · exact absurd (Subtype.ext e) hb
  · rcases hgh h with e | e
    · exact absurd (Subtype.ext e) hg
    · exact absurd (Subtype.ext e) hh

omit hq in
/-- `⊥ ∈ I`: the coordinate `⊥` of `P'` is a chain coordinate. -/
lemma bot_mem_I {p0 : x.toSwitch.P'} (hp0 : p0.1 = ⊥) : p0.1 ∈ x.toSwitch.I :=
  fun hle => p0.2 (le_antisymm (by rw [hp0]; exact bot_le) hle)

omit hq in
/-- `{⊥, c}` (`c ∈ {a, b}`) is a branch of `L`. -/
lemma pair_mem_lowBranches {p0 pc : x.toSwitch.P'} (hp0 : p0.1 = ⊥) (hpc : pc = x.pa ∨ pc = x.pb) :
    ({p0, pc} : Finset x.toSwitch.P') ∈ x.toSwitch.lowBranches := by
  have hcq : pc.1 < x.q := by rcases hpc with rfl | rfl; exacts [x.a_lt_q, x.b_lt_q]
  have h0q : p0.1 < x.q := lt_of_le_of_ne (by rw [hp0]; exact bot_le) p0.2
  simp only [Switch.lowBranches, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_pair,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  refine ⟨Set.pair_subset (bot_mem_I x hp0) (fun hle => (not_le_of_gt hcq) hle), ?_, h0q, hcq⟩
  show IsChain (· ≤ ·) (({p0, pc} : Finset x.toSwitch.P') : Set x.toSwitch.P')
  rw [Finset.coe_pair]
  exact IsChain.pair (show p0 ≤ pc from show p0.1 ≤ pc.1 by rw [hp0]; exact bot_le)

/-- `λ = x_⊥` on `B` for the `c`-family, `c ∈ {a, b}`: its forms are `0` and `x_⊥`. -/
lemma family_eq {lam : (x.toSwitch.P' → ℝ) → ℝ} {pc : x.toSwitch.P'} (hF : Lemma46.Family x lam pc)
    (hpc : pc = x.pa ∨ pc = x.pb) {u : x.toSwitch.P' → ℝ} (hu : u ∈ x.toSwitch.B) {p0 : x.toSwitch.P'}
    (hp0 : p0.1 = ⊥) : lam u = u p0 := by
  have hne : p0 ≠ pc := by
    rintro rfl
    rcases hpc with h | h <;> have h1 := (congrArg Subtype.val h).symm.trans hp0
    · exact x.isX.2.2.2.2.1 (by rw [show x.a = ⊥ from h1]; exact bot_le)
    · exact x.isX.2.2.2.2.2.1 (by rw [show x.b = ⊥ from h1]; exact bot_le)
  apply le_antisymm
  · obtain ⟨K, hK, hcK, hsum⟩ := hF.attain u
    rw [← hsum]
    unfold Switch.chainSum
    calc _ ≤ ∑ p ∈ ({p0} : Finset x.toSwitch.P'), u p :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => Finset.mem_singleton.mpr
            (Subtype.ext ((eq_bot_of_not_special x hq (Lemma46.form_not_special x hK hpc hcK hp)).trans hp0.symm)))
            fun p hp _ => by rw [Finset.mem_singleton.mp hp]; exact hu.1 _ (bot_mem_I x hp0)
      _ = u p0 := Finset.sum_singleton _ _
  · have hval : ∀ s : Finset x.toSwitch.P', (∀ p, p ∈ s ↔ p = p0) → x.toSwitch.chainSum s u = u p0 :=
      fun s hs => by
        rw [show s = {p0} from Finset.ext fun p => (hs p).trans Finset.mem_singleton.symm]
        exact Finset.sum_singleton _ _
    refine (hval _ fun p => ?_).symm.trans_le
      (hF.le u _ (pair_mem_lowBranches x hp0 hpc) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
    rw [mem_erase_iff, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hp, rfl | rfl⟩
      · rfl
      · exact absurd rfl hp
    · rintro rfl
      exact ⟨hne, Or.inl rfl⟩

end Ex47Details

open Ex47Details in
/-- **Example 4.7, details** (paper lines 612–620), given Lemma 4.2 for this switch (`h42`). -/
theorem ex_4_7_details_of (x : XSwitch (WithBot XElem)) (hq : x.q = ((XElem.c : XElem) : WithBot XElem))
    (h42 : ∀ (E : Set (x.toSwitch.P' → ℝ)) (_ : IsFace x.toSwitch.B E) (w : x.toSwitch.P' → ℝ)
      (_ : CrossingAt x.toSwitch E w) (k : ℕ),
      (X ^ (adim E - 2) * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (x.toSwitch.delta E).coeff k) :
    (∀ p : {p // p ∉ x.special}, p.1.1 = ⊥) ∧ x.zeta x.u0 = 0 ∧
    (∀ u ∈ x.toSwitch.B, ∀ p0 : x.toSwitch.P', p0.1 = ⊥ → x.lamA u = u p0 ∧ x.lamB u = u p0) ∧
    (∀ k, (X ^ 2 * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (x.toSwitch.delta x.E0).coeff k) ∧
    (∀ k, (X ^ 3 * (1 + X) ^ 2 : ℤ[X]).coeff k ≤ (x.toSwitch.delta x.toSwitch.B).coeff k) := by
  have hbot : ∀ p : {p // p ∉ x.special}, p.1.1 = ⊥ := fun p => eq_bot_of_not_special x hq p.2
  have h46 := lemma_4_6_of_3_6 x (fun E hE A => lemma_3_6_proved x.toSwitch E hE A)
  obtain ⟨hE0face, hE0dim, -⟩ := lemma_4_4_proved x x.pa x.pb x.pg x.ph rfl rfl rfl rfl
  have hBface : IsFace x.toSwitch.B x.toSwitch.B := IsFace.refl (B_nonempty x.toSwitch)
  have hBdim : adim x.toSwitch.B = 5 := by
    rw [Switch.B, chainOrderPolytope_adim, card_P']
    rfl
  refine ⟨hbot, ?_, fun u hu p0 hp0 => ⟨family_eq x hq (Lemma46.familyA x) (Or.inl rfl) hu hp0,
    family_eq x hq (Lemma46.familyB x) (Or.inr rfl) hu hp0⟩, fun k => ?_, fun k => ?_⟩
  · funext p
    exact Lemma45.u0_I x p.2 (bot_mem_I x (hbot p))
  · obtain ⟨w, hw⟩ := h46 x.E0 hE0face subset_rfl
    have h := h42 x.E0 hE0face w hw k
    rw [hE0dim] at h
    exact h
  · obtain ⟨w, hw⟩ := h46 x.toSwitch.B hBface fun u hu => hu.1
    have h := h42 x.toSwitch.B hBface w hw k
    rw [hBdim] at h
    exact h

end HibiLi.Proofs
