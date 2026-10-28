/-
HibiLi/Proofs/LinExtRows.lean — the linear extensions of Section 4.4 (l. 879-883) and of the proof of Theorem 1.2(a)
(l. 982-985): review 006 coverage item B9.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

A linear extension is an enumeration `e : Fin |P| ≃ P` with `e i < e j → i < j`. Its prefixes are order ideals, and the
next element is minimal in the rest. For the switch of an `XSwitch`, sorting `P` by the key (class, linear extension of
`P`), where the class is `0` on `I`, `1` at `q` and `2` above `q`, lists `I`, then `q`, then `J'`.
-/
import HibiLi.Defs.PaperDefs

namespace HibiLi.Proofs

/-- An injective key into a linear order gives an enumeration of `P` that is strictly monotone in the key. -/
theorem exists_equiv_fin_of_key {P : Type*} [Fintype P] {α : Type*} [LinearOrder α] (key : P → α)
    (inj : Function.Injective key) :
    ∃ e : Fin (Fintype.card P) ≃ P, ∀ p p', key p < key p' → e.symm p < e.symm p' := by
  classical
  set S : Finset α := Finset.univ.image key with hSdef
  have hS : S.card = Fintype.card P := by rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
  let kE : P ≃ {z // z ∈ S} := Equiv.ofBijective
    (fun p => ⟨key p, Finset.mem_image_of_mem _ (Finset.mem_univ p)⟩)
    ⟨fun p p' h => inj (congrArg Subtype.val h), fun z => by
      obtain ⟨p, -, hp⟩ := Finset.mem_image.1 z.2
      exact ⟨p, Subtype.ext hp⟩⟩
  refine ⟨(S.orderIsoOfFin hS).toEquiv.trans kE.symm, fun p p' h => ?_⟩
  show (S.orderIsoOfFin hS).symm (kE p) < (S.orderIsoOfFin hS).symm (kE p')
  exact (S.orderIsoOfFin hS).symm.lt_iff_lt.2 h

/-- l. 879-883, 982-985: in a linear extension, each prefix `I_j` is an order ideal, and `p_{j+1}` is not in `I_j`
and is minimal in `P \ I_j`. -/
theorem sec4_linext_prefixes (P : Type*) [Fintype P] [PartialOrder P] (e : Fin (Fintype.card P) ≃ P)
    (he : ∀ i j, e i < e j → i < j) (j : ℕ) (hj : j < Fintype.card P) :
    IsLowerSet {p | (e.symm p : ℕ) < j} ∧ e ⟨j, hj⟩ ∉ {p | (e.symm p : ℕ) < j} ∧
      ∀ p, p < e ⟨j, hj⟩ → (e.symm p : ℕ) < j := by
  have hlt : ∀ p p' : P, p < p' → e.symm p < e.symm p' := fun p p' h =>
    he _ _ (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  refine ⟨fun a b hba ha => ?_, fun h => ?_, fun p hp => ?_⟩
  · have ha' : (e.symm a : ℕ) < j := ha
    show (e.symm b : ℕ) < j
    rcases hba.lt_or_eq with h | h
    · have := Fin.lt_def.1 (hlt _ _ h)
      omega
    · rw [h]
      exact ha'
  · have h' : (e.symm (e ⟨j, hj⟩) : ℕ) < j := h
    rw [Equiv.symm_apply_apply] at h'
    exact lt_irrefl _ h'
  · have := hlt _ _ hp
    rw [Equiv.symm_apply_apply] at this
    exact Fin.lt_def.1 this

/-- l. 879-883, 982-985: for the switch of `q` of Section 4.2 there is a linear extension of `P` that lists `I` first,
then `q`, then `J'`: its prefix `I_{j₀}` is `I` and its element `p_{j₀+1}` is `q`. -/
theorem sec4_linext_through_switch {P : Type*} [Fintype P] [PartialOrder P] (x : XSwitch P) :
    ∃ (e : Fin (Fintype.card P) ≃ P) (j₀ : ℕ) (hj₀ : j₀ < Fintype.card P), (∀ i j, e i < e j → i < j) ∧
      {p | (e.symm p : ℕ) < j₀} = x.toSwitch.I ∧ e ⟨j₀, hj₀⟩ = x.q := by
  classical
  let cls : P → ℕ := fun p => if ¬ x.q ≤ p then 0 else if p = x.q then 1 else 2
  let key : P → Lex (ℕ × LinearExtension P) := fun p => toLex (cls p, toLinearExtension p)
  have inj : Function.Injective key := fun p p' h => by
    have := congrArg (fun z => (ofLex z).2) h
    exact this
  have hcls : ∀ p p' : P, p ≤ p' → cls p ≤ cls p' := by
    intro p p' h
    by_cases hp : x.q ≤ p
    · have hp' : x.q ≤ p' := le_trans hp h
      by_cases hpq : p = x.q
      · by_cases hp'q : p' = x.q
        · simp [cls, hpq, hp'q]
        · simp [cls, hp', hpq, hp'q]
      · have hp'q : p' ≠ x.q := fun h' => hpq (le_antisymm (h' ▸ h) hp)
        simp [cls, hp, hp', hpq, hp'q]
    · simp [cls, hp]
  have hkey : ∀ p p' : P, p < p' → key p < key p' := by
    intro p p' h
    show toLex (cls p, toLinearExtension p) < toLex (cls p', toLinearExtension p')
    rw [Prod.Lex.lt_iff]
    rcases (hcls p p' h.le).lt_or_eq with hl | hl
    · exact Or.inl hl
    · exact Or.inr ⟨hl, lt_of_le_of_ne (toLinearExtension.monotone h.le) h.ne⟩
  obtain ⟨e, he⟩ := exists_equiv_fin_of_key key inj
  have hlin : ∀ i j, e i < e j → i < j := fun i j h => by
    have := he _ _ (hkey _ _ h)
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  refine ⟨e, (e.symm x.q : ℕ), (e.symm x.q).isLt, hlin, ?_, by simp⟩
  ext p
  show (e.symm p : ℕ) < (e.symm x.q : ℕ) ↔ ¬ x.q ≤ p
  constructor
  · intro h hqp
    rcases hqp.lt_or_eq with hlt | heq
    · have := Fin.lt_def.1 (he _ _ (hkey _ _ hlt))
      omega
    · rw [heq] at h
      exact lt_irrefl _ h
  · intro hp
    have hk : key p < key x.q := by
      show toLex (cls p, toLinearExtension p) < toLex (cls x.q, toLinearExtension x.q)
      rw [Prod.Lex.lt_iff]
      left
      simp [cls, hp]
    exact Fin.lt_def.1 (he _ _ hk)

end HibiLi.Proofs
