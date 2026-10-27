/-
HibiLi/Census/Classify.lean — the sixteen census posets are a complete, irredundant list of the 6-element posets that
contain X (paper v1.00, lines 734–735), and row 5 is P_6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Census

namespace HibiLi.Census

/-! ## The order of a census poset as a Bool table -/

theorem census_le_iff (i : Fin 16) (x y : censusPoset i) : x ≤ y ↔ censusLe i x y = true := Iff.rfl

theorem census_lt_iff (i : Fin 16) (x y : censusPoset i) : x < y ↔ censusLe i x y = true ∧ ¬ censusLe i y x = true :=
  lt_iff_le_not_ge

local instance censusLtDecidable (i : Fin 16) : DecidableRel (α := censusPoset i) (· < ·) :=
  fun x y => decidable_of_iff _ (census_lt_iff i x y).symm

/-- The element `k` of the carrier `Fin 6`, seen in `censusPoset i`. -/
def censusPt (i : Fin 16) (k : Fin 6) : censusPoset i := k

/-- Every census poset has six elements. -/
theorem census_card (i : Fin 16) : Fintype.card (censusPoset i) = 6 := Fintype.card_fin 6

/-- Every census poset contains `X`. -/
theorem census_containsX (i : Fin 16) : ContainsX (censusPoset i) := by
  refine ⟨censusPt i 0, censusPt i 1, censusPt i 2, censusPt i 3, censusPt i 4, ?_⟩
  revert i
  decide

/-! ## Non-isomorphism: an invariant that separates the sixteen rows -/

section Invariant

variable {Q : Type*} [Fintype Q] [PartialOrder Q] [DecidableRel (α := Q) (· < ·)]

/-- The number of elements strictly below `x`. -/
def belowCard (x : Q) : ℕ := (Finset.univ.filter (· < x)).card

/-- The number of elements strictly above `x`. -/
def aboveCard (x : Q) : ℕ := (Finset.univ.filter (x < ·)).card

variable (Q) in
/-- The multiset of the pairs `(#below x, #above x)`, encoded in base 7 (in a 6-element poset each count is `≤ 5`). -/
def censusSig : ℕ := ∑ x : Q, 7 ^ (6 * belowCard x + aboveCard x)

variable {R : Type*} [Fintype R] [PartialOrder R] [DecidableRel (α := R) (· < ·)]

theorem belowCard_iso (e : Q ≃o R) (x : Q) : belowCard (e x) = belowCard x :=
  Finset.card_equiv e.toEquiv.symm fun y => by simpa using e.symm_apply_lt.symm

theorem aboveCard_iso (e : Q ≃o R) (x : Q) : aboveCard (e x) = aboveCard x :=
  Finset.card_equiv e.toEquiv.symm fun y => by simpa using e.lt_symm_apply.symm

theorem censusSig_iso (e : Q ≃o R) : censusSig Q = censusSig R :=
  Fintype.sum_equiv e.toEquiv _ _ fun x => by simp [belowCard_iso, aboveCard_iso]

end Invariant

theorem censusSig_injective : Function.Injective fun i : Fin 16 => censusSig (censusPoset i) := by
  decide

/-- The sixteen census posets are pairwise non-isomorphic. -/
theorem census_iso_eq {i j : Fin 16} (h : Nonempty (censusPoset i ≃o censusPoset j)) : i = j :=
  censusSig_injective (censusSig_iso h.some)

/-! ## Completeness

A 6-element poset containing `X` is `X` (labels `0..4` = a, b, c, g, h) plus one element `f` (label `5`), and its
order is fixed by the `X`-elements below `f` (`d`) and above `f` (`u`). A finite table, checked by the kernel, sends
each of the 30 consistent pairs `(d, u)` to a census row, up to a relabelling `relab s k`: first exchange `k` with `f`
(a poset may contain several copies of `X`, and the row may use another one), then a symmetry of `X`. -/

/-- The order on `Fin 6` of `X` plus `f = 5`, with the `X`-elements `d` below `f` and `u` above `f`. -/
def relDU (d u : Fin 5 → Bool) (x y : Fin 6) : Bool :=
  decide (x = y) ||
  (decide (x.val < 5) && decide (y.val < 5) && decide (censusXRank x < censusXRank y)) ||
  (decide (y.val = 5) && (if hx : x.val < 5 then d ⟨x.val, hx⟩ else false)) ||
  (decide (x.val = 5) && (if hy : y.val < 5 then u ⟨y.val, hy⟩ else false))

/-- The four symmetries of `X` (exchange a, b and/or g, h). -/
def autX : Fin 4 → Equiv.Perm (Fin 6) := ![1, Equiv.swap 0 1, Equiv.swap 3 4, Equiv.swap 0 1 * Equiv.swap 3 4]

/-- Exchange `k` with `f = 5`, then apply the symmetry `autX s`. -/
def relab (s : Fin 4) (k : Fin 6) : Equiv.Perm (Fin 6) := autX s * Equiv.swap k 5

/-- The instances of transitivity and antisymmetry of `relDU d u` that involve `f = 5`. -/
def ValidDU (d u : Fin 5 → Bool) : Prop :=
  (∀ x y : Fin 6, relDU d u x y = true → relDU d u y 5 = true → relDU d u x 5 = true) ∧
  (∀ y z : Fin 6, relDU d u 5 y = true → relDU d u y z = true → relDU d u 5 z = true) ∧
  (∀ x z : Fin 6, relDU d u x 5 = true → relDU d u 5 z = true → relDU d u x z = true) ∧
  (∀ x : Fin 6, relDU d u x 5 = true → relDU d u 5 x = true → x = 5)

instance (d u : Fin 5 → Bool) : Decidable (ValidDU d u) := by unfold ValidDU; infer_instance

/-- The table: every consistent `(d, u)` is a census row up to a relabelling (1024 cases, by the kernel). -/
theorem dU_table : ∀ d0 d1 d2 d3 d4 u0 u1 u2 u3 u4 : Bool,
    ValidDU ![d0, d1, d2, d3, d4] ![u0, u1, u2, u3, u4] →
    ∃ i : Fin 16, ∃ s : Fin 4, ∃ k : Fin 6, ∀ x y : Fin 6,
      relDU ![d0, d1, d2, d3, d4] ![u0, u1, u2, u3, u4] x y = censusLe i (relab s k x) (relab s k y) := by
  decide +kernel

theorem dU_table_of_valid (d u : Fin 5 → Bool) (h : ValidDU d u) :
    ∃ i : Fin 16, ∃ s : Fin 4, ∃ k : Fin 6, ∀ x y : Fin 6,
      relDU d u x y = censusLe i (relab s k x) (relab s k y) := by
  have hd : d = ![d 0, d 1, d 2, d 3, d 4] := by funext x; fin_cases x <;> rfl
  have hu : u = ![u 0, u 1, u 2, u 3, u 4] := by funext x; fin_cases x <;> rfl
  rw [hd, hu] at h ⊢
  exact dU_table _ _ _ _ _ _ _ _ _ _ h

/-- A 6-element poset containing `X` has an element outside any five given ones. -/
theorem exists_sixth_elem {P : Type*} [Fintype P] [DecidableEq P] (hcard : Fintype.card P = 6) (a b c g h : P) :
    ∃ f : P, f ∉ ({a, b, c, g, h} : Finset P) := by
  obtain ⟨f, -, hf⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b, c, g, h}) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard]; exact Nat.lt_of_le_of_lt Finset.card_le_five (by norm_num))
  exact ⟨f, hf⟩

/-- Every 6-element poset that contains `X` is isomorphic to a census poset. -/
theorem census_complete (P : Type*) [Fintype P] [PartialOrder P] (hcard : Fintype.card P = 6)
    (hX : ContainsX P) : ∃ i, Nonempty (P ≃o censusPoset i) := by
  classical
  obtain ⟨a, b, c, g, h, hac, hbc, hcg, hch, hab, hba, hgh, hhg⟩ := hX
  obtain ⟨f, hf⟩ := exists_sixth_elem hcard a b c g h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hf
  obtain ⟨hfa, hfb, hfc, hfg, hfh⟩ := hf
  have hag := hac.trans hcg
  have hah := hac.trans hch
  have hbg := hbc.trans hcg
  have hbh := hbc.trans hch
  let e : Fin 6 → P := ![a, b, c, g, h, f]
  -- `e` is a bijection
  have hinj : Function.Injective e := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp [e] at hxy ⊢ <;> subst_vars <;> simp_all
  have hbij : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).mpr ⟨hinj, by rw [Fintype.card_fin, hcard]⟩
  -- the order of `P`, pulled back along `e`
  let d : Fin 5 → Bool := fun k => decide (e k.castSucc < f)
  let u : Fin 5 → Bool := fun k => decide (f < e k.castSucc)
  have key : ∀ x y : Fin 6, e x ≤ e y ↔ relDU d u x y = true := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [e, d, u, relDU, censusXRank, hac.le, hbc.le, hcg.le, hch.le, hag.le,
      hah.le, hbg.le, hbh.le, hab, hba, hgh, hhg, hac.not_ge, hbc.not_ge, hcg.not_ge, hch.not_ge, hag.not_ge,
      hah.not_ge, hbg.not_ge, hbh.not_ge, le_iff_lt_or_eq, hfa, hfb, hfc, hfg, hfh, Ne.symm hfa, Ne.symm hfb,
      Ne.symm hfc, Ne.symm hfg, Ne.symm hfh]
    all_goals exact decide_eq_true_iff.symm
  have hvalid : ValidDU d u := by
    refine ⟨fun x y h1 h2 => ?_, fun y z h1 h2 => ?_, fun x z h1 h2 => ?_, fun x h1 h2 => ?_⟩
    · rw [← key] at h1 h2 ⊢; exact h1.trans h2
    · rw [← key] at h1 h2 ⊢; exact h1.trans h2
    · rw [← key] at h1 h2 ⊢; exact h1.trans h2
    · rw [← key] at h1 h2; exact hinj (le_antisymm h1 h2)
  obtain ⟨i, s, k, hrel⟩ := dU_table_of_valid d u hvalid
  let E : P ≃ censusPoset i := (Equiv.ofBijective e hbij).symm.trans (relab s k)
  refine ⟨i, ⟨{ toEquiv := E, map_rel_iff' := ?_ }⟩⟩
  intro p q
  obtain ⟨x, rfl⟩ := hbij.2 p
  obtain ⟨y, rfl⟩ := hbij.2 q
  have hx : (Equiv.ofBijective e hbij).symm (e x) = x := (Equiv.ofBijective e hbij).symm_apply_apply x
  have hy : (Equiv.ofBijective e hbij).symm (e y) = y := (Equiv.ofBijective e hbij).symm_apply_apply y
  change censusLe i (relab s k ((Equiv.ofBijective e hbij).symm (e x)))
    (relab s k ((Equiv.ofBijective e hbij).symm (e y))) = true ↔ e x ≤ e y
  rw [hx, hy, ← hrel, key]

/-! ## Row 5 is `P_6` -/

/-- Census row 5 (`i = 4`: `f` below everything) is `P_6 = sharpFamily 1` (`X` with a new bottom). -/
theorem census_iso_sharp : Nonempty (censusPoset 4 ≃o sharpFamily 1) := by
  let toS : Fin 6 → WithBot XElem := ![↑XElem.a, ↑XElem.b, ↑XElem.c, ↑XElem.g, ↑XElem.h, ⊥]
  let ofS : WithBot XElem → Fin 6
    | ⊥ => 5
    | (XElem.a : XElem) => 0
    | (XElem.b : XElem) => 1
    | (XElem.c : XElem) => 2
    | (XElem.g : XElem) => 3
    | (XElem.h : XElem) => 4
  have hle : ∀ x y : Fin 6, toS x ≤ toS y ↔ censusLe 4 x y = true := by decide
  exact ⟨{ toFun := toS, invFun := ofS,
           left_inv := by intro x; fin_cases x <;> rfl,
           right_inv := by intro x; rcases x with _ | x; · rfl
                           cases x <;> rfl,
           map_rel_iff' := fun {x y} => hle x y }⟩

end HibiLi.Census
