/-
LeeDiam/Sec4/HalfJunction.lean — Section 4 helper: the half junction (Lemma 4.12, sec_chain.tex v1.50 l. 138-150).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

Lean columns are 0-based: `p = i - 2` is the column where `W` is tame, `q = i - 1` holds the new middle element `b_q`,
and the outer row `r` holds the segment on the columns `i, …, i + j - 1`. The core works in row `a` (`r = 0`; row `c`
by `σ`), with `a_i` initial (by reversal). Part 1 merges `W` with a 3-move walk on column `q` (`part1_init`,
`part1_final`); afterwards `c_q` arrives at move `μ'` and `a_q` at move `ν'` (`HJTimed`). Part 2 merges the result with
the comb walk of Lemma 4.5 with odd helper positions, its phases ordered so that the component of `c_i` is exchanged
last in phase 1 and first in phase 2 (`comb_first`): `c_i` is present in exactly one state.
-/
import LeeDiam.Defs.Chain
import LeeDiam.Sec4.Junction
import LeeDiam.Sec4.TableRows

namespace LeeDiam.S4

open Finset Band

section HalfJunction

variable {k : ℕ}

theorem merge2_getD {P : Type} (W V : List (Set P)) (w v : ℕ → ℕ) {M t : ℕ} (ht : t ≤ M) :
    (merge2 W V w v M).getD t ∅ = W.getD (w t) ∅ ∪ V.getD (v t) ∅ := by
  unfold merge2
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

/-- An element that lies in no state of `W` is in a merged state exactly when it is in the state of `V`. -/
theorem mem_merge2_right {W V : List (Set (Band k))} {w v : ℕ → ℕ} {M t : ℕ} {y : Band k}
    (hy : ∀ X ∈ W, y ∉ X) : y ∈ (merge2 W V w v M).getD t ∅ ↔ t ≤ M ∧ y ∈ V.getD (v t) ∅ := by
  by_cases ht : t ≤ M
  · rw [merge2_getD W V w v ht]
    constructor
    · rintro (h | h)
      · obtain ⟨X, hX, hyX⟩ := mem_of_mem_getD h
        exact absurd hyX (hy X hX)
      · exact ⟨ht, h⟩
    · rintro ⟨-, h⟩
      exact Or.inr h
  · rw [getD_eq_empty (by rw [merge2_length]; omega)]
    simp only [Set.mem_empty_iff_false, false_iff, not_and]
    intro h
    exact absurd h ht

/-- In a walk tame at column `p` with outer element `h`, every outer element of column `p` in a state is `h`. -/
theorem tame_only_h {W : List (Set (Band k))} {p : Fin k} {h : Band k} (hW : IsWalk W) (hT : IsTameAt W p h)
    {X : Set (Band k)} (hX : X ∈ W) {x : Band k} (hx : x ∈ X) (hx1 : x.1 = p) (hx2 : x.2 ≠ 1) : x = h := by
  have hxac : x = a p ∨ x = c p := by
    have hlt := x.2.isLt
    have h2' : x.2.val ≠ 1 := fun hv => hx2 (Fin.ext hv)
    rcases (by omega : x.2.val = 0 ∨ x.2.val = 2) with hv | hv
    · exact Or.inl (Prod.ext hx1 (Fin.ext hv))
    · exact Or.inr (Prod.ext hx1 (Fin.ext hv))
  have hxo : outerAt X p = some x := by
    rcases hxac with rfl | rfl
    · exact outerAt_of_a_mem hx
    · have hna : a p ∉ X := fun ha => a_ne_c p p (antichain_col (hW.2.1 X hX) ha hx rfl)
      exact outerAt_of_c_mem hna hx
  rcases tame_outer hT hX with h1 | h1 <;> rw [hxo] at h1
  · exact absurd h1 (by simp)
  · exact Option.some_inj.1 h1

theorem vinit_c (q : Fin k) (v : ℕ) :
    c q ∈ ([{b q}, {c q}, {a q}, ∅] : List (Set (Band k))).getD v ∅ ↔ v = 1 := by
  rcases v with _ | _ | _ | _ | v <;> simp [(b_ne_c q q).symm, (a_ne_c q q).symm]

theorem vinit_a (q : Fin k) (v : ℕ) :
    a q ∈ ([{b q}, {c q}, {a q}, ∅] : List (Set (Band k))).getD v ∅ ↔ v = 2 := by
  rcases v with _ | _ | _ | _ | v <;> simp [a_ne_b q q, a_ne_c q q]

theorem vfinal_c (q : Fin k) (v : ℕ) :
    c q ∈ ([∅, {c q}, {a q}, {b q}] : List (Set (Band k))).getD v ∅ ↔ v = 1 := by
  rcases v with _ | _ | _ | _ | v <;> simp [(b_ne_c q q).symm, (a_ne_c q q).symm]

theorem vfinal_a (q : Fin k) (v : ℕ) :
    a q ∈ ([∅, {c q}, {a q}, {b q}] : List (Set (Band k))).getD v ∅ ↔ v = 2 := by
  rcases v with _ | _ | _ | _ | v <;> simp [a_ne_b q q, a_ne_c q q]

/-- The column-`q` timing that Part 2 needs from `W'`: `c_q` first appears in state `μ'`; `a_q` is absent from the
states `μ', …, ν' - 1` and present in state `ν'`. -/
def HJTimed (W' : List (Set (Band k))) (q : Fin k) (μ' ν' : ℕ) : Prop :=
  1 ≤ μ' ∧ μ' < ν' ∧ ν' ≤ W'.length - 1 ∧ (∀ t, c q ∈ W'.getD t ∅ → μ' ≤ t) ∧ c q ∈ W'.getD μ' ∅ ∧
    (∀ t, a q ∈ W'.getD t ∅ → t < μ' ∨ ν' ≤ t) ∧ a q ∈ W'.getD ν' ∅

/-- The schedule of `W` in Part 1 when `b_q` is initial: `W` waits one step, just after its departure move `ν`. -/
def hiW (ν t : ℕ) : ℕ := if t ≤ ν then t else t - 1

/-- The schedule of `b → c → a → -`: move 1 with move `μ` of `W`, move 2 with move `ν`, move 3 alone after `ν`. -/
def hiV (μ ν t : ℕ) : ℕ := if t < μ then 0 else if t < ν then 1 else if t = ν then 2 else 3

/-- A state of a walk whose columns are at most `p` has no element of column `q = p + 1`. -/
theorem not_mem_of_cols {W : List (Set (Band k))} {p q : Fin k} (hpq : q.val = p.val + 1)
    (hcolW : ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ p.val) {y : Band k} (hy : y.1 = q) : ∀ X ∈ W, y ∉ X :=
  fun X hX hyX => by
    have := hcolW X hX y hyX
    rw [hy] at this
    omega

/-- Part 1 of Lemma 4.12 when `b_q` is initial (`W` tame at `p` with outer element `c_p`). -/
theorem part1_init {p q : Fin k} (hpq : q.val = p.val + 1)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} (hW : IsWalkFromTo W A' B') (hT : IsTameAt W p (c p)) :
    ∃ W' μ' ν', IsWalkFromTo W' (A' ∪ {b q}) B' ∧ W'.length - 1 = (W.length - 1) + 1 ∧
      (∀ X ∈ W', ∀ x ∈ X, x.1.val ≤ q.val) ∧ HJTimed W' q μ' ν' := by
  obtain ⟨μ, ν, hμ1, hμν, hνn, hmem⟩ := tame_arrive_depart W p (c p) hT
  have hWlen := List.length_pos_of_ne_nil hW.1.1
  have hcolW : ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ p.val := tame_cols_le hT
  set V : List (Set (Band k)) := [{b q}, {c q}, {a q}, ∅] with hVdef
  have hV : IsWalkFromTo V {b q} ∅ := col_walk_init q
  have hVcols : ∀ Y ∈ V, ∀ y ∈ Y, y.1 = q := by
    intro Y hY y hy
    simp only [hVdef, List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl
    · rw [Set.mem_singleton_iff.1 hy]; rfl
    · rw [Set.mem_singleton_iff.1 hy]; rfl
    · rw [Set.mem_singleton_iff.1 hy]; rfl
    · exact absurd hy (Set.notMem_empty y)
  set n := W.length - 1 with hn
  have hw0 : hiW ν 0 = 0 := by unfold hiW; split_ifs <;> omega
  have hv0 : hiV μ ν 0 = 0 := by unfold hiV; split_ifs <;> omega
  have hwM : hiW ν (n + 1) = W.length - 1 := by unfold hiW; split_ifs <;> omega
  have hvM : hiV μ ν (n + 1) = V.length - 1 := by simp only [hVdef]; unfold hiV; split_ifs <;> simp <;> omega
  have hws : ∀ t < n + 1, hiW ν (t + 1) = hiW ν t ∨ hiW ν (t + 1) = hiW ν t + 1 := by
    intro t ht; unfold hiW; split_ifs <;> omega
  have hvs : ∀ t < n + 1, hiV μ ν (t + 1) = hiV μ ν t ∨ hiV μ ν (t + 1) = hiV μ ν t + 1 := by
    intro t ht; unfold hiV; split_ifs <;> omega
  have hmove : ∀ t < n + 1, hiW ν (t + 1) = hiW ν t + 1 ∨ hiV μ ν (t + 1) = hiV μ ν t + 1 := by
    intro t ht; unfold hiW hiV; split_ifs <;> omega
  have hdisj : ∀ X ∈ W, ∀ Y ∈ V, Disjoint X Y := fun X hX Y hY =>
    Set.disjoint_left.2 fun x hxX hxY => not_mem_of_cols hpq hcolW (hVcols Y hY x hxY) X hX hxX
  have hanti : ∀ t ≤ n + 1, ∀ x ∈ W.getD (hiW ν t) ∅, ∀ y ∈ V.getD (hiV μ ν t) ∅, ¬ Comp x y := by
    intro t ht x hx y hy hxy
    obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hx
    obtain ⟨Y, hY, hyY⟩ := mem_of_mem_getD hy
    have hxc := hcolW X hX x hxX
    have hyv : y.1.val = p.val + 1 := by rw [hVcols Y hY y hyY]; exact hpq
    have hcomp := hxy
    rw [comp_iff_val] at hcomp
    have key : x.1.val = p.val ∧ x.2.val ≠ 1 := by omega
    have hxh : x = c p := tame_only_h hW.1 hT hX hxX (Fin.ext key.1) (fun h => key.2 (by rw [h]; rfl))
    subst hxh
    have hlt : hiW ν t < W.length := by unfold hiW; split_ifs <;> omega
    have hm := (hmem _ hlt).1 hx
    have hv1 : hiV μ ν t = 1 := by
      unfold hiW at hm
      unfold hiV
      split_ifs at hm ⊢ <;> omega
    rw [hv1] at hy
    have hyq : y = c q := Set.mem_singleton_iff.1 hy
    subst hyq
    rw [comp_iff_val] at hxy
    simp only [c_val2] at hxy
    omega
  have hboth : ∀ t < n + 1, hiW ν (t + 1) = hiW ν t + 1 → hiV μ ν (t + 1) = hiV μ ν t + 1 →
      ∃ x ∈ symmDiff (W.getD (hiW ν t) ∅) (W.getD (hiW ν t + 1) ∅),
        ∃ y ∈ symmDiff (V.getD (hiV μ ν t) ∅) (V.getD (hiV μ ν t + 1) ∅), Comp x y := by
    intro t ht hw hv
    have ht' : t + 1 = μ ∨ t + 1 = ν := by
      unfold hiW at hw
      unfold hiV at hv
      split_ifs at hw hv <;> omega
    rcases ht' with h1 | h1
    · have e1 : hiW ν t = t := by unfold hiW; split_ifs <;> omega
      have e2 : hiV μ ν t = 0 := by unfold hiV; split_ifs <;> omega
      rw [e1, e2, h1]
      refine ⟨c p, Set.mem_symmDiff.2 (Or.inr ⟨(hmem μ (by omega)).2 ⟨le_rfl, hμν⟩, fun h => ?_⟩), b q,
        Set.mem_symmDiff.2 (Or.inl ⟨Set.mem_singleton _, fun h => ?_⟩), comp_symm (comp_bc_prev hpq)⟩
      · have := ((hmem t (by omega)).1 h).1
        omega
      · exact b_ne_c q q (Set.mem_singleton_iff.1 h)
    · have e1 : hiW ν t = t := by unfold hiW; split_ifs <;> omega
      have e2 : hiV μ ν t = 1 := by unfold hiV; split_ifs <;> omega
      rw [e1, e2, h1]
      refine ⟨c p, Set.mem_symmDiff.2 (Or.inl ⟨(hmem t (by omega)).2 ⟨by omega, by omega⟩, fun h => ?_⟩), a q,
        Set.mem_symmDiff.2 (Or.inr ⟨Set.mem_singleton _, fun h => ?_⟩), comp_ca_next hpq⟩
      · have := ((hmem ν (by omega)).1 h).2
        omega
      · exact a_ne_c q q (Set.mem_singleton_iff.1 h)
  have hwalk := merge2_walk hW hV hw0 hv0 hwM hvM hws hvs hmove hdisj hanti hboth
  rw [Set.union_empty] at hwalk
  have hcq : ∀ X ∈ W, c q ∉ X := not_mem_of_cols hpq hcolW rfl
  have haq : ∀ X ∈ W, a q ∉ X := not_mem_of_cols hpq hcolW rfl
  refine ⟨merge2 W V (hiW ν) (hiV μ ν) (n + 1), μ, ν, hwalk, by rw [merge2_length]; omega, ?_,
    hμ1, hμν, by rw [merge2_length]; omega, ?_, ?_, ?_, ?_⟩
  · intro X hX x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
    rcases hx with hx | hx
    · obtain ⟨X', hX', hx'⟩ := mem_of_mem_getD hx
      have := hcolW X' hX' x hx'
      omega
    · obtain ⟨Y, hY, hy⟩ := mem_of_mem_getD hx
      rw [hVcols Y hY x hy]
  · intro t ht
    obtain ⟨-, h2⟩ := (mem_merge2_right hcq).1 ht
    rw [vinit_c] at h2
    unfold hiV at h2
    split_ifs at h2 <;> omega
  · rw [mem_merge2_right hcq, vinit_c]
    refine ⟨by omega, ?_⟩
    unfold hiV
    split_ifs <;> omega
  · intro t ht
    obtain ⟨-, h2⟩ := (mem_merge2_right haq).1 ht
    rw [vinit_a] at h2
    unfold hiV at h2
    split_ifs at h2 <;> omega
  · rw [mem_merge2_right haq, vinit_a]
    refine ⟨by omega, ?_⟩
    unfold hiV
    split_ifs <;> omega

/-- Part 1 of Lemma 4.12 when `b_q` is final (`W` tame at `p` with outer element `a_p`). -/
theorem part1_final {p q : Fin k} (hpq : q.val = p.val + 1)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} (hW : IsWalkFromTo W A' B') (hT : IsTameAt W p (a p)) :
    ∃ W' μ' ν', IsWalkFromTo W' A' (B' ∪ {b q}) ∧ W'.length - 1 = (W.length - 1) + 1 ∧
      (∀ X ∈ W', ∀ x ∈ X, x.1.val ≤ q.val) ∧ HJTimed W' q μ' ν' := by
  obtain ⟨μ, ν, hμ1, hμν, hνn, hmem⟩ := tame_arrive_depart W p (a p) hT
  have hWlen := List.length_pos_of_ne_nil hW.1.1
  have hcolW : ∀ X ∈ W, ∀ x ∈ X, x.1.val ≤ p.val := tame_cols_le hT
  set V : List (Set (Band k)) := [∅, {c q}, {a q}, {b q}] with hVdef
  have hV : IsWalkFromTo V ∅ {b q} := col_walk_final q
  have hVcols : ∀ Y ∈ V, ∀ y ∈ Y, y.1 = q := by
    intro Y hY y hy
    simp only [hVdef, List.mem_cons, List.not_mem_nil, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl
    · exact absurd hy (Set.notMem_empty y)
    · rw [Set.mem_singleton_iff.1 hy]; rfl
    · rw [Set.mem_singleton_iff.1 hy]; rfl
    · rw [Set.mem_singleton_iff.1 hy]; rfl
  set n := W.length - 1 with hn
  have hw0 : tsW μ 0 = 0 := by unfold tsW; split_ifs <;> omega
  have hv0 : tsV μ ν 0 = 0 := by unfold tsV; split_ifs <;> omega
  have hwM : tsW μ (n + 1) = W.length - 1 := by unfold tsW; split_ifs <;> omega
  have hvM : tsV μ ν (n + 1) = V.length - 1 := by simp only [hVdef]; unfold tsV; split_ifs <;> simp <;> omega
  have hws : ∀ t < n + 1, tsW μ (t + 1) = tsW μ t ∨ tsW μ (t + 1) = tsW μ t + 1 := by
    intro t ht; unfold tsW; split_ifs <;> omega
  have hvs : ∀ t < n + 1, tsV μ ν (t + 1) = tsV μ ν t ∨ tsV μ ν (t + 1) = tsV μ ν t + 1 := by
    intro t ht; unfold tsV; split_ifs <;> omega
  have hmove : ∀ t < n + 1, tsW μ (t + 1) = tsW μ t + 1 ∨ tsV μ ν (t + 1) = tsV μ ν t + 1 := by
    intro t ht; unfold tsW tsV; split_ifs <;> omega
  have hdisj : ∀ X ∈ W, ∀ Y ∈ V, Disjoint X Y := fun X hX Y hY =>
    Set.disjoint_left.2 fun x hxX hxY => not_mem_of_cols hpq hcolW (hVcols Y hY x hxY) X hX hxX
  have hanti : ∀ t ≤ n + 1, ∀ x ∈ W.getD (tsW μ t) ∅, ∀ y ∈ V.getD (tsV μ ν t) ∅, ¬ Comp x y := by
    intro t ht x hx y hy hxy
    obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hx
    obtain ⟨Y, hY, hyY⟩ := mem_of_mem_getD hy
    have hxc := hcolW X hX x hxX
    have hyv : y.1.val = p.val + 1 := by rw [hVcols Y hY y hyY]; exact hpq
    have hcomp := hxy
    rw [comp_iff_val] at hcomp
    have key : x.1.val = p.val ∧ x.2.val ≠ 1 := by omega
    have hxh : x = a p := tame_only_h hW.1 hT hX hxX (Fin.ext key.1) (fun h => key.2 (by rw [h]; rfl))
    subst hxh
    have hlt : tsW μ t < W.length := by unfold tsW; split_ifs <;> omega
    have hm := (hmem _ hlt).1 hx
    have hv2 : tsV μ ν t = 2 := by
      unfold tsW at hm
      unfold tsV
      split_ifs at hm ⊢ <;> omega
    rw [hv2] at hy
    have hyq : y = a q := Set.mem_singleton_iff.1 hy
    subst hyq
    rw [comp_iff_val] at hxy
    simp only [a_val2] at hxy
    omega
  have hboth : ∀ t < n + 1, tsW μ (t + 1) = tsW μ t + 1 → tsV μ ν (t + 1) = tsV μ ν t + 1 →
      ∃ x ∈ symmDiff (W.getD (tsW μ t) ∅) (W.getD (tsW μ t + 1) ∅),
        ∃ y ∈ symmDiff (V.getD (tsV μ ν t) ∅) (V.getD (tsV μ ν t + 1) ∅), Comp x y := by
    intro t ht hw hv
    have ht' : t = μ ∨ t = ν := by
      unfold tsW at hw
      unfold tsV at hv
      split_ifs at hw hv <;> omega
    rcases ht' with rfl | rfl
    · have e1 : tsW t t = t - 1 := by unfold tsW; simp
      have e2 : tsV t ν t = 1 := by unfold tsV; simp
      rw [e1, e2, Nat.sub_add_cancel hμ1]
      refine ⟨a p, Set.mem_symmDiff.2 (Or.inr ⟨(hmem t (by omega)).2 ⟨le_rfl, hμν⟩, fun h => ?_⟩), c q,
        Set.mem_symmDiff.2 (Or.inl ⟨Set.mem_singleton _, fun h => ?_⟩), comp_ac_next hpq⟩
      · have := ((hmem (t - 1) (by omega)).1 h).1
        omega
      · exact a_ne_c q q (Set.mem_singleton_iff.1 h).symm
    · have e1 : tsW μ t = t - 1 := by unfold tsW; split_ifs <;> omega
      have e2 : tsV μ t t = 2 := by unfold tsV; split_ifs <;> omega
      rw [e1, e2, Nat.sub_add_cancel (by omega : 1 ≤ t)]
      refine ⟨a p, Set.mem_symmDiff.2 (Or.inl ⟨(hmem (t - 1) (by omega)).2 ⟨by omega, by omega⟩, fun h => ?_⟩),
        b q, Set.mem_symmDiff.2 (Or.inr ⟨Set.mem_singleton _, fun h => ?_⟩), comp_symm (comp_ba_prev hpq)⟩
      · have := ((hmem t (by omega)).1 h).2
        omega
      · exact a_ne_b q q (Set.mem_singleton_iff.1 h).symm
  have hwalk := merge2_walk hW hV hw0 hv0 hwM hvM hws hvs hmove hdisj hanti hboth
  rw [Set.union_empty] at hwalk
  have hcq : ∀ X ∈ W, c q ∉ X := not_mem_of_cols hpq hcolW rfl
  have haq : ∀ X ∈ W, a q ∉ X := not_mem_of_cols hpq hcolW rfl
  refine ⟨merge2 W V (tsW μ) (tsV μ ν) (n + 1), μ, μ + 1, hwalk, by rw [merge2_length]; omega, ?_,
    hμ1, by omega, by rw [merge2_length]; omega, ?_, ?_, ?_, ?_⟩
  · intro X hX x hx
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
    rcases hx with hx | hx
    · obtain ⟨X', hX', hx'⟩ := mem_of_mem_getD hx
      have := hcolW X' hX' x hx'
      omega
    · obtain ⟨Y, hY, hy⟩ := mem_of_mem_getD hx
      rw [hVcols Y hY x hy]
  · intro t ht
    obtain ⟨-, h2⟩ := (mem_merge2_right hcq).1 ht
    rw [vfinal_c] at h2
    unfold tsV at h2
    split_ifs at h2 <;> omega
  · rw [mem_merge2_right hcq, vfinal_c]
    refine ⟨by omega, ?_⟩
    unfold tsV
    split_ifs <;> omega
  · intro t ht
    obtain ⟨-, h2⟩ := (mem_merge2_right haq).1 ht
    rw [vfinal_a] at h2
    unfold tsV at h2
    split_ifs at h2 <;> omega
  · rw [mem_merge2_right haq, vfinal_a]
    refine ⟨by omega, ?_⟩
    unfold tsV
    split_ifs <;> omega

/-! ### Part 2: the comb walk with odd helper positions, ordered around the first helper -/

/-- The components of `S`, listed without repetition, with a chosen component `D₀` first. -/
theorem exists_comps_list_first {P : Type} [PartialOrder P] [Finite P] (S : Set P) {D₀ : Set P}
    (hD₀ : IsComponent D₀ S) :
    ∃ L : List (Set P), L.Nodup ∧ (∀ D, D ∈ L ↔ IsComponent D S) ∧ L.head? = some D₀ := by
  obtain ⟨L, hnd, hL⟩ := exists_comps_list S
  have hperm : L.Perm (D₀ :: L.erase D₀) := List.perm_cons_erase ((hL D₀).2 hD₀)
  exact ⟨D₀ :: L.erase D₀, hperm.nodup_iff.1 hnd, fun D => by rw [← hperm.mem_iff, hL], rfl⟩

/-- The components of `S`, listed without repetition, with a chosen component `D₀` last. -/
theorem exists_comps_list_last {P : Type} [PartialOrder P] [Finite P] (S : Set P) {D₀ : Set P}
    (hD₀ : IsComponent D₀ S) :
    ∃ L : List (Set P), L.Nodup ∧ (∀ D, D ∈ L ↔ IsComponent D S) ∧ L.getLast? = some D₀ := by
  obtain ⟨L, hnd, hL⟩ := exists_comps_list S
  have hperm : L.Perm (L.erase D₀ ++ [D₀]) :=
    (List.perm_cons_erase ((hL D₀).2 hD₀)).trans (List.perm_append_comm (l₁ := [D₀]))
  exact ⟨L.erase D₀ ++ [D₀], hperm.nodup_iff.1 hnd, fun D => by rw [← hperm.mem_iff, hL], by simp⟩

/-- Lemma 4.5 with odd helper positions, its phases ordered for the half junction: the component of the first
helper `c_s` is exchanged last in the first phase and first in the second. When `a_s` is initial, `c_s` lies exactly
in state `κ` and `a_s` exactly in the states before `κ`. -/
theorem comb_first (s e : ℕ) (hse : s ≤ e) (hek : e < k) (A B : Set (Band k)) (hAB : IsSplit A B (rowSeg 0 s e))
    (hs : a (⟨s, by omega⟩ : Fin k) ∈ A) :
    ∃ Q : List (Set (Band k)), ∃ κ, IsWalkFromTo Q A B ∧ Q.length - 1 = (e - s + 2) / 2 + 1 ∧
      (∀ X ∈ Q, X ⊆ rowSeg 0 s e ∪ helperSet 0 s e) ∧ 1 ≤ κ ∧ κ + 1 ≤ Q.length - 1 ∧
      (∀ t, c (⟨s, by omega⟩ : Fin k) ∈ Q.getD t ∅ ↔ t = κ) ∧
      (∀ t, a (⟨s, by omega⟩ : Fin k) ∈ Q.getD t ∅ ↔ t < κ) := by
  classical
  set C : Set (Band k) := helperSet 0 s e with hC
  set cs : Band k := c ⟨s, by omega⟩ with hcs
  set as : Band k := a ⟨s, by omega⟩ with has
  have hcsC : cs ∈ C := c_mem_helperSet.2 (mem_helperCols.2 ⟨le_rfl, hse, by simp⟩)
  have hasC : as ∉ C := fun h => absurd h.1 (by show ¬ ((0 : Fin 3) = 2); decide)
  have hasB : as ∉ B := fun h => Set.disjoint_left.1 hAB.1 hs h
  obtain ⟨D₁, hD₁, hcsD₁⟩ := comp_exists (S := A ∪ C) (Or.inr hcsC)
  obtain ⟨D₂, hD₂, hcsD₂⟩ := comp_exists (S := C ∪ B) (Or.inl hcsC)
  have hasD₁ : as ∈ D₁ := comp_closed (y := as) hD₁ hcsD₁ (Or.inl hs) (comp_symm (comp_ac_same _))
  obtain ⟨L₁, h₁nd, h₁c, h₁last⟩ := exists_comps_list_last (A ∪ C) hD₁
  obtain ⟨L₂, h₂nd, h₂c, h₂head⟩ := exists_comps_list_first (C ∪ B) hD₂
  obtain ⟨-, hW, hlen, hsub, htime⟩ := comb s e hse hek 0 (Or.inl rfl) A B hAB L₁ L₂ h₁nd h₁c h₂nd h₂c
  have h₁ne : L₁ ≠ [] := fun h => by rw [h] at h₁last; simp at h₁last
  have h₂ne : L₂ ≠ [] := fun h => by rw [h] at h₂head; simp at h₂head
  have h₁pos := List.length_pos_of_ne_nil h₁ne
  have h₂pos := List.length_pos_of_ne_nil h₂ne
  have hQlen : (L₁.scanl symmDiff A ++ (L₂.scanl symmDiff C).tail).length = L₁.length + L₂.length + 1 := by
    simp only [List.length_append, List.length_scanl, List.length_tail]
    omega
  have hD₁get : L₁.getD (L₁.length - 1) ∅ = D₁ := lastD_of_getLast? h₁last
  have hD₂get : L₂.getD 0 ∅ = D₂ := headD_of_head? h₂head
  have hi₁ : L₁.length - 1 < L₁.length := by omega
  have hasD₁' : as ∈ L₁[L₁.length - 1] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, Option.getD_some] at hD₁get
    rw [hD₁get]
    exact hasD₁
  have hpw₁ := comps_pairwise h₁nd h₁c
  have hpw₂ := comps_pairwise h₂nd h₂c
  refine ⟨L₁.scanl symmDiff A ++ (L₂.scanl symmDiff C).tail, L₁.length, hW, ?_, hsub, h₁pos, by omega, ?_, ?_⟩
  · rw [hlen, helper_count 0 s e (by omega) hse hek, Nat.sub_zero]
  · intro t
    by_cases ht : t < L₁.length + L₂.length + 1
    · rw [htime cs hcsC (L₁.length - 1) hi₁ 0 h₂pos (by rw [hD₁get]; exact hcsD₁) (by rw [hD₂get]; exact hcsD₂)
        t ht]
      omega
    · rw [getD_eq_empty (by rw [hQlen]; omega)]
      simp only [Set.mem_empty_iff_false, false_iff]
      omega
  · intro t
    rw [List.getD_eq_getElem?_getD]
    by_cases htl : t < L₁.length + 1
    · have htl' : t < (L₁.scanl symmDiff A).length := by rw [List.length_scanl]; exact htl
      rw [List.getElem?_append_left htl', List.getElem?_eq_getElem htl', Option.getD_some,
        mem_scanl_symmDiff A L₁ hpw₁ htl', mem_take_comps h₁nd h₁c hi₁ hasD₁' t]
      simp only [hs, true_iff]
      omega
    · by_cases ht : t < L₁.length + L₂.length + 1
      · have htl' : (L₁.scanl symmDiff A).length ≤ t := by rw [List.length_scanl]; omega
        have hj : t - (L₁.scanl symmDiff A).length + 1 < (L₂.scanl symmDiff C).length := by
          rw [List.length_scanl, List.length_scanl]
          omega
        rw [List.getElem?_append_right htl', List.getElem?_tail, List.getElem?_eq_getElem hj, Option.getD_some,
          mem_scanl_symmDiff _ L₂ hpw₂ hj]
        simp only [hasC, false_iff, not_not]
        constructor
        · rintro ⟨D, hD, hasD⟩
          rcases ((h₂c D).1 (List.mem_of_mem_take hD)).2.1 hasD with h | h
          · exact absurd h hasC
          · exact absurd h hasB
        · intro h
          omega
      · rw [List.getElem?_eq_none (by rw [hQlen]; omega)]
        simp only [Option.getD_none, Set.mem_empty_iff_false, false_iff]
        omega

/-- The schedule of `Q` in Part 2: its first `K` moves, then its move `K + 1` together with move `μ` of `W'`, its move
`K + 2` together with move `ν`, and its other moves after `W'`. (`W'` follows `jW K n` of Junction.lean.) -/
def hjV (K μ ν n t : ℕ) : ℕ :=
  if t ≤ K then t else if t < K + μ then K else if t < K + ν then K + 1 else if t ≤ K + n then K + 2
  else K + 2 + (t - K - n)

/-- Part 2 of Lemma 4.12: merge `W'` (columns `≤ i - 1`, timed at column `i - 1`) with the walk of `comb_first` on the
columns `i, …, e`. The only comparable pairs across the two walks are `c_{i-1}, a_i` and `a_{i-1}, c_i`. -/
theorem part2 {i e : ℕ} (hi : 1 ≤ i) (hie : i ≤ e) (hek : e < k)
    {W' : List (Set (Band k))} {A₁ B₁ : Set (Band k)} (hW : IsWalkFromTo W' A₁ B₁)
    (hcols : ∀ X ∈ W', ∀ x ∈ X, x.1.val ≤ i - 1) {μ ν : ℕ} (hT : HJTimed W' ⟨i - 1, by omega⟩ μ ν)
    {A B : Set (Band k)} (hAB : IsSplit A B (rowSeg 0 i e)) (hs : a (⟨i, by omega⟩ : Fin k) ∈ A) :
    ∃ W'', IsWalkFromTo W'' (A₁ ∪ A) (B₁ ∪ B) ∧ W''.length - 1 = (W'.length - 1) + (e - i + 2) / 2 - 1 ∧
      ∀ X ∈ W'', ∀ x ∈ X, x.1.val ≤ e := by
  obtain ⟨Q, κ, hQ, hQlen, hQsub, hκ1, hκℓ, hcT, haT⟩ := comb_first i e hie hek A B hAB hs
  obtain ⟨hμ1, hμν, hνn, hc1, hc2, ha1, ha2⟩ := hT
  set q : Fin k := ⟨i - 1, by omega⟩ with hq
  set ai : Band k := a (⟨i, by omega⟩ : Fin k) with hai
  set ci : Band k := c (⟨i, by omega⟩ : Fin k) with hci
  have hqi : (⟨i, by omega⟩ : Fin k).val = q.val + 1 := by simp only [hq]; omega
  have hWlen := List.length_pos_of_ne_nil hW.1.1
  set n := W'.length - 1 with hn
  set ℓ := Q.length - 1 with hℓ
  set K := κ - 1 with hK
  have hQc : ∀ Y ∈ Q, ∀ y ∈ Y, i ≤ y.1.val ∧ y.1.val ≤ e ∧ y.2 ≠ 1 := by
    intro Y hY y hy
    rcases hQsub Y hY hy with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2, -⟩
    · exact ⟨h1, h2, by rw [h0]; decide⟩
    · exact ⟨h1, h2, by rw [h0]; decide⟩
  have hw0 : jW K n 0 = 0 := by unfold jW; split_ifs <;> omega
  have hv0 : hjV K μ ν n 0 = 0 := by unfold hjV; split_ifs <;> omega
  have hwM : jW K n (n + ℓ - 2) = W'.length - 1 := by unfold jW; split_ifs <;> omega
  have hvM : hjV K μ ν n (n + ℓ - 2) = Q.length - 1 := by unfold hjV; split_ifs <;> omega
  have hws : ∀ t < n + ℓ - 2, jW K n (t + 1) = jW K n t ∨ jW K n (t + 1) = jW K n t + 1 := by
    intro t ht; unfold jW; split_ifs <;> omega
  have hvs : ∀ t < n + ℓ - 2,
      hjV K μ ν n (t + 1) = hjV K μ ν n t ∨ hjV K μ ν n (t + 1) = hjV K μ ν n t + 1 := by
    intro t ht; unfold hjV; split_ifs <;> omega
  have hmove : ∀ t < n + ℓ - 2, jW K n (t + 1) = jW K n t + 1 ∨ hjV K μ ν n (t + 1) = hjV K μ ν n t + 1 := by
    intro t ht; unfold jW hjV; split_ifs <;> omega
  have hdisj : ∀ X ∈ W', ∀ Y ∈ Q, Disjoint X Y := fun X hX Y hY =>
    Set.disjoint_left.2 fun x hxX hxY => by
      have := hcols X hX x hxX
      have := (hQc Y hY x hxY).1
      omega
  have hanti : ∀ t ≤ n + ℓ - 2, ∀ x ∈ W'.getD (jW K n t) ∅, ∀ y ∈ Q.getD (hjV K μ ν n t) ∅, ¬ Comp x y := by
    intro t ht x hx y hy hxy
    obtain ⟨X, hX, hxX⟩ := mem_of_mem_getD hx
    obtain ⟨Y, hY, hyY⟩ := mem_of_mem_getD hy
    have hxc := hcols X hX x hxX
    obtain ⟨hy1, -, hy2⟩ := hQc Y hY y hyY
    have hcomp := hxy
    rw [comp_iff_val] at hcomp
    have hx2 := x.2.isLt
    have hy2' := y.2.isLt
    have hy2v : y.2.val ≠ 1 := fun h => hy2 (Fin.ext h)
    have key : x.1.val = i - 1 ∧ y.1.val = i ∧
        ((x.2.val = 2 ∧ y.2.val = 0) ∨ (x.2.val = 0 ∧ y.2.val = 2)) := by omega
    obtain ⟨hx1, hy1', hrows⟩ := key
    rcases hrows with ⟨hxr, hyr⟩ | ⟨hxr, hyr⟩
    · have hxe : x = c q := Prod.ext (Fin.ext hx1) (Fin.ext hxr)
      have hye : y = ai := Prod.ext (Fin.ext hy1') (Fin.ext hyr)
      rw [hxe] at hx
      rw [hye, haT] at hy
      have h1 := hc1 _ hx
      unfold jW at h1
      unfold hjV at hy
      split_ifs at h1 hy <;> omega
    · have hxe : x = a q := Prod.ext (Fin.ext hx1) (Fin.ext hxr)
      have hye : y = ci := Prod.ext (Fin.ext hy1') (Fin.ext hyr)
      rw [hxe] at hx
      rw [hye, hcT] at hy
      have h1 := ha1 _ hx
      unfold jW at h1
      unfold hjV at hy
      split_ifs at h1 hy <;> omega
  have hboth : ∀ t < n + ℓ - 2, jW K n (t + 1) = jW K n t + 1 → hjV K μ ν n (t + 1) = hjV K μ ν n t + 1 →
      ∃ x ∈ symmDiff (W'.getD (jW K n t) ∅) (W'.getD (jW K n t + 1) ∅),
        ∃ y ∈ symmDiff (Q.getD (hjV K μ ν n t) ∅) (Q.getD (hjV K μ ν n t + 1) ∅), Comp x y := by
    intro t ht hw hv
    have ht' : t + 1 = K + μ ∨ t + 1 = K + ν := by
      unfold jW at hw
      unfold hjV at hv
      split_ifs at hw hv <;> omega
    rcases ht' with h1 | h1
    · have e1 : jW K n t = μ - 1 := by unfold jW; split_ifs <;> omega
      have e2 : hjV K μ ν n t = K := by unfold hjV; split_ifs <;> omega
      rw [e1, e2, Nat.sub_add_cancel hμ1]
      refine ⟨c q, Set.mem_symmDiff.2 (Or.inr ⟨hc2, fun h => ?_⟩), ai,
        Set.mem_symmDiff.2 (Or.inl ⟨(haT K).2 (by omega), fun h => ?_⟩), comp_ca_next hqi⟩
      · have := hc1 _ h
        omega
      · have := (haT (K + 1)).1 h
        omega
    · have e1 : jW K n t = ν - 1 := by unfold jW; split_ifs <;> omega
      have e2 : hjV K μ ν n t = K + 1 := by unfold hjV; split_ifs <;> omega
      rw [e1, e2, Nat.sub_add_cancel (by omega : 1 ≤ ν)]
      refine ⟨a q, Set.mem_symmDiff.2 (Or.inr ⟨ha2, fun h => ?_⟩), ci,
        Set.mem_symmDiff.2 (Or.inl ⟨(hcT (K + 1)).2 (by omega), fun h => ?_⟩), comp_ac_next hqi⟩
      · have := ha1 _ h
        omega
      · have := (hcT (K + 1 + 1)).1 h
        omega
  refine ⟨merge2 W' Q (jW K n) (hjV K μ ν n) (n + ℓ - 2),
    merge2_walk hW hQ hw0 hv0 hwM hvM hws hvs hmove hdisj hanti hboth, by rw [merge2_length]; omega, ?_⟩
  intro X hX x hx
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hX
  rcases hx with hx | hx
  · obtain ⟨X', hX', hx'⟩ := mem_of_mem_getD hx
    have := hcols X' hX' x hx'
    omega
  · obtain ⟨Y, hY, hy⟩ := mem_of_mem_getD hx
    exact (hQc Y hY x hy).2.1

/-! ### Lemma 4.12 -/

/-- A walk between middle sets that is tame at `p` can be replaced by one with a prescribed row of its outer element
of column `p` (by `σ`, which fixes the initial and final sets). -/
theorem tame_prescribe {p : Fin k} {W : List (Set (Band k))} {A' B' : Set (Band k)} {h : Band k}
    (hW : IsWalkFromTo W A' B') (hT : IsTameAt W p h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1) (r : Fin 3) (hr : r ≠ 1) :
    ∃ W₀ : List (Set (Band k)), IsWalkFromTo W₀ A' B' ∧ W₀.length = W.length ∧ IsTameAt W₀ p (p, r) := by
  have hh : h = (p, h.2) := Prod.ext hT.2.1 rfl
  by_cases hhr : h.2 = r
  · refine ⟨W, hW, rfl, ?_⟩
    rw [← hhr, ← hh]
    exact hT
  · obtain ⟨-, hσT, hσW⟩ := tame_symm W hW.1 p h hT
    refine ⟨W.map (sigmaAC '' ·), hσW A' B' hW hmid, List.length_map _, ?_⟩
    have hσh : sigmaAC h = (p, r) := by
      apply Prod.ext hT.2.1
      apply Fin.ext
      rw [sigma_snd_val]
      have hrv : r.val ≠ 1 := fun h' => hr (Fin.ext h')
      have hhv : h.2.val ≠ 1 := fun h' => hT.2.2.1 (Fin.ext h')
      have hne : h.2.val ≠ r.val := fun h' => hhr (Fin.ext h')
      have hrl := r.isLt
      have hhl := h.2.isLt
      show 2 - h.2.val = r.val
      omega
    rw [← hσh]
    exact hσT

/-- Lemma 4.12 in row `a`, when `a_i` is initial: Part 1 by `part1_init` or `part1_final` (after prescribing the row of
the outer element of column `i - 2` of `W`), then Part 2 by `part2`. -/
theorem half_core {i j : ℕ} (hi : 2 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} {h : Band k} (hW : IsWalkFromTo W A' B')
    (hT : IsTameAt W ⟨i - 2, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    {A'' B'' : Set (Band k)} (hAB : IsSplit A'' B'' (insert (b ⟨i - 1, by omega⟩) (rowSeg 0 i (i + j - 1))))
    (hfirst : a (⟨i, by omega⟩ : Fin k) ∈ A'') :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + (j + 1) / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  set p : Fin k := ⟨i - 2, by omega⟩ with hp
  set q : Fin k := ⟨i - 1, by omega⟩ with hq
  have hpq : q.val = p.val + 1 := by simp only [hp, hq]; omega
  set S : Set (Band k) := rowSeg 0 i (i + j - 1) with hS
  obtain ⟨hdis, hU, -⟩ := hAB
  have hbS : b q ∉ S := fun h => absurd h.1 (by show ¬ ((1 : Fin 3) = 0); decide)
  have hSanti : IsAntichainSet S := isAntichainSet_row 0 _ fun x hx => hx.1
  have hab : a (⟨i, by omega⟩ : Fin k) ≠ b q := a_ne_b _ _
  have hins : ∀ x, x ∈ A'' ∪ B'' ↔ x = b q ∨ x ∈ S := fun x => by rw [hU]; rfl
  have hbmem : b q ∈ A'' ∪ B'' := (hins _).2 (Or.inl rfl)
  rcases hbmem with hbA | hbB
  · obtain ⟨W₀, hW₀, hW₀len, hT₀⟩ := tame_prescribe hW hT hmid 2 (by decide)
    obtain ⟨W', μ', ν', hW', hW'len, hW'cols, hW'T⟩ := part1_init hpq hW₀ hT₀
    have hsplit : IsSplit (A'' \ {b q}) B'' S := by
      refine ⟨Set.disjoint_of_subset_left (fun x hx => hx.1) hdis, ?_, hSanti⟩
      ext x
      constructor
      · rintro (⟨hxA, hxb⟩ | hxB)
        · rcases (hins x).1 (Or.inl hxA) with hx | hx
          · exact absurd (Set.mem_singleton_iff.2 hx) hxb
          · exact hx
        · rcases (hins x).1 (Or.inr hxB) with hx | hx
          · rw [hx] at hxB
            exact absurd hxB (Set.disjoint_left.1 hdis hbA)
          · exact hx
      · intro hx
        rcases (hins x).2 (Or.inr hx) with h | h
        · refine Or.inl ⟨h, fun h' => hbS ?_⟩
          rw [Set.mem_singleton_iff.1 h'] at hx
          exact hx
        · exact Or.inr h
    obtain ⟨W'', hW'', hW''len, hW''cols⟩ := part2 (i := i) (e := i + j - 1) (by omega) (by omega) (by omega)
      hW' hW'cols hW'T hsplit ⟨hfirst, fun h' => hab (Set.mem_singleton_iff.1 h')⟩
    have hAeq : A' ∪ {b q} ∪ (A'' \ {b q}) = A' ∪ A'' := by
      ext x
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff]
      constructor
      · rintro ((hx | hx) | ⟨hx, -⟩)
        · exact Or.inl hx
        · rw [hx]
          exact Or.inr hbA
        · exact Or.inr hx
      · rintro (hx | hx)
        · exact Or.inl (Or.inl hx)
        · by_cases hxb : x = b q
          · exact Or.inl (Or.inr hxb)
          · exact Or.inr ⟨hx, hxb⟩
    rw [hAeq] at hW''
    refine ⟨W'', hW'', by omega, fun X hX x hx => ?_⟩
    have := hW''cols X hX x hx
    omega
  · obtain ⟨W₀, hW₀, hW₀len, hT₀⟩ := tame_prescribe hW hT hmid 0 (by decide)
    obtain ⟨W', μ', ν', hW', hW'len, hW'cols, hW'T⟩ := part1_final hpq hW₀ hT₀
    have hsplit : IsSplit A'' (B'' \ {b q}) S := by
      refine ⟨Set.disjoint_of_subset_right (fun x hx => hx.1) hdis, ?_, hSanti⟩
      ext x
      constructor
      · rintro (hxA | ⟨hxB, hxb⟩)
        · rcases (hins x).1 (Or.inl hxA) with hx | hx
          · rw [hx] at hxA
            exact absurd hbB (Set.disjoint_left.1 hdis hxA)
          · exact hx
        · rcases (hins x).1 (Or.inr hxB) with hx | hx
          · exact absurd (Set.mem_singleton_iff.2 hx) hxb
          · exact hx
      · intro hx
        rcases (hins x).2 (Or.inr hx) with h | h
        · exact Or.inl h
        · refine Or.inr ⟨h, fun h' => hbS ?_⟩
          rw [Set.mem_singleton_iff.1 h'] at hx
          exact hx
    obtain ⟨W'', hW'', hW''len, hW''cols⟩ := part2 (i := i) (e := i + j - 1) (by omega) (by omega) (by omega)
      hW' hW'cols hW'T hsplit hfirst
    have hBeq : B' ∪ {b q} ∪ (B'' \ {b q}) = B' ∪ B'' := by
      ext x
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff]
      constructor
      · rintro ((hx | hx) | ⟨hx, -⟩)
        · exact Or.inl hx
        · rw [hx]
          exact Or.inr hbB
        · exact Or.inr hx
      · rintro (hx | hx)
        · exact Or.inl (Or.inl hx)
        · by_cases hxb : x = b q
          · exact Or.inl (Or.inr hxb)
          · exact Or.inr ⟨hx, hxb⟩
    rw [hBeq] at hW''
    refine ⟨W'', hW'', by omega, fun X hX x hx => ?_⟩
    have := hW''cols X hX x hx
    omega

/-- Lemma 4.12 in row `a` (by reversal, `a_i` may be assumed initial). -/
theorem half_row_a {i j : ℕ} (hi : 2 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k)
    {W : List (Set (Band k))} {A' B' : Set (Band k)} {h : Band k} (hW : IsWalkFromTo W A' B')
    (hT : IsTameAt W ⟨i - 2, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    {A'' B'' : Set (Band k)} (hAB : IsSplit A'' B'' (insert (b ⟨i - 1, by omega⟩) (rowSeg 0 i (i + j - 1)))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + (j + 1) / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  have hmem : a (⟨i, by omega⟩ : Fin k) ∈ A'' ∪ B'' := by
    rw [hAB.2.1]
    exact Or.inr ⟨rfl, le_rfl, by show i ≤ i + j - 1; omega⟩
  rcases hmem with hA | hB
  · exact half_core hi hj hL hW hT hmid hAB hA
  · have hmid' : ∀ x ∈ B' ∪ A', x.2 = 1 := fun x hx => hmid x (Set.union_comm B' A' ▸ hx)
    have hAB' : IsSplit B'' A'' (insert (b ⟨i - 1, by omega⟩) (rowSeg 0 i (i + j - 1))) :=
      ⟨hAB.1.symm, by rw [Set.union_comm]; exact hAB.2.1, hAB.2.2⟩
    obtain ⟨W', h1, h2, h3⟩ := half_core hi hj hL (isWalkFromTo_reverse hW) (tame_reverse hT) hmid' hAB' hB
    exact ⟨W'.reverse, isWalkFromTo_reverse h1, by rw [List.length_reverse, h2, List.length_reverse],
      fun X hX => h3 X (List.mem_reverse.1 hX)⟩

/-- Lemma 4.12 (half junction), in the statement form of Sec4/Chain.lean `lem_4_12` (row `c` by `σ`). -/
theorem half_junction (i j : ℕ) (hi : 2 ≤ i) (hj : 1 ≤ j) (hL : i + j ≤ k) (r : Fin 3) (hr : r ≠ 1)
    (W : List (Set (Band k))) (A' B' : Set (Band k)) (h : Band k) (hW : IsWalkFromTo W A' B')
    (hT : IsTameAt W ⟨i - 2, by omega⟩ h) (hmid : ∀ x ∈ A' ∪ B', x.2 = 1)
    (A'' B'' : Set (Band k)) (hAB : IsSplit A'' B'' (insert (b ⟨i - 1, by omega⟩) (rowSeg r i (i + j - 1)))) :
    ∃ W', IsWalkFromTo W' (A' ∪ A'') (B' ∪ B'') ∧ W'.length - 1 = (W.length - 1) + (j + 1) / 2 ∧
      ∀ X ∈ W', ∀ x ∈ X, x.1.val < i + j := by
  have hr' : r = 0 ∨ r = 2 := by
    have h := r.isLt
    have h1 : r.val ≠ 1 := fun h' => hr (Fin.ext h')
    rcases (by omega : r.val = 0 ∨ r.val = 2) with h0 | h2
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h2)
  rcases hr' with rfl | rfl
  · exact half_row_a hi hj hL hW hT hmid hAB
  · obtain ⟨-, hσT, hσW⟩ := tame_symm W hW.1 _ h hT
    obtain ⟨hdis, hU, hanti⟩ := hAB
    have himg : sigmaAC '' (insert (b ⟨i - 1, by omega⟩) (rowSeg 2 i (i + j - 1)) : Set (Band k)) =
        insert (b ⟨i - 1, by omega⟩) (rowSeg 0 i (i + j - 1)) := by
      rw [Set.image_insert_eq, sigma_mid (x := b ⟨i - 1, by omega⟩) rfl, sigma_rowSeg]
    have hAB' : IsSplit (sigmaAC '' A'') (sigmaAC '' B'') (insert (b ⟨i - 1, by omega⟩) (rowSeg 0 i (i + j - 1))) :=
      ⟨(Set.disjoint_image_iff sigma_injective).2 hdis, by rw [← Set.image_union, hU, himg],
        by rw [← himg]; exact (isAntichainSet_image_iff sigmaAC sigma_comp_iff _).2 hanti⟩
    obtain ⟨W', h1, h2, h3⟩ := half_row_a hi hj hL (hσW A' B' hW hmid) hσT hmid hAB'
    refine ⟨W'.map (sigmaAC '' ·), ⟨isWalk_map sigmaAC sigma_injective sigma_comp_iff W' h1.1, ?_, ?_⟩, ?_, ?_⟩
    · rw [List.head?_map, h1.2.1, Option.map_some, Set.image_union,
        sigma_image_mid (fun x hx => hmid x (Or.inl hx)), sigma_image_image]
    · rw [List.getLast?_map, h1.2.2, Option.map_some, Set.image_union,
        sigma_image_mid (fun x hx => hmid x (Or.inr hx)), sigma_image_image]
    · rw [List.length_map, h2, List.length_map]
    · intro X hX x hx
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      obtain ⟨y, hy, rfl⟩ := hx
      exact h3 Y hY y hy

end HalfJunction

end LeeDiam.S4

