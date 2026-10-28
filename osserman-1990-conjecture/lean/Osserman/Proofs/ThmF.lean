/-
ThmF.lean — Theorem F of paper 013 (thm:E, sec_small_roots.tex of the posting copy, lines 6-14 and 315): rows thm_F,
thm_F_nine_patterns, thm_F_nine_patterns_tensor, hasPattern_iff_patternEv.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Premise rows of thm_F (leading arguments with their exact types): s8_3_pattern_clifford (`S85.Pat83Hyp`),
s8_4_pattern_clifford, s8_5_pattern_clifford, s8_6_clifford (abbrevs below).
Proof. thm_F is the assembly of §8.3-8.6 ("This proves Theorem E", line 315). The nine patterns: a multiset with sum 15,
one entry `M ∈ {7, 8}` and the others 1 or 2 is `M` plus `a` ones and `b` twos with `a + 2b = 15 - M`; the solutions are
the nine listed. For a tensor with a full pattern, the eigenvalue of multiplicity `M` is one of the listed ones, and the
second hypothesis says exactly that every other listed multiplicity is at most two.
-/
import Osserman.Proofs.S85Ends

namespace Osserman.Proofs.ThmF

open Osserman Matrix

/-- The type of row `s8_4_pattern_clifford`. -/
abbrev Pat84Hyp : Prop :=
  ∀ (R : CurvTensor 16) (_h : HasPattern R ![7, 5, 2, 1] ∨ HasPattern R ![8, 4, 2, 1]), R.IsClifford

/-- The type of row `s8_5_pattern_clifford`. -/
abbrev Pat85Hyp : Prop :=
  ∀ (R : CurvTensor 16) (_h : HasPattern R ![7, 5, 1, 1, 1] ∨ HasPattern R ![8, 4, 1, 1, 1]), R.IsClifford

/-- The type of row `s8_6_clifford`. -/
abbrev Six86Hyp : Prop := ∀ (R : CurvTensor 16) (μ0 : ℝ) (M : ℕ) (_h : SmallMultHyp R μ0 M), R.IsClifford

/-- Row `hasPattern_iff_patternEv`: the two definitions have the same body. -/
theorem hasPattern_iff_patternEv_proved {n k : ℕ} (R : CurvTensor n) (m : Fin k → ℕ) :
    HasPattern R m ↔ ∃ ev, PatternEv R m ev :=
  Iff.rfl

/-- **Theorem F** (lines 6-14, 315), row `thm_F`. -/
theorem thm_F_proved (h83 : S85.Pat83Hyp) (h84 : Pat84Hyp) (h85 : Pat85Hyp) (h86 : Six86Hyp)
    (R : CurvTensor 16) (_hO : R.IsOsserman)
    (h : HasPattern R ![7, 6, 1, 1] ∨ HasPattern R ![8, 5, 1, 1] ∨ HasPattern R ![7, 5, 2, 1] ∨
      HasPattern R ![8, 4, 2, 1] ∨ HasPattern R ![7, 5, 1, 1, 1] ∨ HasPattern R ![8, 4, 1, 1, 1] ∨
      ∃ μ0 : ℝ, ∃ M : ℕ, SmallMultHyp R μ0 M) :
    R.IsClifford := by
  rcases h with h | h | h | h | h | h | ⟨μ0, M, h⟩
  · exact h83 R (Or.inl h)
  · exact h83 R (Or.inr h)
  · exact h84 R (Or.inl h)
  · exact h84 R (Or.inr h)
  · exact h85 R (Or.inl h)
  · exact h85 R (Or.inr h)
  · exact h86 R μ0 M h

/-! ### The nine further patterns -/

/-- A multiset of ones and twos is `a` ones plus `b` twos. -/
lemma ones_twos (t : Multiset ℕ) (h : ∀ a ∈ t, a = 1 ∨ a = 2) :
    t = Multiset.replicate (t.count 1) 1 + Multiset.replicate (t.count 2) 2 := by
  ext n
  rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
  by_cases h1 : n = 1
  · subst h1
    simp
  by_cases h2 : n = 2
  · subst h2
    simp
  have hn : n ∉ t := fun hn => by rcases h n hn with rfl | rfl <;> contradiction
  rw [Multiset.count_eq_zero.mpr hn, ite_eq_right (Ne.symm h1), ite_eq_right (Ne.symm h2)]

lemma nine_char (s : Multiset ℕ) :
    (s.sum = 15 ∧ ∃ M ∈ ({7, 8} : Finset ℕ), M ∈ s ∧ ∀ a ∈ s.erase M, a = 1 ∨ a = 2) ↔
      s ∈ ([{7, 2, 2, 2, 2}, {7, 2, 2, 2, 1, 1}, {7, 2, 2, 1, 1, 1, 1}, {7, 2, 1, 1, 1, 1, 1, 1},
        {7, 1, 1, 1, 1, 1, 1, 1, 1}, {8, 2, 2, 2, 1}, {8, 2, 2, 1, 1, 1}, {8, 2, 1, 1, 1, 1, 1},
        {8, 1, 1, 1, 1, 1, 1, 1}] : List (Multiset ℕ)) := by
  constructor
  · rintro ⟨hsum, M, hM, hMs, hrest⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, s = M ::ₘ (Multiset.replicate a 1 + Multiset.replicate b 2) :=
      ⟨_, _, by rw [← ones_twos _ hrest, Multiset.cons_erase hMs]⟩
    simp only [Multiset.sum_cons, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hsum
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl
    · obtain rfl : a = 8 - 2 * b := by omega
      have hb : b ≤ 4 := by omega
      interval_cases b <;> decide
    · obtain rfl : a = 7 - 2 * b := by omega
      have hb : b ≤ 3 := by omega
      interval_cases b <;> decide
  · intro hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Theorem F** (lines 13-14), row `thm_F_nine_patterns`. -/
theorem thm_F_nine_patterns_proved :
    let six : List (Multiset ℕ) :=
      [{7, 6, 1, 1}, {8, 5, 1, 1}, {7, 5, 2, 1}, {8, 4, 2, 1}, {7, 5, 1, 1, 1}, {8, 4, 1, 1, 1}]
    let nine : List (Multiset ℕ) :=
      [{7, 2, 2, 2, 2}, {7, 2, 2, 2, 1, 1}, {7, 2, 2, 1, 1, 1, 1}, {7, 2, 1, 1, 1, 1, 1, 1},
        {7, 1, 1, 1, 1, 1, 1, 1, 1}, {8, 2, 2, 2, 1}, {8, 2, 2, 1, 1, 1}, {8, 2, 1, 1, 1, 1, 1},
        {8, 1, 1, 1, 1, 1, 1, 1}]
    (∀ s : Multiset ℕ,
        (s.sum = 15 ∧ ∃ M ∈ ({7, 8} : Finset ℕ), M ∈ s ∧ ∀ a ∈ s.erase M, a = 1 ∨ a = 2) ↔ s ∈ nine) ∧
      nine.Nodup ∧ nine.length = 9 ∧ ∀ s ∈ nine, s ∉ six := by
  intro six nine
  exact ⟨nine_char, by decide, rfl, by decide⟩

/-! ### The nine patterns for a tensor -/

lemma unit_e0 : (Pi.single 0 1 : Vec 16) ⬝ᵥ Pi.single 0 1 = 1 := by
  simp [dotProduct, Pi.single_apply]

/-- **Theorem F** (lines 13-14; S8.111), row `thm_F_nine_patterns_tensor`. -/
theorem thm_F_nine_patterns_tensor_proved {k : ℕ} (R : CurvTensor 16) (m : Fin k → ℕ) (hpat : HasPattern R m)
    (hpos : ∀ i, 0 < m i) (hsum : ∑ i, m i = 15) :
    (∃ μ0 : ℝ, ∃ M : ℕ, SmallMultHyp R μ0 M) ↔
      Finset.univ.val.map m ∈ ([{7, 2, 2, 2, 2}, {7, 2, 2, 2, 1, 1}, {7, 2, 2, 1, 1, 1, 1}, {7, 2, 1, 1, 1, 1, 1, 1},
        {7, 1, 1, 1, 1, 1, 1, 1, 1}, {8, 2, 2, 2, 1}, {8, 2, 2, 1, 1, 1}, {8, 2, 1, 1, 1, 1, 1},
        {8, 1, 1, 1, 1, 1, 1, 1}] : List (Multiset ℕ)) := by
  classical
  have hsum16 : ∑ i, m i + 1 = 16 := by omega
  obtain ⟨ev, hev, hm⟩ := hpat
  have hx := unit_e0
  -- removing the entry of `i0` from the multiset of `m`
  have herase (i0 : Fin k) :
      (Finset.univ.val.map m).erase (m i0) = (Finset.univ.val.erase i0).map m := by
    conv_lhs => rw [← Multiset.cons_erase (Finset.mem_val.mpr (Finset.mem_univ i0))]
    rw [Multiset.map_cons, Multiset.erase_cons_head]
  have hsumv : (Finset.univ.val.map m).sum = 15 := hsum
  rw [← nine_char]
  constructor
  · rintro ⟨μ0, M, hO, hM, hμ0, hle⟩
    -- `μ0` is a listed eigenvalue
    obtain ⟨i0, rfl⟩ : ∃ i0, ev i0 = μ0 := by
      by_contra hno
      have h0 := CorD.redMult_other R hev hsum16 hx (hm _ hx) (μ := μ0) fun i e => hno ⟨i, e.symm⟩
      have := hμ0 _ hx
      omega
    have hmi0 : m i0 = M := (hm _ hx i0).symm.trans (hμ0 _ hx)
    refine ⟨hsumv, M, by rcases hM with rfl | rfl <;> simp,
      by rw [← hmi0]; exact Multiset.mem_map_of_mem m (Finset.mem_val.mpr (Finset.mem_univ i0)), fun a ha => ?_⟩
    rw [← hmi0, herase i0] at ha
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp ha
    have hii0 : i ≠ i0 := ((Multiset.Nodup.mem_erase_iff Finset.univ.nodup).mp hi).1
    have h2 := hle _ hx (ev i) fun e => hii0 (hev e)
    rw [hm _ hx i] at h2
    have := hpos i
    omega
  · rintro ⟨-, M, hM, hMs, hrest⟩
    obtain ⟨i0, -, hi0⟩ := Multiset.mem_map.mp hMs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    have hO : R.IsOsserman := (CorD.hasPattern_osserman_proved R m hsum16 ⟨ev, hev, hm⟩).1
    refine ⟨ev i0, M, hO, hM, fun x hx' => (hm x hx' i0).trans hi0, fun x hx' μ hμ => ?_⟩
    by_cases hin : ∃ i, μ = ev i
    · obtain ⟨i, rfl⟩ := hin
      have hii0 : i ≠ i0 := fun e => hμ (congrArg ev e)
      have hmem : m i ∈ (Finset.univ.val.map m).erase M := by
        rw [← hi0, herase i0]
        exact Multiset.mem_map_of_mem m ((Multiset.mem_erase_of_ne hii0).mpr (Finset.mem_val.mpr (Finset.mem_univ i)))
      rw [hm x hx' i]
      rcases hrest _ hmem with h | h <;> omega
    · rw [CorD.redMult_other R hev hsum16 hx' (hm x hx') fun i e => hin ⟨i, e⟩]
      omega

end Osserman.Proofs.ThmF
