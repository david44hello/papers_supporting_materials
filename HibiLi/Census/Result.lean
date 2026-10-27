/-
HibiLi/Census/Result.lean — the n = 6 census sentence (paper v0.70, lines 736–737), assembled:
"For n=6, seven of the sixteen posets containing X attain the bound, P_6 among them".
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Census.Classify
import HibiLi.Census.FVectorsO
import HibiLi.Census.FVectorsC
import HibiLi.Proofs.FacePoly

namespace HibiLi.Census

open Polynomial

theorem fNum_order (i : Fin 16) (k : ℕ) (hk : k ≤ 6) :
    fNum (orderPolytope (censusPoset i)) k = (censusFO i).getD k 0 := by
  fin_cases i
  exacts [fNumO0 k hk, fNumO1 k hk, fNumO2 k hk, fNumO3 k hk, fNumO4 k hk, fNumO5 k hk, fNumO6 k hk, fNumO7 k hk, fNumO8 k hk, fNumO9 k hk, fNumO10 k hk, fNumO11 k hk, fNumO12 k hk, fNumO13 k hk, fNumO14 k hk, fNumO15 k hk]

theorem fNum_chain (i : Fin 16) (k : ℕ) (hk : k ≤ 6) :
    fNum (chainPolytope (censusPoset i)) k = (censusFC i).getD k 0 := by
  fin_cases i
  exacts [fNumC0 k hk, fNumC1 k hk, fNumC2 k hk, fNumC3 k hk, fNumC4 k hk, fNumC5 k hk, fNumC6 k hk, fNumC7 k hk, fNumC8 k hk, fNumC9 k hk, fNumC10 k hk, fNumC11 k hk, fNumC12 k hk, fNumC13 k hk, fNumC14 k hk, fNumC15 k hk]

/-- A census poset has no face of dimension above 6. -/
theorem fNum_eq_zero_of_six_lt (i : Fin 16) (Q : Set (censusPoset i → ℝ)) {k : ℕ} (hk : 6 < k) : fNum Q k = 0 :=
  Proofs.fNum_eq_zero_of_card_lt Q (by rw [card_censusPoset]; exact hk)

/-- `F_C − F_O = t²(1+t)³` iff the coefficients `f_k(C) − f_k(O)`, `k ≤ 6`, are those of `t²(1+t)³`. -/
theorem diff_eq_gap_iff (i : Fin 16) :
    facePoly (chainPolytope (censusPoset i)) - facePoly (orderPolytope (censusPoset i)) = gapPoly 6 ↔
      ∀ k < 7, (((censusFC i).getD k 0 : ℕ) : ℤ) - ((censusFO i).getD k 0 : ℕ) =
        if 2 ≤ k then (Nat.choose 3 (k - 2) : ℤ) else 0 := by
  constructor
  · intro h k hk
    have hc := congrArg (fun p => Polynomial.coeff p k) h
    simp only [coeff_sub, Proofs.facePoly_coeff, Proofs.gapPoly_coeff] at hc
    rw [fNum_order i k (by omega), fNum_chain i k (by omega)] at hc
    simpa using hc
  · intro h
    ext k
    simp only [coeff_sub, Proofs.facePoly_coeff, Proofs.gapPoly_coeff]
    by_cases hk : k ≤ 6
    · rw [fNum_order i k hk, fNum_chain i k hk]
      simpa using h k (by omega)
    · have h2 : 2 ≤ k := by omega
      have h3 : Nat.choose 3 (k - 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [fNum_eq_zero_of_six_lt i _ (by omega), fNum_eq_zero_of_six_lt i _ (by omega)]
      simp [h2, h3]

/-- Exactly the census rows 1–7 (`i < 7`) attain the bound. -/
theorem census_attain_iff (i : Fin 16) :
    facePoly (chainPolytope (censusPoset i)) - facePoly (orderPolytope (censusPoset i)) = gapPoly 6 ↔ i.val < 7 := by
  rw [diff_eq_gap_iff]
  revert i
  decide

/-- **Census sentence** (paper v0.70, lines 736–737),. -/
theorem sec5_census_n6_proved :
    (∀ i, Fintype.card (censusPoset i) = 6) ∧
    (∀ i, ContainsX (censusPoset i)) ∧
    (∀ i j, Nonempty (censusPoset i ≃o censusPoset j) → i = j) ∧
    (∀ (P : Type*) [Fintype P] [PartialOrder P], Fintype.card P = 6 → ContainsX P →
        ∃ i, Nonempty (P ≃o censusPoset i)) ∧
    (∃ S : Finset (Fin 16), S.card = 7 ∧ ∀ i, i ∈ S ↔
        facePoly (chainPolytope (censusPoset i)) - facePoly (orderPolytope (censusPoset i)) = gapPoly 6) ∧
    (∃ i, Nonempty (censusPoset i ≃o sharpFamily 1) ∧
        facePoly (chainPolytope (censusPoset i)) - facePoly (orderPolytope (censusPoset i)) = gapPoly 6) := by
  refine ⟨census_card, census_containsX, fun i j h => census_iso_eq h,
    fun P _ _ hcard hX => census_complete P hcard hX, ?_, ⟨4, census_iso_sharp, (census_attain_iff 4).2 (by decide)⟩⟩
  refine ⟨Finset.univ.filter fun i : Fin 16 => i.val < 7, by decide, fun i => ?_⟩
  rw [census_attain_iff]
  simp

end HibiLi.Census
