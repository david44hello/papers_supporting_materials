/-
HibiLi/Proofs/LU.lean — the functions L and U of a switch: 0 ≤ L ≤ U ≤ 1 on B, L convex, U concave (paper 240–242).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import HibiLi.Defs.Switch

namespace HibiLi.Proofs

open HibiLi Finset

variable {P : Type*} [Fintype P] [PartialOrder P] (s : Switch P)

lemma chainSum_add_smul (K : Finset s.P') (x y : s.P' → ℝ) (a b : ℝ) :
    s.chainSum K (a • x + b • y) = a * s.chainSum K x + b * s.chainSum K y := by
  simp [Switch.chainSum, sum_add_distrib, mul_sum]

lemma upVal_add_smul (j : Option s.P') (x y : s.P' → ℝ) (a b : ℝ) (hab : a + b = 1) :
    s.upVal j (a • x + b • y) = a * s.upVal j x + b * s.upVal j y := by
  cases j with
  | none => simp only [Switch.upVal]; linarith
  | some r => simp [Switch.upVal]

lemma chainSum_le_L {K : Finset s.P'} (hK : K ∈ s.lowBranches) (u : s.P' → ℝ) : s.chainSum K u ≤ s.L u :=
  le_sup' (fun K => s.chainSum K u) hK

lemma U_le_upVal {j : Option s.P'} (hj : j ∈ s.upBranches) (u : s.P' → ℝ) : s.U u ≤ s.upVal j u :=
  inf'_le (fun j => s.upVal j u) hj

/-- `L` is convex (a maximum of linear functions). -/
lemma L_convex : ConvexOn ℝ Set.univ s.L := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  refine sup'_le _ _ fun K hK => ?_
  rw [chainSum_add_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (chainSum_le_L s hK x) ha)
    (mul_le_mul_of_nonneg_left (chainSum_le_L s hK y) hb)

/-- `U` is concave (a minimum of affine functions). -/
lemma U_concave : ConcaveOn ℝ Set.univ s.U := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  refine le_inf' _ _ fun j hj => ?_
  rw [upVal_add_smul s j x y a b hab]
  exact add_le_add (mul_le_mul_of_nonneg_left (U_le_upVal s hj x) ha)
    (mul_le_mul_of_nonneg_left (U_le_upVal s hj y) hb)

/-- Every element strictly above `q` lies outside `I` (no element of `I` is above `q`). -/
lemma not_mem_I_of_gt {r : P} (hr : s.q < r) : r ∉ s.I := fun hrI => s.q_notMem (s.isLowerSet hr.le hrI)

/-- On `B`: `0 ≤ L ≤ U ≤ 1` (Fourier §3). -/
lemma L_U_bounds {u : s.P' → ℝ} (hu : u ∈ s.B) : 0 ≤ s.L u ∧ s.L u ≤ s.U u ∧ s.U u ≤ 1 := by
  classical
  obtain ⟨_, _, _, h4, h5⟩ := hu
  refine ⟨?_, ?_, ?_⟩
  · have h0 : (∅ : Finset s.P') ∈ s.lowBranches := by simp [Switch.lowBranches, IsChainSet]
    simpa [Switch.chainSum] using chainSum_le_L s h0 u
  · refine sup'_le _ _ fun K hK => le_inf' _ _ fun j hj => ?_
    simp only [Switch.lowBranches, mem_filter, mem_univ, true_and] at hK
    obtain ⟨hKI, hKc, hKq⟩ := hK
    cases j with
    | none => exact h5 K hKI hKc
    | some r =>
      simp only [Switch.upBranches, mem_insert, reduceCtorEq, mem_image, mem_filter, mem_univ, true_and,
        Option.some.injEq, false_or] at hj
      obtain ⟨r', hr', rfl⟩ := hj
      exact h4 r' (not_mem_I_of_gt s hr') K hKI hKc (fun p hp => (show p.1 < r'.1 from lt_trans (hKq p hp) hr'))
  · have hnone : (none : Option s.P') ∈ s.upBranches := by simp [Switch.upBranches]
    simpa [Switch.upVal] using U_le_upVal s hnone u

end HibiLi.Proofs
