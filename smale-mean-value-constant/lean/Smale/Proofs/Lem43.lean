/-
Smale/Proofs/Lem43.lean — a helper for Lemma 4.3 of paper 009: the Dieudonné polynomial `P_c` does not depend on
the formal degree `n` once `n ≥ deg H` (the terms with `ℓ ≥ deg H` have `h_{ℓ+1} = 0`).
-/
import Smale.Defs.Basic

namespace Smale

open Polynomial

/-- `P_c` does not depend on the formal degree `n` once `n ≥ deg H`. -/
theorem dieudonne_eq_natDegree (H : ℂ[X]) (n : ℕ) (hn : H.natDegree ≤ n) (c : ℝ) :
    dieudonne H n c = dieudonne H H.natDegree c := by
  unfold dieudonne
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  have hzero : ∑ l ∈ Finset.Ico H.natDegree n,
      C (H.coeff (l + 1) * (((Chebyshev.U ℝ (l : ℤ)).eval c : ℝ) : ℂ)) * X ^ l = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    have hl' := (Finset.mem_Ico.1 hl).1
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  rw [hzero, add_zero]

end Smale
