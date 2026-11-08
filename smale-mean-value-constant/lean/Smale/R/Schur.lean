/-
Smale/R/Schur.lean — The Schur-Cohn matrix of a coefficient sequence: its identity, and a common zero of P and P* makes it singular.
-/
import Mathlib

namespace Smale.RCheck

open Polynomial Complex ComplexConjugate Finset

/-- The Schur-Cohn (Bezout) matrix of `p_0, ..., p_m`:
`B_jk = Σ_{i ≤ min(j,k)} (p_{j-i} conj p_{k-i} - conj p_{m-j+i} p_{m-k+i})`, `j, k < m`. -/
noncomputable def schurB (m : ℕ) (p : ℕ → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun j k => ∑ i ∈ Finset.range (min (j : ℕ) (k : ℕ) + 1),
    (p ((j : ℕ) - i) * conj (p ((k : ℕ) - i)) - conj (p (m - (j : ℕ) + i)) * p (m - (k : ℕ) + i))

section helpers

variable {R : Type*} [CommRing R] (σ : R →+* R) (m : ℕ) (p : ℕ → R)

/-- One term of the recursion. -/
noncomputable def aT (j k : ℕ) : R := p j * σ (p k) - σ (p (m - j)) * p (m - k)

/-- `B_jk` for all natural `j, k`. -/
noncomputable def bF (j k : ℕ) : R := ∑ i ∈ range (min j k + 1), aT σ m p (j - i) (k - i)

theorem bF_succ (j k : ℕ) : bF σ m p (j + 1) (k + 1) = aT σ m p (j + 1) (k + 1) + bF σ m p j k := by
  unfold bF
  have h : min (j + 1) (k + 1) + 1 = (min j k + 1) + 1 := by omega
  rw [h, sum_range_succ', add_comm]
  simp only [Nat.add_sub_add_right, Nat.sub_zero]

theorem bF_zero_left (k : ℕ) : bF σ m p 0 k = aT σ m p 0 k := by
  simp [bF]

theorem bF_zero_right (j : ℕ) : bF σ m p j 0 = aT σ m p j 0 := by
  simp [bF]

/-- The row `j = m` vanishes: the two halves are the same sum, reflected. -/
theorem bF_top_left (k : ℕ) (hk : k ≤ m) : bF σ m p m k = 0 := by
  unfold bF
  have hmin : min m k = k := min_eq_right hk
  rw [hmin]
  have hterm : ∀ i ∈ range (k + 1), aT σ m p (m - i) (k - i) =
      (fun i => σ (p i) * p (m - k + i)) (k + 1 - 1 - i) - (fun i => σ (p i) * p (m - k + i)) i := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have h1 : m - (m - i) = i := by omega
    have h2 : m - (k - i) = m - k + i := by omega
    have h3 : m - k + (k - i) = m - i := by omega
    have h4 : k + 1 - 1 - i = k - i := by omega
    simp only [aT, h1, h2, h3, h4]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_range_reflect (fun i => σ (p i) * p (m - k + i)) (k + 1), sub_self]

/-- The column `k = m` vanishes. -/
theorem bF_top_right (j : ℕ) (hj : j ≤ m) : bF σ m p j m = 0 := by
  unfold bF
  have hmin : min j m = j := min_eq_left hj
  rw [hmin]
  have hterm : ∀ i ∈ range (j + 1), aT σ m p (j - i) (m - i) =
      (fun i => σ (p (m - j + i)) * p i) (j + 1 - 1 - i) - (fun i => σ (p (m - j + i)) * p i) i := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (mem_range.1 hi)
    have h1 : m - (j - i) = m - j + i := by omega
    have h2 : m - (m - i) = i := by omega
    have h3 : m - j + (j - i) = m - i := by omega
    have h4 : j + 1 - 1 - i = j - i := by omega
    simp only [aT, h1, h2, h3, h4]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_range_reflect (fun i => σ (p (m - j + i)) * p i) (j + 1), sub_self]

/-- A ring map carries `bF` to `bF`. -/
theorem bF_map {S : Type*} [CommRing S] (σ' : S →+* S) (φ : R →+* S) (hφ : ∀ x, φ (σ x) = σ' (φ x)) (j k : ℕ) :
    φ (bF σ m p j k) = bF σ' m (fun l => φ (p l)) j k := by
  simp only [bF, aT, map_sum, map_sub, map_mul, hφ]

/-- The corner decomposition of a double sum. -/
theorem double_sum_corner (G : ℕ → ℕ → R) :
    ∑ j ∈ range (m + 1), ∑ k ∈ range (m + 1), G j k =
      ∑ j ∈ range m, ∑ k ∈ range m, G (j + 1) (k + 1) + ∑ j ∈ range m, G (j + 1) 0 +
        ∑ k ∈ range m, G 0 (k + 1) + G 0 0 := by
  simp only [sum_range_succ' _ m, sum_add_distrib]
  ring

/-- The telescoping identity, on natural indices. -/
theorem bF_telescope (w y : R) :
    (1 - w * y) * ∑ j ∈ range m, ∑ k ∈ range m, bF σ m p j k * w ^ j * y ^ k =
      ∑ j ∈ range (m + 1), ∑ k ∈ range (m + 1), aT σ m p j k * w ^ j * y ^ k := by
  have htop : ∑ j ∈ range (m + 1), ∑ k ∈ range (m + 1), bF σ m p j k * w ^ j * y ^ k =
      ∑ j ∈ range m, ∑ k ∈ range m, bF σ m p j k * w ^ j * y ^ k := by
    rw [sum_range_succ]
    have hrow : ∑ k ∈ range (m + 1), bF σ m p m k * w ^ m * y ^ k = 0 := by
      refine sum_eq_zero fun k hk => ?_
      rw [bF_top_left σ m p k (Nat.lt_succ_iff.1 (mem_range.1 hk))]
      ring
    rw [hrow, add_zero]
    refine sum_congr rfl fun j hj => ?_
    rw [sum_range_succ, bF_top_right σ m p j (mem_range.1 hj).le]
    ring
  rw [double_sum_corner m (fun j k => aT σ m p j k * w ^ j * y ^ k)]
  have hdec := double_sum_corner m (fun j k => bF σ m p j k * w ^ j * y ^ k)
  rw [htop] at hdec
  have h1 : ∑ j ∈ range m, ∑ k ∈ range m, aT σ m p (j + 1) (k + 1) * w ^ (j + 1) * y ^ (k + 1) =
      ∑ j ∈ range m, ∑ k ∈ range m, bF σ m p (j + 1) (k + 1) * w ^ (j + 1) * y ^ (k + 1) -
        w * y * ∑ j ∈ range m, ∑ k ∈ range m, bF σ m p j k * w ^ j * y ^ k := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [bF_succ]
    ring
  have h2 : ∑ j ∈ range m, aT σ m p (j + 1) 0 * w ^ (j + 1) * y ^ 0 =
      ∑ j ∈ range m, bF σ m p (j + 1) 0 * w ^ (j + 1) * y ^ 0 := by
    simp only [bF_zero_right]
  have h3 : ∑ k ∈ range m, aT σ m p 0 (k + 1) * w ^ 0 * y ^ (k + 1) =
      ∑ k ∈ range m, bF σ m p 0 (k + 1) * w ^ 0 * y ^ (k + 1) := by
    simp only [bF_zero_left]
  have h4 : aT σ m p 0 0 * w ^ 0 * y ^ 0 = bF σ m p 0 0 * w ^ 0 * y ^ 0 := by
    rw [bF_zero_left]
  rw [h1, h2, h3, h4]
  linear_combination hdec

/-- One row of `bF`, packed at `x`: the recursion the checker runs. -/
theorem bF_row_succ (x : R) (j : ℕ) (hj : j ≤ m) :
    ∑ k ∈ range (m + 1), bF σ m p (j + 1) k * x ^ k =
      (∑ k ∈ range (m + 1), bF σ m p j k * x ^ k) * x +
        p (j + 1) * ∑ k ∈ range (m + 1), σ (p k) * x ^ k -
        σ (p (m - (j + 1))) * ∑ k ∈ range (m + 1), p (m - k) * x ^ k := by
  have hdrop : ∑ k ∈ range (m + 1), bF σ m p j k * x ^ k = ∑ k ∈ range m, bF σ m p j k * x ^ k := by
    rw [sum_range_succ, bF_top_right σ m p j hj]
    ring
  rw [hdrop, mul_sum, mul_sum, sum_mul, sum_range_succ' (fun k => bF σ m p (j + 1) k * x ^ k) m]
  rw [sum_range_succ' (fun k => p (j + 1) * (σ (p k) * x ^ k)) m,
    sum_range_succ' (fun k => σ (p (m - (j + 1))) * (p (m - k) * x ^ k)) m]
  simp only [bF_succ, bF_zero_right, aT]
  simp only [add_mul, sub_mul, sum_add_distrib, sum_sub_distrib, pow_succ, pow_zero, mul_one, Nat.sub_zero]
  have hA : ∀ (k : ℕ), bF σ m p j k * (x ^ k * x) = bF σ m p j k * x ^ k * x := by
    intro k; ring
  simp only [hA]
  have hB : ∑ k ∈ range m, p (j + 1) * σ (p (k + 1)) * (x ^ k * x) =
      ∑ k ∈ range m, p (j + 1) * (σ (p (k + 1)) * (x ^ k * x)) :=
    sum_congr rfl fun k _ => by ring
  have hC : ∑ k ∈ range m, σ (p (m - (j + 1))) * p (m - (k + 1)) * (x ^ k * x) =
      ∑ k ∈ range m, σ (p (m - (j + 1))) * (p (m - (k + 1)) * (x ^ k * x)) :=
    sum_congr rfl fun k _ => by ring
  rw [hB, hC]
  ring

/-- The first row. -/
theorem bF_row_zero (x : R) :
    ∑ k ∈ range (m + 1), bF σ m p 0 k * x ^ k =
      p 0 * ∑ k ∈ range (m + 1), σ (p k) * x ^ k - σ (p (m - 0)) * ∑ k ∈ range (m + 1), p (m - k) * x ^ k := by
  simp only [bF_zero_left, aT, mul_sum, sub_mul, sum_sub_distrib, ← mul_assoc]

/-- The reflected coefficient sum of `P*`. -/
theorem star_reflect (q : ℕ → R) (w : R) :
    ∑ l ∈ range (m + 1), q l * w ^ (m - l) = ∑ j ∈ range (m + 1), q (m - j) * w ^ j := by
  rw [← sum_range_reflect (fun j => q (m - j) * w ^ j) (m + 1)]
  refine sum_congr rfl fun l hl => ?_
  have hl' : l ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hl)
  have h1 : m + 1 - 1 - l = m - l := by omega
  have h2 : m - (m - l) = l := by omega
  simp only [h1, h2]

end helpers

theorem schurB_apply (m : ℕ) (p : ℕ → ℂ) (j k : Fin m) :
    schurB m p j k = bF (starRingEnd ℂ) m p (j : ℕ) (k : ℕ) := by
  simp only [schurB, Matrix.of_apply, bF, aT]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ min (j : ℕ) (k : ℕ) := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hj : i ≤ (j : ℕ) := hi'.trans (min_le_left _ _)
  have hk : i ≤ (k : ℕ) := hi'.trans (min_le_right _ _)
  have h1 : m - ((j : ℕ) - i) = m - (j : ℕ) + i := by omega
  have h2 : m - ((k : ℕ) - i) = m - (k : ℕ) + i := by omega
  rw [h1, h2]

/-- The defining identity of `schurB`. -/
theorem schurB_identity (m : ℕ) (p : ℕ → ℂ) (w z : ℂ) :
    (1 - w * conj z) * ∑ j : Fin m, ∑ k : Fin m, schurB m p j k * w ^ (j : ℕ) * conj z ^ (k : ℕ) =
      (∑ l ∈ Finset.range (m + 1), p l * w ^ l) * conj (∑ l ∈ Finset.range (m + 1), p l * z ^ l) -
      (∑ l ∈ Finset.range (m + 1), conj (p l) * w ^ (m - l)) *
        conj (∑ l ∈ Finset.range (m + 1), conj (p l) * z ^ (m - l)) := by
  have hleft : ∑ j : Fin m, ∑ k : Fin m, schurB m p j k * w ^ (j : ℕ) * conj z ^ (k : ℕ) =
      ∑ j ∈ range m, ∑ k ∈ range m, bF (starRingEnd ℂ) m p j k * w ^ j * conj z ^ k := by
    simp only [schurB_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ k ∈ range m, bF (starRingEnd ℂ) m p j k * w ^ j * conj z ^ k) m]
    refine sum_congr rfl fun j _ => ?_
    exact Fin.sum_univ_eq_sum_range (fun k => bF (starRingEnd ℂ) m p (j : ℕ) k * w ^ (j : ℕ) * conj z ^ k) m
  rw [hleft, bF_telescope (starRingEnd ℂ)]
  have hstar : conj (∑ l ∈ range (m + 1), conj (p l) * z ^ (m - l)) =
      ∑ k ∈ range (m + 1), p (m - k) * conj z ^ k := by
    rw [map_sum, ← star_reflect m (fun l => p l) (conj z)]
    refine sum_congr rfl fun l _ => ?_
    simp [map_mul, map_pow]
  have hconj : conj (∑ l ∈ range (m + 1), p l * z ^ l) = ∑ k ∈ range (m + 1), conj (p k) * conj z ^ k := by
    rw [map_sum]
    refine sum_congr rfl fun l _ => ?_
    simp [map_mul, map_pow]
  rw [hstar, hconj, star_reflect m (fun l => conj (p l)) w, sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun k _ => ?_
  simp only [aT]
  ring

/-- A common zero of `P` and `P*`, anywhere in `ℂ`, makes `schurB` singular. -/
theorem schurB_det_eq_zero_of_common_zero (m : ℕ) (hm : 0 < m) (p : ℕ → ℂ) (w : ℂ)
    (h1 : ∑ l ∈ Finset.range (m + 1), p l * w ^ l = 0)
    (h2 : ∑ l ∈ Finset.range (m + 1), conj (p l) * w ^ (m - l) = 0) :
    (schurB m p).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun k => conj w ^ (k : ℕ), ?_, ?_⟩
  · intro h
    have h0 := congrFun h ⟨0, hm⟩
    simp at h0
  · set v : Fin m → ℂ := fun k => conj w ^ (k : ℕ) with hv
    let Q : ℂ[X] := ∑ j : Fin m, C ((schurB m p).mulVec v j) * X ^ (j : ℕ)
    have hQ : (1 - C (conj w) * X) * Q = 0 := by
      apply Polynomial.funext
      intro u
      have hid := schurB_identity m p u w
      rw [h1, h2, map_zero, mul_zero, mul_zero, sub_zero] at hid
      have hsum : Q.eval u = ∑ j : Fin m, ∑ k : Fin m, schurB m p j k * u ^ (j : ℕ) * conj w ^ (k : ℕ) := by
        simp only [Q, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Matrix.mulVec, dotProduct, hv]
        refine sum_congr rfl fun j _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun k _ => ?_
        ring
      simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_zero]
      rw [hsum, mul_comm (conj w) u]
      exact hid
    have hne : (1 - C (conj w) * X : ℂ[X]) ≠ 0 := by
      intro h
      have h0 := congrArg (fun q : ℂ[X] => q.coeff 0) h
      simp at h0
    have hQ0 : Q = 0 := (mul_eq_zero.1 hQ).resolve_left hne
    funext j
    have hc := congrArg (fun q : ℂ[X] => q.coeff (j : ℕ)) hQ0
    simp only [Q, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
    rw [sum_eq_single j] at hc
    · simpa using hc
    · intro b _ hb
      have hne' : (j : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [hne']
    · intro hj
      exact absurd (mem_univ j) hj

end Smale.RCheck
