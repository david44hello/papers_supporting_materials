/-
Smale/R/RowTest.lean — The digits of H and G, and what a passing row test says in plain integers.
-/
import Smale.R.Row

namespace Smale.RCheck

open Polynomial Finset Smale.RK

section interval2

variable (hb : List GS) (a k : ℕ) (amat : List (List GS))

theorem half_bound (z : GI) (hz : l1 z ≤ gB (dW k)) :
    |z.re| < 2 ^ (wOf k - 1) ∧ |z.im| < 2 ^ (wOf k - 1) := by
  have hg : gB (dW k) < 2 ^ (wOf k - 1) := gB_lt k
  exact ⟨lt_of_le_of_lt ((abs_re_le_l1 z).trans hz) hg, lt_of_le_of_lt ((abs_im_le_l1 z).trans hz) hg⟩

/-- The hypotheses every digit needs. -/
structure Good : Prop where
  shape : aShape amat = true
  aD : a + 1 ≤ 2 ^ k
  hh : ∀ l, l ≤ 17 → l1 (hE hb l) ≤ 2 ^ 75

variable {hb a k amat}

theorem Good.dW_nonneg (_ : Good hb a k amat) : (0 : ℤ) ≤ dW k := by
  unfold dW
  positivity

theorem Good.a_cast (hG : Good hb a k amat) : (a : ℤ) + 1 ≤ dW k := by
  have := hG.aD
  unfold dW
  exact_mod_cast this

theorem Good.hC_small (hG : Good hb a k amat) (s j k' : ℕ) (hk' : k' ≤ 17) (hs : s ≤ 34) :
    l1 (hCI hb a k amat s j k') ≤ gB (dW k) :=
  (hC_bound (Int.natCast_nonneg a) hG.a_cast hG.hh (aE_bound amat hG.shape) s j k' hk' hs).trans
    (hB_le_gB hG.dW_nonneg)

theorem Good.gC_small (hG : Good hb a k amat) (s j t : ℕ) (hs : s ≤ 34) :
    l1 (gCI hb a k amat s j t) ≤ gB (dW k) :=
  gC_bound (Int.natCast_nonneg a) hG.a_cast hG.hh (aE_bound amat hG.shape) s j t hs

variable (hb a k amat)

def ureOf (j : ℕ) : ℕ := toU (offOf k) (hsOf hb a k amat j).1
def uimOf (j : ℕ) : ℕ := toU (offOf k) (hsOf hb a k amat j).2

/-- A digit at this interval's width. -/
abbrev dgK (k u i : ℕ) : SN := dg (wOf k) (maskOf k) (halfOf k) u i

variable {hb a k amat}

theorem Good.dg_H_re (hG : Good hb a k amat) (j s k' : ℕ) (hs : s < 35) (hk' : k' < 18) :
    sval (dgK k (ureOf hb a k amat j) (18 * s + k')) = (hCI hb a k amat s j k').re := by
  have hN : sval (hsOf hb a k amat j).1 =
      ∑ i ∈ range (18 * 35), (hCI hb a k amat (i / 18) j (i % 18)).re * (2 ^ wOf k) ^ i :=
    hs_pi hb a k amat reAdd (fun z n => re_mul_gI z n) hG.shape j
  have hg : ∀ i < 18 * 35, |(hCI hb a k amat (i / 18) j (i % 18)).re| < 2 ^ (wOf k - 1) := by
    intro i hi
    exact (half_bound k _ (hG.hC_small _ _ _ (by omega) (by omega))).1
  have h := sval_dg (wOf k) (18 * 35) (wOf_pos k) (fun i => (hCI hb a k amat (i / 18) j (i % 18)).re) hg _ hN
    (18 * s + k') (by omega)
  have hdiv : (18 * s + k') / 18 = s := by omega
  have hmod : (18 * s + k') % 18 = k' := by omega
  simp only [hdiv, hmod] at h
  exact h

theorem Good.dg_H_im (hG : Good hb a k amat) (j s k' : ℕ) (hs : s < 35) (hk' : k' < 18) :
    sval (dgK k (uimOf hb a k amat j) (18 * s + k')) = (hCI hb a k amat s j k').im := by
  have hN : sval (hsOf hb a k amat j).2 =
      ∑ i ∈ range (18 * 35), (hCI hb a k amat (i / 18) j (i % 18)).im * (2 ^ wOf k) ^ i :=
    hs_pi hb a k amat imAdd (fun z n => im_mul_gI z n) hG.shape j
  have hg : ∀ i < 18 * 35, |(hCI hb a k amat (i / 18) j (i % 18)).im| < 2 ^ (wOf k - 1) := by
    intro i hi
    exact (half_bound k _ (hG.hC_small _ _ _ (by omega) (by omega))).2
  have h := sval_dg (wOf k) (18 * 35) (wOf_pos k) (fun i => (hCI hb a k amat (i / 18) j (i % 18)).im) hg _ hN
    (18 * s + k') (by omega)
  have hdiv : (18 * s + k') / 18 = s := by omega
  have hmod : (18 * s + k') % 18 = k' := by omega
  simp only [hdiv, hmod] at h
  exact h

variable (hb a k amat)

/-- `conj A`, packed by columns. -/
abbrev astarK : List GS := astarCols (wOf k) amat

/-- `G_s,j`, packed. -/
def gAt (j s : ℕ) : GS :=
  gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j >>> (s * (18 * wOf k)))
    (uimOf hb a k amat j >>> (s * (18 * wOf k))) gzero

variable {hb a k amat}

theorem Good.astar_val (hG : Good hb a k amat) (k' : ℕ) (hk' : k' < 17) :
    gval ((astarK k amat).getD k' gzero) = ∑ t ∈ range 17, star (aE amat t k') * gI (xW k) ^ t := by
  have hget : (astarK k amat).getD k' gzero = packX (wOf k) (amat.map fun r => gconj (r.getD k' gzero)) := by
    simp [astarCols, List.getD_eq_getElem?_getD, hk']
  have hlen := aShape_length amat hG.shape
  rw [hget, packX_val, List.length_map, hlen]
  refine sum_congr rfl fun t ht => ?_
  have ht' : t < amat.length := by
    rw [hlen]
    exact mem_range.1 ht
  rw [getD_map_lt amat _ gzero [] t ht', gval_gconj]
  rfl

theorem dg_shift_order (k u s i : ℕ) :
    dgK k (u >>> (s * (18 * wOf k))) i = dgK k u (18 * s + i) := by
  have h : s * (18 * wOf k) = wOf k * (18 * s) := by ring
  rw [h]
  exact dg_shift_mul _ _ _ _ _ _

theorem Good.gAt_val (hG : Good hb a k amat) (j s : ℕ) (hs : s < 35) :
    gval (gAt hb a k amat j s) = ∑ t ∈ range 17, gCI hb a k amat s j t * gI (xW k) ^ t := by
  unfold gAt
  rw [gRow_val, gval_gzero, zero_add]
  have hlen : (astarK k amat).length = 17 := by simp [astarCols]
  rw [hlen]
  have hterm : ∀ k' ∈ range 17,
      gval (dg (wOf k) (maskOf k) (halfOf k) (ureOf hb a k amat j >>> (s * (18 * wOf k))) k',
          dg (wOf k) (maskOf k) (halfOf k) (uimOf hb a k amat j >>> (s * (18 * wOf k))) k') *
        gval ((astarK k amat).getD k' gzero) =
      ∑ t ∈ range 17, hCI hb a k amat s j k' * star (aE amat t k') * gI (xW k) ^ t := by
    intro k' hk'
    have hk2 := mem_range.1 hk'
    have hd : gval (dg (wOf k) (maskOf k) (halfOf k) (ureOf hb a k amat j >>> (s * (18 * wOf k))) k',
        dg (wOf k) (maskOf k) (halfOf k) (uimOf hb a k amat j >>> (s * (18 * wOf k))) k') = hCI hb a k amat s j k' := by
      ext
      · change sval (dgK k (ureOf hb a k amat j >>> (s * (18 * wOf k))) k') = _
        rw [dg_shift_order]
        exact hG.dg_H_re j s k' hs (by omega)
      · change sval (dgK k (uimOf hb a k amat j >>> (s * (18 * wOf k))) k') = _
        rw [dg_shift_order]
        exact hG.dg_H_im j s k' hs (by omega)
    rw [hd, hG.astar_val k' hk2, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    ring
  rw [sum_congr rfl hterm, sum_comm]
  refine sum_congr rfl fun t _ => ?_
  unfold gCI gC
  rw [sum_mul]

theorem Good.dg_G_re (hG : Good hb a k amat) (j s t : ℕ) (hs : s < 35) (ht : t < 17) :
    sval (dgK k (toU (off17Of k) (gAt hb a k amat j s).1) t) = (gCI hb a k amat s j t).re := by
  have hN : sval (gAt hb a k amat j s).1 = ∑ i ∈ range 17, (gCI hb a k amat s j i).re * (2 ^ wOf k) ^ i := by
    change reAdd (gval (gAt hb a k amat j s)) = _
    rw [hG.gAt_val j s hs, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [gI_pow]
    exact re_mul_gI _ _
  have hg : ∀ i < 17, |(gCI hb a k amat s j i).re| < 2 ^ (wOf k - 1) := by
    intro i _
    exact (half_bound k _ (hG.gC_small _ _ _ (by omega))).1
  exact sval_dg (wOf k) 17 (wOf_pos k) (fun i => (gCI hb a k amat s j i).re) hg _ hN t ht

theorem Good.dg_G_im (hG : Good hb a k amat) (j s t : ℕ) (hs : s < 35) (ht : t < 17) :
    sval (dgK k (toU (off17Of k) (gAt hb a k amat j s).2) t) = (gCI hb a k amat s j t).im := by
  have hN : sval (gAt hb a k amat j s).2 = ∑ i ∈ range 17, (gCI hb a k amat s j i).im * (2 ^ wOf k) ^ i := by
    change imAdd (gval (gAt hb a k amat j s)) = _
    rw [hG.gAt_val j s hs, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [gI_pow]
    exact im_mul_gI _ _
  have hg : ∀ i < 17, |(gCI hb a k amat s j i).im| < 2 ^ (wOf k - 1) := by
    intro i _
    exact (half_bound k _ (hG.gC_small _ _ _ (by omega))).2
  exact sval_dg (wOf k) 17 (wOf_pos k) (fun i => (gCI hb a k amat s j i).im) hg _ hN t ht

/-! ### Magnitudes -/

theorem Good.mag_G (hG : Good hb a k amat) (j s t : ℕ) (hs : s < 35) (ht : t < 17) :
    (dgK k (toU (off17Of k) (gAt hb a k amat j s).1) t).2 + (dgK k (toU (off17Of k) (gAt hb a k amat j s).2) t).2 =
      l1N (gCI hb a k amat s j t) := by
  rw [mag_eq_natAbs (dgK k _ t), mag_eq_natAbs (dgK k (toU (off17Of k) (gAt hb a k amat j s).2) t),
    hG.dg_G_re j s t hs ht, hG.dg_G_im j s t hs ht]
  rfl

theorem Good.mag_H (hG : Good hb a k amat) (j s k' : ℕ) (hs : s < 35) (hk' : k' < 18) :
    (dgK k (ureOf hb a k amat j) (18 * s + k')).2 + (dgK k (uimOf hb a k amat j) (18 * s + k')).2 =
      l1N (hCI hb a k amat s j k') := by
  rw [mag_eq_natAbs (dgK k _ (18 * s + k')), mag_eq_natAbs (dgK k (uimOf hb a k amat j) (18 * s + k')),
    hG.dg_H_re j s k' hs hk', hG.dg_H_im j s k' hs hk']
  rfl

/-! ### The column and row sums -/

variable (amat)

/-- `Σ_t |A_tk|₁`. -/
noncomputable def colZ (k' : ℕ) : ℕ := ∑ t ∈ range 17, l1N (aE amat t k')
/-- `Σ_i |A_ji|₁`. -/
noncomputable def rowZ (j : ℕ) : ℕ := ∑ i ∈ range 17, l1N (aE amat j i)

variable {amat}

theorem Good.col_getD (hG : Good hb a k amat) (k' : ℕ) (hk' : k' < 17) :
    (colSums amat).getD k' 0 = colZ amat k' := by
  have hget : (colSums amat).getD k' 0 = l1List (amat.map fun r => r.getD k' gzero) := by
    simp [colSums, List.getD_eq_getElem?_getD, hk']
  have hlen := aShape_length amat hG.shape
  rw [hget, l1List_eq, List.length_map, hlen]
  refine sum_congr rfl fun t ht => ?_
  have ht' : t < amat.length := by
    rw [hlen]
    exact mem_range.1 ht
  rw [getD_map_lt amat _ gzero [] t ht']
  rfl

theorem colSums_length : (colSums amat).length = 17 := by
  simp [colSums]

theorem foldr_plain (L : List ℕ) : L.foldr (· + ·) 0 = ∑ i ∈ range L.length, L.getD i 0 := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [ih, sum_range_succ', add_comm]
    simp

theorem Good.l1List_row (hG : Good hb a k amat) (j : ℕ) : l1List (amat.getD j []) = rowZ amat j := by
  rw [l1List_eq]
  unfold rowZ
  have hsub : range (amat.getD j []).length ⊆ range 17 := range_subset_range.2 (aShape_row amat hG.shape j)
  rw [← sum_subset hsub]
  · rfl
  · intro i _ hi
    have hi' : (amat.getD j []).length ≤ i := by simpa using hi
    have h0 : aE amat j i = 0 := by
      unfold aE
      rw [List.getD_eq_default _ _ hi', gval_gzero]
    rw [h0]
    simp [l1N]

theorem shl_eta (x k : ℕ) : x <<< (93 + 34 * k) = x * (2 ^ 93 * (2 ^ k) ^ 34) := by
  rw [Nat.shiftLeft_eq, pow_add 2 93 (34 * k), ← pow_mul 2 k 34, Nat.mul_comm k 34]

theorem Good.eta_eq (hG : Good hb a k amat) :
    etaOf k amat = (∑ k' ∈ range 17, colZ amat k') * (2 ^ 93 * (2 ^ k) ^ 34) := by
  have hsum : ∑ i ∈ range 17, (colSums amat).getD i 0 = ∑ k' ∈ range 17, colZ amat k' :=
    sum_congr rfl fun i hi => hG.col_getD i (mem_range.1 hi)
  have hfold : (colSums amat).foldr (· + ·) 0 = ∑ k' ∈ range 17, colZ amat k' := by
    rw [foldr_plain, colSums_length, hsum]
  unfold etaOf
  rw [hfold]
  exact shl_eta _ k

/-! ### The row test -/

variable (hb a k amat)

/-- `testRow` at order 6, with its `let`s written out. -/
theorem testRow_eq (j : ℕ) :
    testRow (wOf k) (maskOf k) (halfOf k) (offOf k) (off17Of k) 6 (astarK k amat) (colSums amat) (etaOf k amat) j
        (hsOf hb a k amat j) (amat.getD j []) =
      Nat.ble
        (tailAll (wOf k) (maskOf k) (halfOf k) (colSums amat) 29
            (ureOf hb a k amat j >>> (6 * (18 * wOf k))) (uimOf hb a k amat j >>> (6 * (18 * wOf k)))
            (lowOrders (wOf k) (maskOf k) (halfOf k) (off17Of k) (astarK k amat) 5
              (ureOf hb a k amat j >>> (18 * wOf k)) (uimOf hb a k amat j >>> (18 * wOf k))
              (rowNorm (wOf k) (maskOf k) (halfOf k) j 17 0
                (toU (off17Of k) (gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j)
                  (uimOf hb a k amat j) gzero).1)
                (toU (off17Of k) (gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j)
                  (uimOf hb a k amat j) gzero).2) (0, szero)).1) +
          etaOf k amat * l1List (amat.getD j []) + 1)
        (cond (rowNorm (wOf k) (maskOf k) (halfOf k) j 17 0
                (toU (off17Of k) (gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j)
                  (uimOf hb a k amat j) gzero).1)
                (toU (off17Of k) (gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j)
                  (uimOf hb a k amat j) gzero).2) (0, szero)).2.1 0
              (rowNorm (wOf k) (maskOf k) (halfOf k) j 17 0
                (toU (off17Of k) (gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j)
                  (uimOf hb a k amat j) gzero).1)
                (toU (off17Of k) (gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j)
                  (uimOf hb a k amat j) gzero).2) (0, szero)).2.2) := rfl

theorem gAt_zero (j : ℕ) :
    gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) (ureOf hb a k amat j) (uimOf hb a k amat j) gzero =
      gAt hb a k amat j 0 := by
  simp [gAt]

theorem gAt_succ (j s : ℕ) :
    gRow (wOf k) (maskOf k) (halfOf k) (astarK k amat) ((ureOf hb a k amat j >>> (18 * wOf k)) >>> (s * (18 * wOf k)))
        ((uimOf hb a k amat j >>> (18 * wOf k)) >>> (s * (18 * wOf k))) gzero = gAt hb a k amat j (s + 1) := by
  have hshift : ∀ u : ℕ, (u >>> (18 * wOf k)) >>> (s * (18 * wOf k)) = u >>> ((s + 1) * (18 * wOf k)) := by
    intro u
    rw [← Nat.shiftRight_add]
    congr 1
    ring
  simp only [hshift, gAt]

variable {hb a k amat}

/-- **What a passing row test says.** -/
theorem Good.row_ineq (hG : Good hb a k amat) (j : ℕ) (hj : j < 17)
    (hT : testRow (wOf k) (maskOf k) (halfOf k) (offOf k) (off17Of k) 6 (astarK k amat) (colSums amat) (etaOf k amat) j
        (hsOf hb a k amat j) (amat.getD j []) = true) :
    (∑ t ∈ range 17, (if t = j then 0 else l1N (gCI hb a k amat 0 j t))) +
        ∑ s ∈ range 5, ∑ t ∈ range 17, l1N (gCI hb a k amat (s + 1) j t) +
        ∑ s ∈ range 29, ∑ k' ∈ range 17, l1N (hCI hb a k amat (6 + s) j k') * colZ amat k' +
        (∑ k' ∈ range 17, colZ amat k') * (2 ^ 93 * (2 ^ k) ^ 34) * rowZ amat j + 1 ≤
      (gCI hb a k amat 0 j j).re := by
  rw [testRow_eq, gAt_zero, Nat.ble_eq] at hT
  generalize hr0 : rowNorm (wOf k) (maskOf k) (halfOf k) j 17 0 (toU (off17Of k) (gAt hb a k amat j 0).1)
    (toU (off17Of k) (gAt hb a k amat j 0).2) (0, szero) = r0 at hT
  -- the kept digit
  have hdiag : r0.2 = dgK k (toU (off17Of k) (gAt hb a k amat j 0).1) j := by
    have := rowNorm_snd (wOf k) (maskOf k) (halfOf k) j 17 0 (toU (off17Of k) (gAt hb a k amat j 0).1)
      (toU (off17Of k) (gAt hb a k amat j 0).2) (0, szero) (by omega) (by omega)
    rw [hr0] at this
    simpa using this
  have hdsval : sval r0.2 = (gCI hb a k amat 0 j j).re := by
    rw [hdiag]
    exact hG.dg_G_re j 0 j (by omega) hj
  -- the first sum
  have hA0 : (∑ t ∈ range 17, (if t = j then 0 else l1N (gCI hb a k amat 0 j t))) ≤ r0.1 := by
    rw [← hr0, rowNorm_fst]
    simp only [Nat.zero_add]
    refine sum_le_sum fun t ht => ?_
    have ht' := mem_range.1 ht
    by_cases htj : t = j
    · simp [htj]
    · simp only [htj, ite_false]
      exact (hG.mag_G j 0 t (by omega) ht').ge
  -- the low orders
  have hlow : lowOrders (wOf k) (maskOf k) (halfOf k) (off17Of k) (astarK k amat) 5
        (ureOf hb a k amat j >>> (18 * wOf k)) (uimOf hb a k amat j >>> (18 * wOf k)) r0.1 =
      r0.1 + ∑ s ∈ range 5, ∑ t ∈ range 17, l1N (gCI hb a k amat (s + 1) j t) := by
    rw [lowOrders_val]
    refine congrArg (r0.1 + ·) (sum_congr rfl fun s hs => sum_congr rfl fun t ht => ?_)
    have hs' := mem_range.1 hs
    rw [gAt_succ]
    exact hG.mag_G j (s + 1) t (by omega) (mem_range.1 ht)
  -- the tail
  have htail : ∀ acc : ℕ, tailAll (wOf k) (maskOf k) (halfOf k) (colSums amat) 29
        (ureOf hb a k amat j >>> (6 * (18 * wOf k))) (uimOf hb a k amat j >>> (6 * (18 * wOf k))) acc =
      acc + ∑ s ∈ range 29, ∑ k' ∈ range 17, l1N (hCI hb a k amat (6 + s) j k') * colZ amat k' := by
    intro acc
    rw [tailAll_val, colSums_length]
    refine congrArg (acc + ·) (sum_congr rfl fun s hs => sum_congr rfl fun k' hk' => ?_)
    have hs' := mem_range.1 hs
    have hk2 := mem_range.1 hk'
    rw [hG.col_getD k' hk2]
    have h1 := dg_shift_order k (ureOf hb a k amat j) 6 (18 * s + k')
    have h2 := dg_shift_order k (uimOf hb a k amat j) 6 (18 * s + k')
    have hidx : 18 * 6 + (18 * s + k') = 18 * (6 + s) + k' := by ring
    rw [hidx] at h1 h2
    have hm := hG.mag_H j (6 + s) k' (by omega) (by omega)
    rw [← h1, ← h2] at hm
    exact congrArg (· * colZ amat k') hm
  rw [hlow, htail, hG.l1List_row, hG.eta_eq] at hT
  -- the sign of the diagonal
  obtain ⟨hsign, hmag⟩ : r0.2.1 = false ∧ r0.1 + ∑ s ∈ range 5, ∑ t ∈ range 17, l1N (gCI hb a k amat (s + 1) j t) +
      ∑ s ∈ range 29, ∑ k' ∈ range 17, l1N (hCI hb a k amat (6 + s) j k') * colZ amat k' +
      (∑ k' ∈ range 17, colZ amat k') * (2 ^ 93 * (2 ^ k) ^ 34) * rowZ amat j + 1 ≤ r0.2.2 := by
    cases hb' : r0.2.1 with
    | true =>
      rw [hb'] at hT
      exact absurd hT (by simp)
    | false =>
      rw [hb'] at hT
      exact ⟨rfl, hT⟩
  have hval : (gCI hb a k amat 0 j j).re = (r0.2.2 : ℤ) := by
    rw [← hdsval]
    simp [sval, hsign]
  rw [hval]
  have key : ∀ A0 r01 A2 A3 A4 m : ℕ, A0 ≤ r01 → r01 + A2 + A3 + A4 + 1 ≤ m → A0 + A2 + A3 + A4 + 1 ≤ m := by
    intro A0 r01 A2 A3 A4 m h1 h2
    omega
  exact_mod_cast key _ _ _ _ _ _ hA0 hmag

/-- From the whole check. -/
theorem check_good (hc : checkInterval hb a k 6 amat = true) (hh : ∀ l, l ≤ 17 → l1 (hE hb l) ≤ 2 ^ 75) :
    Good hb a k amat ∧ ∀ j < 17, testRow (wOf k) (maskOf k) (halfOf k) (offOf k) (off17Of k) 6 (astarK k amat)
      (colSums amat) (etaOf k amat) j (hsOf hb a k amat j) (amat.getD j []) = true := by
  rw [checkInterval_eq] at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨⟨h1, ?_, hh⟩, h3⟩
  have := Nat.le_of_ble_eq_true h2
  simpa [Nat.one_shiftLeft] using this

end interval2

end Smale.RCheck
