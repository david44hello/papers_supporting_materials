/-
Smale/R/CheckerSpec.lean — What the checker's functions compute: signed values, Gaussian values, the loops, the balanced digits.
-/
import Smale.R.Checker
import Mathlib

namespace Smale.RK

open Finset

/-! ### Signed values -/

def sval (x : SN) : ℤ := if x.1 = true then -(x.2 : ℤ) else (x.2 : ℤ)

@[simp] theorem sval_szero : sval szero = 0 := by simp [sval, szero]

theorem sval_sneg (x : SN) : sval (sneg x) = - sval x := by
  obtain ⟨b, n⟩ := x
  cases b <;> simp [sval, sneg]

theorem sval_sadd (x y : SN) : sval (sadd x y) = sval x + sval y := by
  obtain ⟨b, n⟩ := x
  obtain ⟨c, m⟩ := y
  by_cases h : m ≤ n
  · have h' : Nat.ble m n = true := by
      rw [Nat.ble_eq]
      exact h
    cases b <;> cases c <;> simp [sadd, sval, h', Nat.cast_sub h] <;> ring
  · have h' : Nat.ble m n = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]
      exact h
    have hle : n ≤ m := by omega
    cases b <;> cases c <;> simp [sadd, sval, h', Nat.cast_sub hle] <;> ring

theorem sval_smul (x y : SN) : sval (smul x y) = sval x * sval y := by
  obtain ⟨b, n⟩ := x
  obtain ⟨c, m⟩ := y
  cases b <;> cases c <;> simp [smul, sval]

theorem sval_sshl (x : SN) (w : ℕ) : sval (sshl x w) = sval x * 2 ^ w := by
  obtain ⟨b, n⟩ := x
  cases b <;> simp [sshl, sval, Nat.shiftLeft_eq]

theorem mag_eq_natAbs (x : SN) : x.2 = (sval x).natAbs := by
  obtain ⟨b, n⟩ := x
  cases b <;> simp [sval]

/-! ### Gaussian values -/

def gval (x : GS) : GaussianInt := ⟨sval x.1, sval x.2⟩

/-- The integer `n` as a Gaussian integer. -/
abbrev gI (n : ℤ) : GaussianInt := (n : GaussianInt)

@[simp] theorem gval_gzero : gval gzero = 0 := by
  ext <;> simp [gval, gzero]

theorem gval_gadd (x y : GS) : gval (gadd x y) = gval x + gval y := by
  ext <;> simp [gval, gadd, sval_sadd]

theorem gval_gneg (x : GS) : gval (gneg x) = - gval x := by
  ext <;> simp [gval, gneg, sval_sneg]

theorem gval_gconj (x : GS) : gval (gconj x) = star (gval x) := by
  ext <;> simp [gval, gconj, sval_sneg]

theorem gval_gmul (x y : GS) : gval (gmul x y) = gval x * gval y := by
  ext <;> simp [gval, gmul, sval_sadd, sval_sneg, sval_smul, Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem re_mul_gI (z : GaussianInt) (n : ℤ) : (z * gI n).re = z.re * n := by
  simp [Zsqrtd.re_mul, gI]

theorem im_mul_gI (z : GaussianInt) (n : ℤ) : (z * gI n).im = z.im * n := by
  simp [Zsqrtd.im_mul, gI]

theorem gval_gshl (x : GS) (w : ℕ) : gval (gshl x w) = gval x * gI (2 ^ w) := by
  ext
  · rw [re_mul_gI]
    simp [gval, gshl, sval_sshl]
  · rw [im_mul_gI]
    simp [gval, gshl, sval_sshl]

/-! ### The packing loops -/

theorem packX_val (w : ℕ) (L : List GS) :
    gval (packX w L) = ∑ i ∈ range L.length, gval (L.getD i gzero) * gI (2 ^ w) ^ i := by
  induction L with
  | nil => simp [packX]
  | cons q qs ih =>
    simp only [packX, gval_gadd, gval_gshl, ih, List.length_cons]
    rw [sum_range_succ', sum_mul, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [pow_succ]
    ring

/-- `vTable` follows a two-step recurrence. -/
theorem vTable_getD (tw d2 : SN) (f : ℕ → ℤ) (hf : ∀ n, f (n + 2) = sval tw * f (n + 1) + sval d2 * f n) :
    ∀ (n l : ℕ) (v v' : SN), sval v = f (l + 1) → sval v' = f l → ∀ i < n,
      sval ((vTable tw d2 n v v').getD i szero) = f (l + 1 + i) := by
  intro n
  induction n with
  | zero => intro l v v' _ _ i hi; omega
  | succ n ih =>
    intro l v v' hv hv' i hi
    cases i with
    | zero => simpa [vTable] using hv
    | succ i =>
      have hstep : sval (sadd (smul tw v) (smul d2 v')) = f (l + 1 + 1) := by
        rw [sval_sadd, sval_smul, sval_smul, hv, hv', hf]
      have := ih (l + 1) _ _ hstep hv i (by omega)
      simp only [vTable, List.getD_cons_succ]
      rw [this]
      congr 1
      omega

theorem qList_length (k : ℕ) (hb : List GS) (vs : List SN) : (qList k hb vs).length = 18 := by
  simp [qList]

theorem qList_getD (k : ℕ) (hb : List GS) (vs : List SN) (l : ℕ) (hl : l < 18) :
    gval ((qList k hb vs).getD l gzero) =
      gval (hb.getD l gzero) * gI (2 ^ (k * (17 - l))) * gI (sval (vs.getD l szero)) := by
  have hget : (qList k hb vs).getD l gzero =
      (smul (sshl (hb.getD l gzero).1 (k * (17 - l))) (vs.getD l szero),
        smul (sshl (hb.getD l gzero).2 (k * (17 - l))) (vs.getD l szero)) := by
    simp [qList, List.getD, hl]
  rw [hget]
  ext
  · rw [re_mul_gI, re_mul_gI]
    simp [gval, sval_smul, sval_sshl]
  · rw [im_mul_gI, im_mul_gI]
    simp [gval, sval_smul, sval_sshl]

/-- `rowsAux` follows its one-step recurrence. -/
theorem rowsAux_getD (w J : ℕ) (cP rP : GS) (qs : List GS) (R : ℕ → GaussianInt)
    (hR : ∀ j < J, R (j + 1) = R j * gI (2 ^ w) + gval (qs.getD j gzero) * gval cP -
      star (gval (qs.getD (17 - j) gzero)) * gval rP) :
    ∀ (n j : ℕ) (prev : GS), j + n ≤ J → gval prev = R j → ∀ i < n,
      gval ((rowsAux w cP rP qs n j prev).getD i gzero) = R (j + i + 1) := by
  intro n
  induction n with
  | zero => intro j prev _ _ i hi; omega
  | succ n ih =>
    intro j prev hjn hprev i hi
    have hstep : gval (gadd (gadd (gshl prev w) (gmul (qs.getD j gzero) cP))
        (gneg (gmul (gconj (qs.getD (17 - j) gzero)) rP))) = R (j + 1) := by
      rw [hR j (by omega), gval_gadd, gval_gadd, gval_gneg, gval_gshl, gval_gmul, gval_gmul, gval_gconj, hprev]
      ring
    cases i with
    | zero => simpa [rowsAux] using hstep
    | succ i =>
      have := ih (j + 1) _ (by omega) hstep i (by omega)
      simp only [rowsAux, List.getD_cons_succ]
      rw [this]
      congr 1
      omega

theorem rowsAux_length (w : ℕ) (cP rP : GS) (qs : List GS) :
    ∀ (n j : ℕ) (prev : GS), (rowsAux w cP rP qs n j prev).length = n := by
  intro n
  induction n with
  | zero => intro j prev; rfl
  | succ n ih => intro j prev; simp [rowsAux, ih]

theorem combo_val : ∀ (as rs : List GS) (acc : GS), as.length ≤ rs.length →
    gval (combo as rs acc) =
      gval acc + ∑ i ∈ range as.length, gval (as.getD i gzero) * gval (rs.getD i gzero) := by
  intro as
  induction as with
  | nil => intro rs acc _; simp [combo]
  | cons a as ih =>
    intro rs acc h
    cases rs with
    | nil => simp at h
    | cons r rs =>
      have h' : as.length ≤ rs.length := by simpa using h
      simp only [combo, List.length_cons]
      rw [ih rs _ h', gval_gadd, gval_gmul, sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

/-! ### Digits -/

/-- Digit `i` of `u`, balanced. -/
def dg (w mask half u i : ℕ) : SN := digit mask half (u >>> (w * i))

section digits

variable (w mask half : ℕ)

theorem dg_zero (u : ℕ) : digit mask half u = dg w mask half u 0 := by
  simp [dg]

theorem dg_shift (u i : ℕ) : dg w mask half (u >>> w) i = dg w mask half u (i + 1) := by
  simp only [dg]
  rw [← Nat.shiftRight_add]
  congr 2
  ring

theorem dg_shift_mul (m u i : ℕ) : dg w mask half (u >>> (w * m)) i = dg w mask half u (m + i) := by
  simp only [dg]
  rw [← Nat.shiftRight_add]
  congr 2
  ring

theorem gRow_val : ∀ (L : List GS) (ure uim : ℕ) (acc : GS),
    gval (gRow w mask half L ure uim acc) = gval acc +
      ∑ k ∈ range L.length, gval (dg w mask half ure k, dg w mask half uim k) * gval (L.getD k gzero) := by
  intro L
  induction L with
  | nil => intro ure uim acc; simp [gRow]
  | cons a as ih =>
    intro ure uim acc
    simp only [gRow, List.length_cons]
    rw [ih, gval_gadd, gval_gmul, sum_range_succ']
    simp only [dg_shift, List.getD_cons_succ, List.getD_cons_zero, ← dg_zero w mask half]
    ring

theorem tailRow_val : ∀ (L : List ℕ) (ure uim acc : ℕ),
    tailRow w mask half L ure uim acc = acc +
      ∑ k ∈ range L.length, ((dg w mask half ure k).2 + (dg w mask half uim k).2) * L.getD k 0 := by
  intro L
  induction L with
  | nil => intro ure uim acc; simp [tailRow]
  | cons a as ih =>
    intro ure uim acc
    simp only [tailRow, List.length_cons]
    rw [ih, sum_range_succ']
    simp only [dg_shift, List.getD_cons_succ, List.getD_cons_zero, ← dg_zero w mask half]
    ring

theorem tailAll_val (col : List ℕ) : ∀ (n ure uim acc : ℕ),
    tailAll w mask half col n ure uim acc = acc + ∑ s ∈ range n, ∑ k ∈ range col.length,
      ((dg w mask half ure (18 * s + k)).2 + (dg w mask half uim (18 * s + k)).2) * col.getD k 0 := by
  intro n
  induction n with
  | zero => intro ure uim acc; simp [tailAll]
  | succ n ih =>
    intro ure uim acc
    simp only [tailAll]
    rw [ih, tailRow_val, sum_range_succ']
    have hshift : ∀ (u s k : ℕ), dg w mask half (u >>> (18 * w)) (18 * s + k) = dg w mask half u (18 * (s + 1) + k) := by
      intro u s k
      have h1 : 18 * w = w * 18 := by ring
      rw [h1, dg_shift_mul]
      congr 1
      ring
    simp only [hshift]
    simp only [Nat.mul_zero, Nat.zero_add]
    ring

theorem rowNorm_fst (j : ℕ) : ∀ (n t ure uim : ℕ) (acc : ℕ × SN),
    (rowNorm w mask half j n t ure uim acc).1 = acc.1 + ∑ i ∈ range n,
      (if t + i = j then (dg w mask half uim i).2 else (dg w mask half ure i).2 + (dg w mask half uim i).2) := by
  intro n
  induction n with
  | zero => intro t ure uim acc; simp [rowNorm]
  | succ n ih =>
    intro t ure uim acc
    simp only [rowNorm]
    rw [ih, sum_range_succ']
    simp only [dg_shift, ← dg_zero w mask half, Nat.add_zero]
    have hidx : ∀ i, t + 1 + i = t + (i + 1) := by intro i; ring
    simp only [hidx]
    by_cases htj : t = j
    · simp [htj, Nat.beq_refl]
      ring
    · have hne : Nat.beq t j = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]
        exact htj
      simp [htj, hne]
      ring

theorem rowNorm_snd (j : ℕ) : ∀ (n t ure uim : ℕ) (acc : ℕ × SN), t ≤ j → j < t + n →
    (rowNorm w mask half j n t ure uim acc).2 = dg w mask half ure (j - t) := by
  intro n
  induction n with
  | zero => intro t ure uim acc h1 h2; omega
  | succ n ih =>
    intro t ure uim acc h1 h2
    simp only [rowNorm]
    by_cases htj : t = j
    · subst htj
      have hkeep : ∀ (m s u v : ℕ) (b : ℕ × SN), t < s →
          (rowNorm w mask half t m s u v b).2 = b.2 := by
        intro m
        induction m with
        | zero => intro s u v b _; rfl
        | succ m ihm =>
          intro s u v b hs
          simp only [rowNorm]
          have hne : Nat.beq s t = false := by
            rw [← Bool.not_eq_true, Nat.beq_eq]
            omega
          rw [ihm _ _ _ _ (by omega), hne]
          rfl
      rw [hkeep _ _ _ _ _ (by omega)]
      simp [Nat.beq_refl, ← dg_zero w mask half]
    · rw [ih _ _ _ _ (by omega) (by omega), dg_shift]
      congr 1
      omega

/-- `lowOrders`, read. -/
theorem lowOrders_val (off17 : ℕ) (astar : List GS) : ∀ (n ure uim acc : ℕ),
    lowOrders w mask half off17 astar n ure uim acc = acc + ∑ s ∈ range n, ∑ t ∈ range 17,
      ((dg w mask half (toU off17 (gRow w mask half astar (ure >>> (s * (18 * w))) (uim >>> (s * (18 * w))) gzero).1) t).2 +
       (dg w mask half (toU off17 (gRow w mask half astar (ure >>> (s * (18 * w))) (uim >>> (s * (18 * w))) gzero).2) t).2) := by
  intro n
  induction n with
  | zero => intro ure uim acc; simp [lowOrders]
  | succ n ih =>
    intro ure uim acc
    simp only [lowOrders]
    rw [ih, rowNorm_fst, sum_range_succ' _ n]
    have hshift : ∀ (u s : ℕ), (u >>> (18 * w)) >>> (s * (18 * w)) = u >>> ((s + 1) * (18 * w)) := by
      intro u s
      rw [← Nat.shiftRight_add]
      congr 1
      ring
    simp only [hshift]
    have hif : ∀ (y z : ℕ), ∑ i ∈ range 17, (if 0 + i = 99 then (dg w mask half z i).2 else (dg w mask half y i).2 + (dg w mask half z i).2) =
        ∑ i ∈ range 17, ((dg w mask half y i).2 + (dg w mask half z i).2) := by
      intro y z
      refine sum_congr rfl fun i hi => ?_
      have := mem_range.1 hi
      rw [ite_eq_right (by omega)]
    simp only [hif, Nat.zero_mul, Nat.shiftRight_zero]
    ring

end digits

/-! ### The balanced digit lemma -/

theorem digits_of_expansion (x : ℕ) (hx : 0 < x) : ∀ (n : ℕ) (D : ℕ → ℕ), (∀ i < n, D i < x) → ∀ i < n,
    (∑ j ∈ range n, D j * x ^ j) / x ^ i % x = D i := by
  intro n
  induction n with
  | zero => intro D _ i hi; omega
  | succ n ih =>
    intro D hD i hi
    have hsplit : ∑ j ∈ range (n + 1), D j * x ^ j = D 0 + x * ∑ j ∈ range n, D (j + 1) * x ^ j := by
      rw [sum_range_succ', mul_sum, add_comm]
      simp only [pow_zero, mul_one]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [pow_succ]
      ring
    have h0 : D 0 < x := hD 0 (by omega)
    rw [hsplit]
    cases i with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    | succ i =>
      have hdiv : (D 0 + x * ∑ j ∈ range n, D (j + 1) * x ^ j) / x = ∑ j ∈ range n, D (j + 1) * x ^ j := by
        rw [Nat.add_mul_div_left _ _ hx, Nat.div_eq_of_lt h0, zero_add]
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
      exact ih (fun j => D (j + 1)) (fun j hj => hD (j + 1) (by omega)) i (by omega)

theorem offsetOf_eq (w n : ℕ) (hw : 0 < w) :
    offsetOf w n = ∑ j ∈ range n, 2 ^ (w - 1) * (2 ^ w) ^ j := by
  have hx : 2 ≤ 2 ^ w := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  simp only [offsetOf, Nat.one_shiftLeft]
  rw [← mul_sum, Nat.geomSum_eq hx, pow_mul]

theorem sval_digit (w u : ℕ) (_hw : 0 < w) :
    sval (digit ((1 <<< w) - 1) (1 <<< (w - 1)) u) = ((u % 2 ^ w : ℕ) : ℤ) - 2 ^ (w - 1) := by
  have hland : Nat.land u (2 ^ w - 1) = u % 2 ^ w := Nat.and_two_pow_sub_one_eq_mod u w
  simp only [digit, Nat.one_shiftLeft, hland]
  by_cases h : 2 ^ (w - 1) ≤ u % 2 ^ w
  · have h' : Nat.ble (2 ^ (w - 1)) (u % 2 ^ w) = true := by
      rw [Nat.ble_eq]
      exact h
    simp [h', sval, Nat.cast_sub h]
  · have h' : Nat.ble (2 ^ (w - 1)) (u % 2 ^ w) = false := by
      rw [← Bool.not_eq_true, Nat.ble_eq]
      exact h
    have hle : u % 2 ^ w ≤ 2 ^ (w - 1) := by omega
    simp [h', sval, Nat.cast_sub hle]

/-- **The balanced digit lemma.** A signed number whose base `2^w` expansion has all digits below `2^(w-1)` in size
gives back exactly those digits. -/
theorem sval_dg (w n : ℕ) (hw : 0 < w) (g : ℕ → ℤ) (hg : ∀ i < n, |g i| < 2 ^ (w - 1)) (N : SN)
    (hN : sval N = ∑ i ∈ range n, g i * (2 ^ w) ^ i) (i : ℕ) (hi : i < n) :
    sval (dg w ((1 <<< w) - 1) (1 <<< (w - 1)) (toU (offsetOf w n) N) i) = g i := by
  have hx2 : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  -- the nonnegative digits
  let D : ℕ → ℕ := fun j => ((2 : ℤ) ^ (w - 1) + g j).toNat
  have hDcast : ∀ j < n, ((D j : ℕ) : ℤ) = 2 ^ (w - 1) + g j := by
    intro j hj
    have := abs_lt.1 (hg j hj)
    exact Int.toNat_of_nonneg (by linarith [this.1])
  have hDlt : ∀ j < n, D j < 2 ^ w := by
    intro j hj
    have h1 := hDcast j hj
    have h2 := abs_lt.1 (hg j hj)
    have h3 : ((D j : ℕ) : ℤ) < ((2 ^ w : ℕ) : ℤ) := by
      push_cast
      rw [h1, hx2]
      linarith [h2.2]
    exact_mod_cast h3
  -- the offset number is the sum of those digits
  have hsum : (((offsetOf w n : ℕ) : ℤ) + sval N) = ((∑ j ∈ range n, D j * (2 ^ w) ^ j : ℕ) : ℤ) := by
    rw [offsetOf_eq w n hw, hN]
    push_cast
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [hDcast j (mem_range.1 hj)]
    ring
  have hU : toU (offsetOf w n) N = ∑ j ∈ range n, D j * (2 ^ w) ^ j := by
    obtain ⟨b, m⟩ := N
    cases b with
    | false =>
      have : ((offsetOf w n + m : ℕ) : ℤ) = ((∑ j ∈ range n, D j * (2 ^ w) ^ j : ℕ) : ℤ) := by
        rw [← hsum]
        simp [sval]
      exact_mod_cast this
    | true =>
      have hval : ((offsetOf w n : ℕ) : ℤ) - m = ((∑ j ∈ range n, D j * (2 ^ w) ^ j : ℕ) : ℤ) := by
        rw [← hsum]
        simp [sval]
        ring
      have hle : m ≤ offsetOf w n := by
        have hnn : (0 : ℤ) ≤ ((∑ j ∈ range n, D j * (2 ^ w) ^ j : ℕ) : ℤ) := Int.natCast_nonneg _
        have : (m : ℤ) ≤ offsetOf w n := by linarith
        exact_mod_cast this
      have : ((offsetOf w n - m : ℕ) : ℤ) = ((∑ j ∈ range n, D j * (2 ^ w) ^ j : ℕ) : ℤ) := by
        rw [Nat.cast_sub hle, hval]
      exact_mod_cast this
  simp only [dg]
  rw [sval_digit w _ hw, hU, Nat.shiftRight_eq_div_pow, pow_mul,
    digits_of_expansion (2 ^ w) (by positivity) n D hDlt i hi, hDcast i hi]
  ring

end Smale.RK
