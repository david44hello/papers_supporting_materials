/-
Smale/R/Row.lean — The objects of one interval, and the packed rows as values.
-/
import Smale.R.Poly

namespace Smale.RCheck

open Polynomial Finset Smale.RK

/-! ### Small helpers -/

theorem getD_map_lt {α β : Type*} (L : List α) (f : α → β) (d : β) (d' : α) (t : ℕ) (ht : t < L.length) :
    (L.map f).getD t d = f (L.getD t d') := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]

theorem sum_two_level (c n : ℕ) (F : ℕ → ℤ) :
    ∑ i ∈ range (c * n), F i = ∑ s ∈ range n, ∑ k ∈ range c, F (c * s + k) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

def reAdd : GI →+ ℤ where
  toFun := Zsqrtd.re
  map_zero' := rfl
  map_add' := Zsqrtd.re_add

def imAdd : GI →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' := Zsqrtd.im_add

theorem star_gI (n : ℤ) : star (gI n) = gI n := by
  ext <;> simp [gI]

theorem gI_pow (n : ℤ) (e : ℕ) : gI n ^ e = gI (n ^ e) := by
  simp [gI]

theorem gI_mul (n m : ℤ) : gI n * gI m = gI (n * m) := by
  simp [gI]

theorem foldr_sum {α : Type*} (L : List α) (f : α → ℕ) (d : α) :
    (L.map f).foldr (· + ·) 0 = ∑ i ∈ range L.length, f (L.getD i d) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, List.length_cons]
    rw [ih, sum_range_succ', add_comm]
    simp

/-- The natural `ℓ¹` size. -/
def l1N (z : GI) : ℕ := z.re.natAbs + z.im.natAbs

theorem l1N_cast (z : GI) : ((l1N z : ℕ) : ℤ) = l1 z := by
  simp [l1N, l1]

theorem l1List_eq (L : List GS) : l1List L = ∑ i ∈ range L.length, l1N (gval (L.getD i gzero)) := by
  unfold l1List
  rw [foldr_sum L _ gzero]
  refine sum_congr rfl fun i _ => ?_
  simp only [l1N, gval]
  rw [mag_eq_natAbs (L.getD i gzero).1, mag_eq_natAbs (L.getD i gzero).2]

/-! ### Evaluating the polynomials at an integer -/

section eval

variable (a D : ℤ) (h : ℕ → GI) (A : ℕ → ℕ → GI)

theorem eval_sg (T : ℤ) (f : GI[X]) : (sg f).eval (gI T) = star (f.eval (gI T)) := by
  have hstar : (starRingEnd GI) (gI T) = gI T := star_gI T
  calc (sg f).eval (gI T) = f.eval₂ (starRingEnd GI) (gI T) := by simp [sg, eval_map]
    _ = f.eval₂ ((starRingEnd GI).comp (RingHom.id GI)) ((starRingEnd GI) (gI T)) := by rw [hstar]; rfl
    _ = (starRingEnd GI) (f.eval₂ (RingHom.id GI) (gI T)) := (hom_eval₂ f _ _ _).symm
    _ = star (f.eval (gI T)) := by rw [eval₂_id]; rfl

theorem qP_eval (T : ℤ) (l : ℕ) :
    (qP a D h l).eval (gI T) = h l * gI (D ^ (17 - l)) * gI ((wP a D (l + 1)).eval T) := by
  unfold qP
  rw [eval_mul, eval_C, eval_map]
  congr 1
  exact eval₂_at_apply (Int.castRingHom GI) T

/-- The ring map "evaluate at the integer `T`". -/
noncomputable def phiT (T : ℤ) : GI[X] →+* GI := evalRingHom (gI T)

theorem bP_eval (T : ℤ) (j k : ℕ) :
    (bP a D h j k).eval (gI T) = bF (starRingEnd GI) 17 (fun l => (qP a D h l).eval (gI T)) j k := by
  have := bF_map sg 17 (qP a D h) (starRingEnd GI) (phiT T) (fun f => eval_sg T f) j k
  simpa [phiT, bP] using this

end eval

/-! ### The objects of one interval -/

section interval

variable (hb : List GS) (a k : ℕ) (amat : List (List GS))

def hE (l : ℕ) : GI := gval (hb.getD l gzero)
def aE (j i : ℕ) : GI := gval ((amat.getD j []).getD i gzero)

def wOf (k : ℕ) : ℕ := 324 + 34 * k
def maskOf (k : ℕ) : ℕ := (1 <<< wOf k) - 1
def halfOf (k : ℕ) : ℕ := 1 <<< (wOf k - 1)
def offOf (k : ℕ) : ℕ := offsetOf (wOf k) (18 * 35)
def off17Of (k : ℕ) : ℕ := offsetOf (wOf k) 17

def vsOf (a k : ℕ) : List SN :=
  vTable (false, 2 * a + (2 <<< (18 * wOf k))) (true, 1 <<< (2 * k)) 18 (false, 1) szero
def qsOf : List GS := qList k hb (vsOf a k)
def cPOf : GS := gconj (packX (wOf k) (qsOf hb a k))
def rPOf : GS := packX (wOf k) ((List.range 18).map fun t => (qsOf hb a k).getD (17 - t) gzero)
def rowsOf : List GS := rowsAux (wOf k) (cPOf hb a k) (rPOf hb a k) (qsOf hb a k) 17 0 gzero
def etaOf : ℕ := ((colSums amat).foldr (· + ·) 0) <<< (etaBits + 34 * k)

theorem checkInterval_eq (order : ℕ) : checkInterval hb a k order amat =
    (aShape amat && Nat.ble (a + 1) (1 <<< k) && (List.range 17).all fun j =>
      testRow (wOf k) (maskOf k) (halfOf k) (offOf k) (off17Of k) order (astarCols (wOf k) amat) (colSums amat)
        (etaOf k amat) j (combo (amat.getD j []) (rowsOf hb a k) gzero) (amat.getD j [])) := rfl

abbrev xW (k : ℕ) : ℤ := 2 ^ wOf k
abbrev tW (k : ℕ) : ℤ := xW k ^ 18
abbrev dW (k : ℕ) : ℤ := 2 ^ k

theorem wOf_pos (k : ℕ) : 0 < wOf k := by unfold wOf; omega

theorem vs_getD (i : ℕ) (hi : i < 18) :
    sval ((vsOf a k).getD i szero) = (wP (a : ℤ) (dW k) (i + 1)).eval (tW k) := by
  have hT : tW k = 2 ^ (18 * wOf k) := by
    unfold tW xW
    rw [← pow_mul]
    congr 1
    ring
  have hf : ∀ n, (fun n => (wP (a : ℤ) (dW k) n).eval (tW k)) (n + 2) =
      sval (false, 2 * a + (2 <<< (18 * wOf k))) * (fun n => (wP (a : ℤ) (dW k) n).eval (tW k)) (n + 1) +
        sval (true, 1 <<< (2 * k)) * (fun n => (wP (a : ℤ) (dW k) n).eval (tW k)) n := by
    intro n
    simp only [wP, eval_sub, eval_mul, eval_add, eval_C, eval_X, sval, Nat.shiftLeft_eq, ite_true, Bool.false_eq_true,
      ite_false]
    push_cast
    rw [hT]
    unfold dW
    rw [show (2 : ℤ) ^ (2 * k) = ((2 : ℤ) ^ k) ^ 2 by rw [← pow_mul]; ring_nf]
    ring
  have := vTable_getD (false, 2 * a + (2 <<< (18 * wOf k))) (true, 1 <<< (2 * k))
    (fun n => (wP (a : ℤ) (dW k) n).eval (tW k)) hf 18 0 (false, 1) szero (by simp [sval, wP]) (by simp [wP]) i hi
  have hidx : 0 + 1 + i = i + 1 := by omega
  rw [hidx] at this
  exact this

theorem qs_length : (qsOf hb a k).length = 18 := qList_length _ _ _

/-- `q_l` at `tau = x^18`. -/
noncomputable def qV (l : ℕ) : GI := (qP (a : ℤ) (dW k) (hE hb) l).eval (gI (tW k))

theorem qs_getD (l : ℕ) (hl : l < 18) : gval ((qsOf hb a k).getD l gzero) = qV hb a k l := by
  unfold qsOf qV
  rw [qList_getD _ _ _ _ hl, qP_eval, vs_getD a k l hl]
  have hpow : ((2 : ℤ) ^ (k * (17 - l))) = dW k ^ (17 - l) := by
    unfold dW
    rw [pow_mul]
  rw [hpow]
  rfl

theorem star_xW_pow (e : ℕ) : star (gI (xW k) ^ e) = gI (xW k) ^ e := by
  rw [gI_pow, star_gI]

theorem cP_val : gval (cPOf hb a k) = ∑ i ∈ range 18, star (qV hb a k i) * gI (xW k) ^ i := by
  unfold cPOf
  rw [gval_gconj, packX_val, qs_length, star_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [star_mul', star_xW_pow, qs_getD hb a k i (mem_range.1 hi)]

theorem rP_val : gval (rPOf hb a k) = ∑ t ∈ range 18, qV hb a k (17 - t) * gI (xW k) ^ t := by
  unfold rPOf
  rw [packX_val]
  have hlen : ((List.range 18).map fun t => (qsOf hb a k).getD (17 - t) gzero).length = 18 := by simp
  rw [hlen]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.1 ht
  have hget : ((List.range 18).map fun t => (qsOf hb a k).getD (17 - t) gzero).getD t gzero =
      (qsOf hb a k).getD (17 - t) gzero := by
    simp [List.getD_eq_getElem?_getD, ht']
  rw [hget, qs_getD hb a k (17 - t) (by omega)]

/-- `Row_j`, value. Index shifted: `rowV 0 = 0`, `rowV (j + 1)` is `Row_j`. -/
noncomputable def rowV : ℕ → GI
  | 0 => 0
  | j + 1 => ∑ k' ∈ range 18, bF (starRingEnd GI) 17 (qV hb a k) j k' * gI (xW k) ^ k'

theorem rowV_step (j : ℕ) (hj : j < 17) :
    rowV hb a k (j + 1) = rowV hb a k j * gI (2 ^ wOf k) +
      gval ((qsOf hb a k).getD j gzero) * gval (cPOf hb a k) -
      star (gval ((qsOf hb a k).getD (17 - j) gzero)) * gval (rPOf hb a k) := by
  rw [qs_getD hb a k j (by omega), qs_getD hb a k (17 - j) (by omega), cP_val, rP_val]
  cases j with
  | zero =>
    have := bF_row_zero (starRingEnd GI) 17 (qV hb a k) (gI (xW k))
    simp only [rowV]
    rw [this]
    simp [starRingEnd_apply]
  | succ j =>
    have := bF_row_succ (starRingEnd GI) 17 (qV hb a k) (gI (xW k)) j (by omega)
    simp only [rowV]
    rw [this]
    simp [starRingEnd_apply]

theorem rows_getD (i : ℕ) (hi : i < 17) : gval ((rowsOf hb a k).getD i gzero) = rowV hb a k (i + 1) := by
  have := rowsAux_getD (wOf k) 17 (cPOf hb a k) (rPOf hb a k) (qsOf hb a k) (rowV hb a k)
    (rowV_step hb a k) 17 0 gzero (by omega) (by simp [rowV]) i hi
  simpa [rowsOf] using this

theorem rows_length : (rowsOf hb a k).length = 17 := rowsAux_length _ _ _ _ _ _ _

/-! ### The shape checks -/

theorem getD_mem_or {α : Type*} (L : List α) (i : ℕ) (d : α) : L.getD i d ∈ L ∨ L.getD i d = d := by
  by_cases h : i < L.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (by omega)

theorem aShape_length (hs : aShape amat = true) : amat.length = 17 := by
  simp only [aShape, Bool.and_eq_true] at hs
  exact Nat.eq_of_beq_eq_true hs.1

theorem aShape_mem (hs : aShape amat = true) {r : List GS} (hr : r ∈ amat) :
    r.length ≤ 17 ∧ ∀ e ∈ r, e.1.2 ≤ 2 ^ 48 ∧ e.2.2 ≤ 2 ^ 48 := by
  simp only [aShape, Bool.and_eq_true, List.all_eq_true] at hs
  have h := hs.2 r hr
  refine ⟨Nat.le_of_ble_eq_true h.1, fun e he => ?_⟩
  have h2 := h.2 e he
  have h48 : (1 : ℕ) <<< 48 = 2 ^ 48 := by norm_num
  rw [h48] at h2
  exact ⟨Nat.le_of_ble_eq_true h2.1, Nat.le_of_ble_eq_true h2.2⟩

theorem aShape_row (hs : aShape amat = true) (j : ℕ) : (amat.getD j []).length ≤ 17 := by
  rcases getD_mem_or amat j [] with h | h
  · exact (aShape_mem amat hs h).1
  · rw [h]
    simp

theorem aE_bound (hs : aShape amat = true) (j i : ℕ) : l1 (aE amat j i) ≤ 2 ^ 49 := by
  have hparts : ((amat.getD j []).getD i gzero).1.2 ≤ 2 ^ 48 ∧ ((amat.getD j []).getD i gzero).2.2 ≤ 2 ^ 48 := by
    rcases getD_mem_or (amat.getD j []) i gzero with h | h
    · rcases getD_mem_or amat j [] with hr | hr
      · exact (aShape_mem amat hs hr).2 _ h
      · rw [hr] at h
        simp at h
    · rw [h]
      simp [gzero, szero]
  unfold aE l1
  simp only [gval]
  have h1 : |sval ((amat.getD j []).getD i gzero).1| ≤ 2 ^ 48 := by
    have := mag_eq_natAbs ((amat.getD j []).getD i gzero).1
    rw [Int.abs_eq_natAbs, ← this]
    exact_mod_cast hparts.1
  have h2 : |sval ((amat.getD j []).getD i gzero).2| ≤ 2 ^ 48 := by
    have := mag_eq_natAbs ((amat.getD j []).getD i gzero).2
    rw [Int.abs_eq_natAbs, ← this]
    exact_mod_cast hparts.2
  have h3 : (2 : ℤ) ^ 49 = 2 ^ 48 + 2 ^ 48 := by norm_num
  linarith

/-! ### The rows of `H` -/

/-- `H_j`, packed. -/
def hsOf (j : ℕ) : GS := combo (amat.getD j []) (rowsOf hb a k) gzero

/-- Short names for the polynomials of this interval. -/
noncomputable abbrev hCI (s j k' : ℕ) : GI := hC (a : ℤ) (dW k) (hE hb) (aE amat) s j k'
noncomputable abbrev gCI (s j t : ℕ) : GI := gC (a : ℤ) (dW k) (hE hb) (aE amat) s j t

theorem hs_val_rows (hs : aShape amat = true) (j : ℕ) :
    gval (hsOf hb a k amat j) = ∑ i ∈ range 17, aE amat j i * rowV hb a k (i + 1) := by
  have hle : (amat.getD j []).length ≤ (rowsOf hb a k).length := by
    rw [rows_length]
    exact aShape_row amat hs j
  unfold hsOf
  rw [combo_val _ _ _ hle, gval_gzero, zero_add]
  have hsub : range (amat.getD j []).length ⊆ range 17 := range_subset_range.2 (aShape_row amat hs j)
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [rows_getD hb a k i (by have := aShape_row amat hs j; omega)]
    rfl
  · intro i _ hi
    have hi' : (amat.getD j []).length ≤ i := by simpa using hi
    have h0 : aE amat j i = 0 := by
      unfold aE
      rw [List.getD_eq_default _ _ hi', gval_gzero]
    rw [h0, zero_mul]

theorem rowV_eval (i : ℕ) :
    rowV hb a k (i + 1) = ∑ k' ∈ range 18, (bP (a : ℤ) (dW k) (hE hb) i k').eval (gI (tW k)) * gI (xW k) ^ k' := by
  simp only [rowV]
  refine sum_congr rfl fun k' _ => ?_
  rw [bP_eval]
  rfl

theorem hs_val_expand (hs : aShape amat = true) (j : ℕ) :
    gval (hsOf hb a k amat j) = ∑ k' ∈ range 18, ∑ s ∈ range 35, hCI hb a k amat s j k' * gI (tW k ^ s * xW k ^ k') := by
  rw [hs_val_rows hb a k amat hs]
  simp only [rowV_eval, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun k' hk' => ?_
  have hdeg : (hP (a : ℤ) (dW k) (hE hb) (aE amat) j k').natDegree < 35 := by
    have := hP_natDegree (a := (a : ℤ)) (D := dW k) (h := hE hb) (A := aE amat) j k'
      (by have := mem_range.1 hk'; omega)
    omega
  have heval := eval_eq_sum_range' hdeg (gI (tW k))
  have hsplit : ∑ i ∈ range 17, aE amat j i * ((bP (a : ℤ) (dW k) (hE hb) i k').eval (gI (tW k)) * gI (xW k) ^ k') =
      (hP (a : ℤ) (dW k) (hE hb) (aE amat) j k').eval (gI (tW k)) * gI (xW k) ^ k' := by
    unfold hP
    rw [eval_finsetSum, sum_mul]
    refine sum_congr rfl fun i _ => ?_
    rw [eval_mul, eval_C]
    ring
  rw [hsplit, heval, sum_mul]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_assoc, gI_pow, gI_pow, gI_mul]
  rfl

/-- One additive projection of a Gaussian integer, `re` or `im`. -/
theorem hs_pi (π : GI →+ ℤ) (hπ : ∀ z n, π (z * gI n) = π z * n) (hs : aShape amat = true) (j : ℕ) :
    π (gval (hsOf hb a k amat j)) =
      ∑ i ∈ range (18 * 35), π (hCI hb a k amat (i / 18) j (i % 18)) * (2 ^ wOf k) ^ i := by
  rw [hs_val_expand hb a k amat hs, map_sum]
  simp only [map_sum, hπ]
  rw [sum_comm, sum_two_level 18 35]
  refine sum_congr rfl fun s _ => sum_congr rfl fun k' hk' => ?_
  have hk2 := mem_range.1 hk'
  have hdiv : (18 * s + k') / 18 = s := by omega
  have hmod : (18 * s + k') % 18 = k' := by omega
  rw [hdiv, hmod, pow_add, pow_mul]

end interval

end Smale.RCheck
