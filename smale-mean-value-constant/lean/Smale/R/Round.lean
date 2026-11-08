/-
Smale/R/Round.lean — The rounded data against the exact data, and what a chain of dyadic intervals covers.
-/
import Smale.R.Interval
import Smale.R.Hb

namespace Smale.RCheck

open Polynomial Finset Smale.RK Matrix ComplexConjugate

/-! ### The rounded coefficients -/

/-- `hb` is `hGQ` rounded at `2^-64`, and its entries have the size the bounds assume. -/
def roundOK (hb : List GS) : Bool :=
  (List.range 18).all fun l =>
    let g := Exact.hGQ.getD (l + 1) Exact.GQ.zero
    let e := hb.getD l gzero
    decide (|g.re * 2 ^ 64 - (sval e.1 : ℚ)| ≤ 1) && decide (|g.im * 2 ^ 64 - (sval e.2 : ℚ)| ≤ 1) &&
      decide (|sval e.1| + |sval e.2| ≤ 2 ^ 75)

theorem roundOK_hb : roundOK hb = true := by decide +kernel

theorem hb_size (l : ℕ) (hl : l ≤ 17) : l1 (hE hb l) ≤ 2 ^ 75 := by
  have h := roundOK_hb
  simp only [roundOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact (h l (by omega)).2

theorem hb_round (l : ℕ) (hl : l ≤ 17) : ‖(2 ^ 64 : ℂ) * Hdata.coeff (l + 1) - toC (hE hb l)‖ ≤ 2 := by
  have h := roundOK_hb
  simp only [roundOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hre, him⟩, -⟩ := h l (by omega)
  rw [Exact.Hdata_eq, Exact.coeff_toPoly]
  set g := Exact.hGQ.getD (l + 1) Exact.GQ.zero with hg
  set e := hb.getD l gzero with he
  have hreR : |((g.re : ℝ) * 2 ^ 64 - (sval e.1 : ℝ))| ≤ 1 := by exact_mod_cast hre
  have himR : |((g.im : ℝ) * 2 ^ 64 - (sval e.2 : ℝ))| ≤ 1 := by exact_mod_cast him
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have hz1 : ((2 ^ 64 : ℂ) * g.toC - toC (hE hb l)).re = (g.re : ℝ) * 2 ^ 64 - (sval e.1 : ℝ) := by
    have h1 : (toC (hE hb l)).re = (sval e.1 : ℝ) := re_toC _
    have h2 : ((2 ^ 64 : ℂ) * g.toC).re = (g.re : ℝ) * 2 ^ 64 := by
      have h3 : ((2 ^ 64 : ℂ)) = (((2 : ℝ) ^ 64 : ℝ) : ℂ) := by push_cast; rfl
      rw [h3, Complex.re_ofReal_mul, Exact.GQ.toC_re]
      ring
    rw [Complex.sub_re, h1, h2]
  have hz2 : ((2 ^ 64 : ℂ) * g.toC - toC (hE hb l)).im = (g.im : ℝ) * 2 ^ 64 - (sval e.2 : ℝ) := by
    have h1 : (toC (hE hb l)).im = (sval e.2 : ℝ) := (GaussianInt.intCast_im _).symm
    have h2 : ((2 ^ 64 : ℂ) * g.toC).im = (g.im : ℝ) * 2 ^ 64 := by
      have h3 : ((2 ^ 64 : ℂ)) = (((2 : ℝ) ^ 64 : ℝ) : ℂ) := by push_cast; rfl
      rw [h3, Complex.im_ofReal_mul, Exact.GQ.toC_im]
      ring
    rw [Complex.sub_im, h1, h2]
  rw [hz1, hz2]
  linarith

/-! ### The cover -/

/-- The dyadic intervals of the list follow each other, from `0` to `1`, at scale `2^20`. -/
def coverChain : ℕ → List (ℕ × ℕ) → Bool
  | cur, [] => Nat.beq cur (2 ^ 20)
  | cur, (a, k) :: rest =>
    Nat.ble k 20 && Nat.ble 1 a && Nat.beq ((a - 1) * 2 ^ (20 - k)) cur &&
      coverChain ((a + 1) * 2 ^ (20 - k)) rest

theorem coverChain_sound (c : ℝ) : ∀ (L : List (ℕ × ℕ)) (cur : ℕ), coverChain cur L = true →
    (cur : ℝ) ≤ 2 ^ 20 * c → c ≤ 1 → L ≠ [] →
    ∃ e ∈ L, (e.1 : ℝ) - 1 ≤ 2 ^ e.2 * c ∧ (2 : ℝ) ^ e.2 * c ≤ e.1 + 1 := by
  intro L
  induction L with
  | nil => intro _ _ _ _ h; exact absurd rfl h
  | cons e rest ih =>
    intro cur hchain hcur hc1 _
    obtain ⟨a, k⟩ := e
    simp only [coverChain, Bool.and_eq_true] at hchain
    obtain ⟨⟨⟨hk, ha⟩, hlow⟩, hnext⟩ := hchain
    have hk' : k ≤ 20 := Nat.le_of_ble_eq_true hk
    have ha' : 1 ≤ a := Nat.le_of_ble_eq_true ha
    have hlow' : (a - 1) * 2 ^ (20 - k) = cur := Nat.eq_of_beq_eq_true hlow
    have hsplit : (2 : ℝ) ^ 20 = 2 ^ k * 2 ^ (20 - k) := by
      rw [← pow_add]
      congr 1
      omega
    have hS : (0 : ℝ) < 2 ^ (20 - k) := by positivity
    by_cases hin : (2 : ℝ) ^ k * c ≤ a + 1
    · refine ⟨(a, k), List.mem_cons_self .., ?_, hin⟩
      have h1 : ((a : ℝ) - 1) * 2 ^ (20 - k) ≤ 2 ^ 20 * c := by
        rw [← Nat.cast_one (R := ℝ), ← Nat.cast_sub ha']
        calc (((a - 1 : ℕ) : ℝ)) * 2 ^ (20 - k) = (((a - 1) * 2 ^ (20 - k) : ℕ) : ℝ) := by push_cast; rfl
          _ = (cur : ℝ) := by rw [hlow']
          _ ≤ _ := hcur
      have h2 : ((a : ℝ) - 1) * 2 ^ (20 - k) ≤ (2 ^ k * c) * 2 ^ (20 - k) := by
        calc _ ≤ 2 ^ 20 * c := h1
          _ = _ := by rw [hsplit]; ring
      exact le_of_mul_le_mul_right h2 hS
    · have hup : ((a : ℝ) + 1) * 2 ^ (20 - k) < 2 ^ 20 * c := by
        have h1 : (a : ℝ) + 1 < 2 ^ k * c := not_le.1 hin
        calc ((a : ℝ) + 1) * 2 ^ (20 - k) < (2 ^ k * c) * 2 ^ (20 - k) := mul_lt_mul_of_pos_right h1 hS
          _ = _ := by rw [hsplit]; ring
      have hcast : (((a + 1) * 2 ^ (20 - k) : ℕ) : ℝ) = ((a : ℝ) + 1) * 2 ^ (20 - k) := by push_cast; rfl
      cases rest with
      | nil =>
        simp only [coverChain] at hnext
        have heq : (a + 1) * 2 ^ (20 - k) = 2 ^ 20 := Nat.eq_of_beq_eq_true hnext
        have h3 : ((a : ℝ) + 1) * 2 ^ (20 - k) = 2 ^ 20 := by
          rw [← hcast, heq]
          norm_num
        rw [h3] at hup
        have : (2 : ℝ) ^ 20 * c ≤ 2 ^ 20 := by
          have h4 : (0 : ℝ) < 2 ^ 20 := by positivity
          nlinarith
        linarith
      | cons f fs =>
        obtain ⟨x, hx, hx2⟩ := ih _ hnext (by rw [hcast]; exact hup.le) hc1 (by simp)
        exact ⟨x, List.mem_cons_of_mem _ hx, hx2⟩

end Smale.RCheck
