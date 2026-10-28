/-
Smale/Proofs/GQPoly.lean — exact Gaussian-rational arithmetic for the data of Section 5. A computable type `GQ` of
Gaussian rationals and coefficient lists `GP = List GQ` (ascending) with sum, scalar multiple, product, derivative,
evaluation and the reversed conjugate; the map `toPoly : GP → ℂ[X]` turns a kernel computation (`decide +kernel` on
lists of rationals) into an identity of complex polynomials.
-/
import Smale.Defs.Data

namespace Smale.Exact

open Polynomial Complex ComplexConjugate

/-- A Gaussian rational `re + im·i`, computable (the kernel decides equalities of these). -/
structure GQ where
  re : ℚ
  im : ℚ
  deriving DecidableEq

namespace GQ

def zero : GQ := ⟨0, 0⟩
def add (a b : GQ) : GQ := ⟨a.re + b.re, a.im + b.im⟩
def mul (a b : GQ) : GQ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def neg (a : GQ) : GQ := ⟨-a.re, -a.im⟩
def cnj (a : GQ) : GQ := ⟨a.re, -a.im⟩
def ofQ (q : ℚ) : GQ := ⟨q, 0⟩

/-- The complex number `a.re + a.im·i`. -/
noncomputable def toC (a : GQ) : ℂ := gq a.re a.im

theorem toC_re (a : GQ) : a.toC.re = a.re := by simp [toC, gq]

theorem toC_im (a : GQ) : a.toC.im = a.im := by simp [toC, gq]

theorem toC_zero : zero.toC = 0 := by
  apply Complex.ext <;> simp [toC_re, toC_im, zero]

theorem toC_add (a b : GQ) : (add a b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [toC_re, toC_im, add]

theorem toC_mul (a b : GQ) : (mul a b).toC = a.toC * b.toC := by
  apply Complex.ext <;> simp [toC_re, toC_im, mul]

theorem toC_neg (a : GQ) : (neg a).toC = -a.toC := by
  apply Complex.ext <;> simp [toC_re, toC_im, neg]

theorem toC_cnj (a : GQ) : (cnj a).toC = conj a.toC := by
  apply Complex.ext <;> simp [toC_re, toC_im, cnj]

theorem toC_ofQ (q : ℚ) : (ofQ q).toC = (q : ℂ) := by
  apply Complex.ext <;> simp [toC_re, toC_im, ofQ]

theorem toC_injective : Function.Injective toC := by
  intro a b h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [toC_re, toC_im, Rat.cast_inj] at hre him
  cases a; cases b; simp_all

theorem toC_eq_zero_iff (a : GQ) : a.toC = 0 ↔ a = zero := by
  rw [← toC_zero]; exact toC_injective.eq_iff

end GQ

/-- Coefficient lists, ascending: `[c₀, c₁, …]` is `c₀ + c₁X + ⋯`. -/
abbrev GP := List GQ

/-- The complex polynomial of a coefficient list. -/
noncomputable def toPoly : GP → ℂ[X]
  | [] => 0
  | c :: p => C c.toC + X * toPoly p

def padd : GP → GP → GP
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => GQ.add a b :: padd p q

def psmul (a : GQ) : GP → GP
  | [] => []
  | c :: p => GQ.mul a c :: psmul a p

def pneg : GP → GP
  | [] => []
  | c :: p => GQ.neg c :: pneg p

def pmul : GP → GP → GP
  | [], _ => []
  | a :: p, q => padd (psmul a q) (GQ.zero :: pmul p q)

/-- `pderivAux k [c₀, c₁, …] = [k c₀, (k+1) c₁, …]`. -/
def pderivAux : ℕ → GP → GP
  | _, [] => []
  | k, c :: p => GQ.mul (GQ.ofQ k) c :: pderivAux (k + 1) p

def pderiv : GP → GP
  | [] => []
  | _ :: p => pderivAux 1 p

/-- Horner evaluation. -/
def peval : GP → GQ → GQ
  | [], _ => GQ.zero
  | c :: p, z => GQ.add c (GQ.mul z (peval p z))

/-- `p - q = 0` coefficientwise (lists of any lengths). -/
def peq (p q : GP) : Bool := (padd p (pneg q)).all (· == GQ.zero)

theorem toPoly_nil : toPoly [] = 0 := rfl

theorem toPoly_cons (c : GQ) (p : GP) : toPoly (c :: p) = C c.toC + X * toPoly p := rfl

theorem toPoly_padd (p q : GP) : toPoly (padd p q) = toPoly p + toPoly q := by
  induction p generalizing q with
  | nil => simp [padd, toPoly]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, toPoly]
    | cons b q => simp only [padd, toPoly_cons, ih, GQ.toC_add, map_add]; ring

theorem toPoly_psmul (a : GQ) (p : GP) : toPoly (psmul a p) = C a.toC * toPoly p := by
  induction p with
  | nil => simp [psmul, toPoly]
  | cons c p ih => simp only [psmul, toPoly_cons, ih, GQ.toC_mul, map_mul]; ring

theorem toPoly_pneg (p : GP) : toPoly (pneg p) = -toPoly p := by
  induction p with
  | nil => simp [pneg, toPoly]
  | cons c p ih => simp only [pneg, toPoly_cons, ih, GQ.toC_neg, map_neg]; ring

theorem toPoly_pmul (p q : GP) : toPoly (pmul p q) = toPoly p * toPoly q := by
  induction p with
  | nil => simp [pmul, toPoly]
  | cons a p ih =>
    simp only [pmul, toPoly_padd, toPoly_psmul, toPoly_cons, ih, GQ.toC_zero, map_zero]; ring

theorem toPoly_pderivAux (k : ℕ) (p : GP) :
    toPoly (pderivAux k p) = C (k : ℂ) * toPoly p + X * derivative (toPoly p) := by
  induction p generalizing k with
  | nil => simp [pderivAux, toPoly]
  | cons c p ih =>
    simp only [pderivAux, toPoly_cons, ih, GQ.toC_mul, GQ.toC_ofQ, derivative_C, derivative_mul,
      derivative_X, map_mul, Rat.cast_natCast, Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

theorem toPoly_pderiv (p : GP) : toPoly (pderiv p) = derivative (toPoly p) := by
  cases p with
  | nil => simp [pderiv, toPoly]
  | cons c p =>
    simp only [pderiv, toPoly_pderivAux, toPoly_cons, derivative_add, derivative_C, derivative_mul, derivative_X,
      Nat.cast_one, map_one]
    ring

theorem eval_toPoly (p : GP) (z : GQ) : (toPoly p).eval z.toC = (peval p z).toC := by
  induction p with
  | nil => simp [toPoly, peval, GQ.toC_zero]
  | cons c p ih => simp [toPoly_cons, peval, ih, GQ.toC_add, GQ.toC_mul]

theorem coeff_toPoly (p : GP) (k : ℕ) : (toPoly p).coeff k = (p.getD k GQ.zero).toC := by
  induction p generalizing k with
  | nil => simp [toPoly, GQ.toC_zero]
  | cons c p ih =>
    cases k with
    | zero => simp [toPoly_cons]
    | succ k => simp [toPoly_cons, coeff_X_mul, ih]

theorem toPoly_eq_zero_of_all {p : GP} (h : p.all (· == GQ.zero) = true) : toPoly p = 0 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [toPoly_cons, h.1, ih h.2, GQ.toC_zero]

/-- The kernel check `peq p q = true` proves `toPoly p = toPoly q`. -/
theorem toPoly_eq_of_peq {p q : GP} (h : peq p q = true) : toPoly p = toPoly q := by
  have h0 := toPoly_eq_zero_of_all h
  rw [toPoly_padd, toPoly_pneg] at h0
  exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h0)

theorem toPoly_eq_sum (p : GP) :
    toPoly p = ∑ k ∈ Finset.range p.length, C (p.getD k GQ.zero).toC * X ^ k := by
  induction p with
  | nil => simp [toPoly]
  | cons c p ih =>
    rw [toPoly_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- The degree of `toPoly p` from its last coefficient. -/
theorem natDegree_toPoly {p : GP} {n : ℕ} (hlen : p.length = n + 1) (hlast : p.getD n GQ.zero ≠ GQ.zero) :
    (toPoly p).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_toPoly, List.getD_eq_default _ _ (by rw [hlen]; exact_mod_cast hk), GQ.toC_zero]
  · rw [coeff_toPoly]; exact (GQ.toC_eq_zero_iff _).not.mpr hlast

end Smale.Exact
