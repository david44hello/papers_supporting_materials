/-
NagataHigman/Defs/FirstReturn.lean — definitions for Proposition 2.1 steps (3)-(5) and v1.02 Remark 2.3 (cut in v1.03) (package B2).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.04, lines 300-302 (s, Arc)
and v1.02 line 302 (S_X). A NEW Defs file (not an extension of Defs/WordCycle.lean), so that adding it rebuilds nothing.
-/
import Mathlib
import NagataHigman.Defs.GroupAlgebra

set_option autoImplicit false

noncomputable section

namespace NagataHigman

open Equiv Finset

variable (F : Type*) [Field F]

/-- `S_X = ∑_{π ∈ Sym(X)} π` (paper v1.02 line 302; v1.04 does not use `S_X`); `Sym(X)` = the permutations moving only points of `X`. -/
def symGroupSum {N : ℕ} (X : Finset (Fin N)) : GrpAlg F N :=
  ∑ π ∈ univ.filter (fun π : Perm (Fin N) => π.support ⊆ X), perm F π

variable {N : ℕ}

open Classical in
/-- The return time to `X` (paper line 300): the least `k ≥ 1` with `τ^k(x) ∈ X` (`0` if there is none). -/
def returnTime (τ : Perm (Fin N)) (X : Finset (Fin N)) (x : Fin N) : ℕ :=
  if h : ∃ k, 0 < k ∧ (τ ^ k) x ∈ X then Nat.find h else 0

/-- The first-return map as a function (paper line 300): `s(x) = τ^k(x)` for the least `k ≥ 1` with `τ^k(x) ∈ X`,
for `x ∈ X`; points outside `X` are fixed. -/
def firstReturnFun (τ : Perm (Fin N)) (X : Finset (Fin N)) (x : Fin N) : Fin N :=
  if x ∈ X then (τ ^ returnTime τ X x) x else x

namespace FirstReturn

theorem returnTime_spec {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (h : ∃ k, 0 < k ∧ (τ ^ k) x ∈ X) :
    0 < returnTime τ X x ∧ (τ ^ returnTime τ X x) x ∈ X := by
  classical
  unfold returnTime
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem returnTime_min {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (h : ∃ k, 0 < k ∧ (τ ^ k) x ∈ X)
    {j : ℕ} (hj : 0 < j) (hjr : j < returnTime τ X x) : (τ ^ j) x ∉ X := by
  classical
  unfold returnTime at hjr
  rw [dite_eq_left h] at hjr
  exact fun hmem => Nat.find_min h hjr ⟨hj, hmem⟩

theorem exists_return_of_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) :
    ∃ k, 0 < k ∧ (τ ^ k) x ∈ X :=
  ⟨orderOf τ, orderOf_pos τ, by rw [pow_orderOf_eq_one]; exact hx⟩

/-- `τ^a(x) = τ^b(y)` with `a ≤ b` gives `x = τ^(b-a)(y)`. -/
theorem eq_pow_sub_of_pow_eq {τ : Perm (Fin N)} {a b : ℕ} {x y : Fin N} (hab : a ≤ b)
    (h : (τ ^ a) x = (τ ^ b) y) : x = (τ ^ (b - a)) y := by
  apply (τ ^ a).injective
  rw [h, ← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hab]

theorem firstReturnFun_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) :
    firstReturnFun τ X x ∈ X := by
  unfold firstReturnFun
  rw [ite_eq_left hx]
  exact (returnTime_spec (exists_return_of_mem hx)).2

/-- Two points of `X` with the same first return are equal. -/
theorem firstReturnFun_inj_of_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x y : Fin N} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : (τ ^ returnTime τ X x) x = (τ ^ returnTime τ X y) y) : x = y := by
  have hex := exists_return_of_mem (τ := τ) hx
  have hey := exists_return_of_mem (τ := τ) hy
  obtain ⟨hx0, -⟩ := returnTime_spec hex
  obtain ⟨hy0, -⟩ := returnTime_spec hey
  rcases lt_trichotomy (returnTime τ X x) (returnTime τ X y) with hab | hab | hab
  · have e := eq_pow_sub_of_pow_eq hab.le hxy
    exact absurd (e ▸ hx) (returnTime_min hey (by omega) (by omega))
  · rw [hab] at hxy
    exact (τ ^ returnTime τ X y).injective hxy
  · have e := eq_pow_sub_of_pow_eq hab.le hxy.symm
    exact absurd (e ▸ hy) (returnTime_min hex (by omega) (by omega))

theorem firstReturnFun_injective (τ : Perm (Fin N)) (X : Finset (Fin N)) :
    Function.Injective (firstReturnFun τ X) := by
  intro x y hxy
  by_cases hx : x ∈ X <;> by_cases hy : y ∈ X
  · unfold firstReturnFun at hxy
    rw [ite_eq_left hx, ite_eq_left hy] at hxy
    exact firstReturnFun_inj_of_mem hx hy hxy
  · have h1 := firstReturnFun_mem (τ := τ) hx
    rw [hxy] at h1
    unfold firstReturnFun at h1
    rw [ite_eq_right hy] at h1
    exact absurd h1 hy
  · have h1 := firstReturnFun_mem (τ := τ) hy
    rw [← hxy] at h1
    unfold firstReturnFun at h1
    rw [ite_eq_right hx] at h1
    exact absurd h1 hx
  · unfold firstReturnFun at hxy
    rwa [ite_eq_right hx, ite_eq_right hy] at hxy

end FirstReturn

/-- The first-return map `s` of `τ` to `X` (paper line 300), as a permutation of `Fin N` fixing every point outside
`X`. -/
def firstReturn (τ : Perm (Fin N)) (X : Finset (Fin N)) : Perm (Fin N) :=
  Equiv.ofBijective (firstReturnFun τ X) (FirstReturn.firstReturnFun_injective τ X).bijective_of_finite

/-- The arc of `x ∈ X` (paper line 302): `Arc(x) = (τ(x), τ²(x), …, s(x))`. -/
def arc (τ : Perm (Fin N)) (X : Finset (Fin N)) (x : Fin N) : List (Fin N) :=
  (List.range (returnTime τ X x)).map fun i => (τ ^ (i + 1)) x

end NagataHigman

end
