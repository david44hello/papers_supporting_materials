/-
Lem81Stable.lean — Lemma 8.1 of paper 013 (sec_small_roots.tex of the posting copy, lines 29-30, 43, 45-50): the five rows about the
standard system that do not depend on review a3: `lem_8_1_orthonormal`, `std_sys_trace_zero`, `cliffProd_nine_symm_inv`,
`lem_8_1_Omega_zero`, `lem_8_1_Omega_pi`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route for `Ω(0) = ±I` (lines 46-49; the paper's reason: nine is odd, so `Ω` commutes with every `S_i`, and the `S_i` act
irreducibly): `Ω² = I`, so if `Ω ≠ -I` there is a nonzero `u` with `Ωu = u`. Every `S_i` maps fixed vectors of `Ω` to
fixed vectors. With `S_0` one gets a fixed vector in `𝕆 ⊕ 0` or `0 ⊕ 𝕆`; the swap maps `x ↦ (e x̄_2, x̄_1 e)` (linear
combinations of `S_1, …, S_8`) and the left alternative law `a(āz) = |a|²z` then reach every vector, so `Ω = I`.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.StdSystem
import Osserman.Proofs.OctonionFacts

namespace Osserman.Proofs.Lem81

open Osserman Matrix Osserman.Proofs.StdSystem Osserman.Proofs.OctonionLinear Osserman.Proofs.OctonionFacts

/-! ## Signs of anticommuting products, in any ring -/

section Signs

variable {R : Type*} [Ring R]

/-- If `b` anticommutes with every factor of `l`, then `b` passes through the product with the sign `(-1)^|l|`. -/
lemma mul_prod_anticomm (b : R) :
    ∀ l : List R, (∀ a ∈ l, b * a = -(a * b)) → b * l.prod = ((-1 : ℤ) ^ l.length) • (l.prod * b)
  | [], _ => by simp
  | a :: t, h => by
    have head : b * a = -(a * b) := h a (by simp)
    have tail := mul_prod_anticomm b t fun x hx => h x (by simp [hx])
    rw [List.prod_cons, List.length_cons, ← mul_assoc, head, neg_mul, mul_assoc, tail, mul_smul_comm, pow_succ,
      mul_neg_one, neg_smul, mul_assoc]

/-- The same, with the product on the left. -/
lemma prod_mul_anticomm (b : R) (l : List R) (h : ∀ a ∈ l, b * a = -(a * b)) :
    l.prod * b = ((-1 : ℤ) ^ l.length) • (b * l.prod) := by
  rw [mul_prod_anticomm b l h, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

/-- In a product of `k` pairwise anticommuting factors, each factor passes through with the sign `(-1)^(k+1)`. -/
lemma mul_prod_ofFn_anticomm :
    ∀ {k : ℕ} (H : Fin k → R), (∀ i j, i ≠ j → H i * H j = -(H j * H i)) →
      ∀ i, H i * (List.ofFn H).prod = ((-1 : ℤ) ^ (k + 1)) • ((List.ofFn H).prod * H i)
  | 0, _, _, i => i.elim0
  | k + 1, H, hH, i => by
    have tail : ∀ x ∈ List.ofFn (fun j : Fin k => H j.succ), H 0 * x = -(x * H 0) := by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hH 0 j.succ (Fin.succ_ne_zero j).symm
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [mul_assoc, prod_mul_anticomm (H 0) _ tail, List.length_ofFn, mul_smul_comm, smul_smul, ← pow_add,
        show k + 1 + 1 + k = 2 * (k + 1) by ring, pow_mul, neg_one_sq, one_pow, one_smul]
    · have rest := mul_prod_ofFn_anticomm (fun j : Fin k => H j.succ)
        (fun a b hab => hH a.succ b.succ fun h => hab (Fin.succ_injective _ h)) j
      rw [← mul_assoc, hH j.succ 0 (Fin.succ_ne_zero j), neg_mul, mul_assoc, rest, mul_smul_comm, ← mul_assoc,
        pow_succ (-1 : ℤ) (k + 1), mul_neg_one, neg_smul]

/-- Reversing `k` pairwise anticommuting factors gives the sign `(-1)^(k choose 2)`. -/
lemma prod_reverse_ofFn_anticomm :
    ∀ {k : ℕ} (H : Fin k → R), (∀ i j, i ≠ j → H i * H j = -(H j * H i)) →
      (List.ofFn H).reverse.prod = ((-1 : ℤ) ^ k.choose 2) • (List.ofFn H).prod
  | 0, _, _ => by simp
  | k + 1, H, hH => by
    have tail : ∀ x ∈ List.ofFn (fun j : Fin k => H j.succ), H 0 * x = -(x * H 0) := by
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hH 0 j.succ (Fin.succ_ne_zero j).symm
    have rest := prod_reverse_ofFn_anticomm (fun j : Fin k => H j.succ)
      (fun a b hab => hH a.succ b.succ fun h => hab (Fin.succ_injective _ h))
    have count : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    rw [List.ofFn_succ, List.reverse_cons, List.prod_append, List.prod_singleton, rest, smul_mul_assoc,
      prod_mul_anticomm (H 0) _ tail, List.length_ofFn, smul_smul, ← pow_add, List.prod_cons, count]

/-- Negating every factor of a product gives the sign `(-1)^|l|`. -/
lemma prod_map_neg_smul : ∀ l : List R, (l.map Neg.neg).prod = ((-1 : ℤ) ^ l.length) • l.prod
  | [] => by simp
  | a :: t => by
    rw [List.map_cons, List.prod_cons, prod_map_neg_smul t, List.prod_cons, List.length_cons, mul_smul_comm, pow_succ,
      mul_neg_one, neg_smul, neg_mul, smul_neg]

/-- If every factor squares to `1`, a product times its reverse is `1`. -/
lemma prod_mul_prod_reverse : ∀ l : List R, (∀ a ∈ l, a * a = 1) → l.prod * l.reverse.prod = 1
  | [], _ => by simp
  | a :: t, h => by
    rw [List.prod_cons, List.reverse_cons, List.prod_append, List.prod_singleton, mul_assoc, ← mul_assoc t.prod,
      prod_mul_prod_reverse t fun x hx => h x (by simp [hx]), one_mul, h a (by simp)]

end Signs

/-! ## Symmetric Clifford systems -/

section Clifford

variable {n k : ℕ} {H : Fin k → Matrix (Fin n) (Fin n) ℝ}

lemma cliff_anticomm (hH : IsSymmCliffordSystem H) {i j : Fin k} (hij : i ≠ j) : H i * H j = -(H j * H i) :=
  eq_neg_of_add_eq_zero_left (by simpa [hij] using hH.2 i j)

lemma cliff_sq (hH : IsSymmCliffordSystem H) (i : Fin k) : H i * H i = 1 := by
  have two : H i * H i + H i * H i = 2 := by simpa using hH.2 i i
  have scaled : (2 : ℝ) • (H i * H i) = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [two_smul, two_smul, two, one_add_one_eq_two]
  exact smul_right_injective _ two_ne_zero scaled

/-- `⟨H_ix, H_jx⟩ = δ_ij |x|²` for a symmetric Clifford system. -/
lemma cliff_dot (hH : IsSymmCliffordSystem H) (i j : Fin k) (x : Vec n) :
    (H i *ᵥ x) ⬝ᵥ (H j *ᵥ x) = if i = j then x ⬝ᵥ x else 0 := by
  have expand (a b : Fin k) : (H a *ᵥ x) ⬝ᵥ (H b *ᵥ x) = x ⬝ᵥ ((H a * H b) *ᵥ x) := by
    rw [← mulVec_mulVec, dotProduct_mulVec x (H a), ← mulVec_transpose, hH.1 a]
  split_ifs with hij
  · rw [hij, expand, cliff_sq hH, one_mulVec]
  · have swapped := expand j i
    rw [dotProduct_comm, cliff_anticomm hH (Ne.symm hij), neg_mulVec, dotProduct_neg, ← expand i j] at swapped
    linarith

/-- A member of a symmetric Clifford system with at least two members is trace-free: `H_i = -H_jH_iH_j`. -/
lemma cliff_trace (hH : IsSymmCliffordSystem H) {i j : Fin k} (hij : i ≠ j) : (H i).trace = 0 := by
  have conj : H j * (H i * H j) = -H i := by
    rw [← mul_assoc, cliff_anticomm hH hij.symm, neg_mul, mul_assoc, cliff_sq hH, mul_one]
  have cyc : (H j * (H i * H j)).trace = (H i).trace := by
    rw [trace_mul_comm, mul_assoc, cliff_sq hH, mul_one]
  rw [conj, trace_neg] at cyc
  linarith

/-- For an odd number of factors every factor commutes with the ordered product. -/
lemma cliff_comm_prod (hH : IsSymmCliffordSystem H) (hk : Even (k + 1)) (i : Fin k) :
    H i * cliffProd H = cliffProd H * H i := by
  rw [cliffProd, mul_prod_ofFn_anticomm H (fun a b hab => cliff_anticomm hH hab) i, hk.neg_one_pow, one_smul]

/-- The ordered product reversed, for `k(k-1)/2` even. -/
lemma cliff_reverse (hH : IsSymmCliffordSystem H) (hk : Even (k.choose 2)) :
    (List.ofFn H).reverse.prod = cliffProd H := by
  rw [cliffProd, prod_reverse_ofFn_anticomm H (fun a b hab => cliff_anticomm hH hab), hk.neg_one_pow, one_smul]

end Clifford

/-! ## The five rows -/

/-- **Lemma 8.1, proof** (lines 29-30): `⟨S_ix, S_jx⟩ = δ_ij q`. -/
theorem lem_8_1_orthonormal_proved (x : Vec 16) (i j : Fin 9) :
    (stdSys i *ᵥ x) ⬝ᵥ (stdSys j *ᵥ x) = if i = j then x ⬝ᵥ x else 0 :=
  cliff_dot sec6_std_system_proved.2 i j x

/-- **Lemma 8.1, proof** (line 43): `tr S_i = 0`. -/
theorem std_sys_trace_zero_proved (i : Fin 9) : (stdSys i).trace = 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact cliff_trace sec6_std_system_proved.2 hj.symm

/-- **Lemma 8.1, proof** (line 45): nine symmetric Clifford matrices have a symmetric involutive product. -/
theorem cliffProd_nine_symm_inv_proved {n : ℕ} (H : Fin 9 → Matrix (Fin n) (Fin n) ℝ)
    (hH : IsSymmCliffordSystem H) :
    (cliffProd H)ᵀ = cliffProd H ∧ cliffProd H * cliffProd H = 1 := by
  have reverse := cliff_reverse hH (by decide)
  have symm : (List.ofFn H).map transpose = List.ofFn H := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hH.1 i
  refine ⟨?_, ?_⟩
  · rw [cliffProd, transpose_list_prod, symm]
    exact reverse
  · rw [show cliffProd H * cliffProd H = (List.ofFn H).prod * (List.ofFn H).reverse.prod by rw [reverse]; rfl]
    exact prod_mul_prod_reverse _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact cliff_sq hH i

/-! ### `Ω = S_0 ⋯ S_8` is `±I` -/

section Omega

local notation "Ω" => cliffProd stdSys

lemma omega_comm (i : Fin 9) : stdSys i * Ω = Ω * stdSys i :=
  cliff_comm_prod sec6_std_system_proved.2 (by decide) i

lemma omega_sq : Ω * Ω = 1 := (cliffProd_nine_symm_inv_proved stdSys sec6_std_system_proved.2).2

lemma omega_fix_std {w : Vec 16} (hw : Ω *ᵥ w = w) (i : Fin 9) : Ω *ᵥ (stdSys i *ᵥ w) = stdSys i *ᵥ w := by
  rw [mulVec_mulVec, ← omega_comm, ← mulVec_mulVec, hw]

lemma std_zero_pair (a b : Vec 8) : stdSys 0 *ᵥ octPair a b = octPair a (-b) := by
  rw [std_mulVec]
  simp [stdSysFun]

lemma std_succ_mulVec (k : Fin 8) (x : Vec 16) : stdSys k.succ *ᵥ x = swapFun (octBasis k) x := by
  rw [std_mulVec]
  simp [stdSysFun, swapFun]

lemma swap_smul_e (c : ℝ) (e : Vec 8) (x : Vec 16) : swapFun (c • e) x = c • swapFun e x := by
  simp only [swapFun, omul_smul_left, omul_smul_right, pair_smul]

lemma swap_sum_basis (e : Vec 8) (x : Vec 16) : swapFun e x = ∑ k, e k • swapFun (octBasis k) x := by
  let L : Vec 8 →ₗ[ℝ] Vec 16 :=
    { toFun := fun f => swapFun f x
      map_add' := fun f g => swap_add_e f g x
      map_smul' := fun c f => swap_smul_e c f x }
  have basis : e = ∑ k, e k • octBasis k := by
    ext j
    simp [octBasis, Finset.sum_apply, Pi.single_apply]
  calc swapFun e x = L e := rfl
    _ = L (∑ k, e k • octBasis k) := by rw [← basis]
    _ = ∑ k, e k • swapFun (octBasis k) x := by simp [L, map_sum]

lemma omega_fix_swap {w : Vec 16} (hw : Ω *ᵥ w = w) (e : Vec 8) : Ω *ᵥ swapFun e w = swapFun e w := by
  rw [swap_sum_basis, mulVec_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mulVec_smul, ← std_succ_mulVec, omega_fix_std hw]

lemma oconj_zero : oconj 0 = 0 := by
  simpa using oconj_smul 0 0

lemma pair_sub (a b c d : Vec 8) : octPair a b - octPair c d = octPair (a - c) (b - d) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℝ (octPair c d), pair_smul, pair_add,
    neg_one_smul, neg_one_smul]

/-- From a fixed vector `(a, 0)` with `a ≠ 0`, every `(0, z)` is fixed: `(0, z) = swap_e(a, 0)` with
`e = |a|⁻² a z` (left alternative law). -/
lemma omega_fix_second {a : Vec 8} (ha : a ≠ 0) (hfix : Ω *ᵥ octPair a 0 = octPair a 0) (z : Vec 8) :
    Ω *ᵥ octPair 0 z = octPair 0 z := by
  have norm : a ⬝ᵥ a ≠ 0 := fun h => ha (dotProduct_self_eq_zero.mp h)
  have hit : swapFun ((a ⬝ᵥ a)⁻¹ • omul a z) (octPair a 0) = octPair 0 z := by
    have alt := oct_left_alt_proved (oconj a) z
    rw [oconj_invol, oconj_dot] at alt
    simp only [swapFun, first_pair, second_pair, oconj_zero, omul_zero, omul_smul_right, alt, smul_smul,
      inv_mul_cancel₀ norm, one_smul]
  rw [← hit]
  exact omega_fix_swap hfix _

/-- If every `(0, z)` is fixed, every vector is fixed: `(y, 0) = S_1(0, ȳ)`. -/
lemma omega_fix_all (hsecond : ∀ z, Ω *ᵥ octPair 0 z = octPair 0 z) (x : Vec 16) : Ω *ᵥ x = x := by
  have first (y : Vec 8) : Ω *ᵥ octPair y 0 = octPair y 0 := by
    have hit : swapFun oone (octPair 0 (oconj y)) = octPair y 0 := by
      simp only [swapFun, first_pair, second_pair, oconj_invol, one_omul, oconj_zero, zero_omul]
    rw [← hit]
    exact omega_fix_swap (hsecond _) _
  have split : x = octPair (oct1 x) 0 + octPair 0 (oct2 x) := by
    rw [pair_add, add_zero, zero_add, pair_parts]
  rw [split, mulVec_add, first, hsecond]

/-- A nonzero fixed vector forces `Ω = I`. -/
lemma omega_eq_one {u : Vec 16} (hu : u ≠ 0) (hfix : Ω *ᵥ u = u) : Ω = 1 := by
  set a := oct1 u
  set b := oct2 u
  have hpair : u = octPair a b := (pair_parts u).symm
  have hS0 : stdSys 0 *ᵥ u = octPair a (-b) := by rw [hpair, std_zero_pair]
  have fixS0 := omega_fix_std hfix 0
  have hsecond : ∀ z, Ω *ᵥ octPair 0 z = octPair 0 z := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb
        have pair_zero : octPair 0 0 = 0 := by
          have h := pair_smul (0 : Vec 8) 0 0
          simp only [zero_smul] at h
          exact h.symm
        exact hu (by rw [hpair, ha, hb, pair_zero])
      have hminus : Ω *ᵥ octPair 0 (b + b) = octPair 0 (b + b) := by
        have diff : u - stdSys 0 *ᵥ u = octPair 0 (b + b) := by
          rw [hS0, hpair, pair_sub, sub_self, sub_neg_eq_add]
        rw [← diff, mulVec_sub, hfix, fixS0]
      have hbb : b + b ≠ 0 := by
        rw [← two_smul ℝ b]
        exact smul_ne_zero two_ne_zero hb
      have hc : oconj (b + b) ≠ 0 := by
        intro h
        apply hbb
        rw [← oconj_invol (b + b), h, oconj_zero]
      have moved : Ω *ᵥ octPair (oconj (b + b)) 0 = octPair (oconj (b + b)) 0 := by
        have hit : swapFun oone (octPair 0 (b + b)) = octPair (oconj (b + b)) 0 := by
          simp only [swapFun, first_pair, second_pair, one_omul, oconj_zero, zero_omul]
        rw [← hit]
        exact omega_fix_swap hminus _
      exact omega_fix_second hc moved
    · have hplus : Ω *ᵥ octPair (a + a) 0 = octPair (a + a) 0 := by
        have sum : u + stdSys 0 *ᵥ u = octPair (a + a) 0 := by
          rw [hS0, hpair, pair_add, add_neg_cancel]
        rw [← sum, mulVec_add, hfix, fixS0]
      have haa : a + a ≠ 0 := by
        rw [← two_smul ℝ a]
        exact smul_ne_zero two_ne_zero ha
      exact omega_fix_second haa hplus
  exact ext_iff_mulVec.mpr fun x => by rw [one_mulVec]; exact omega_fix_all hsecond x

lemma omega_pm : Ω = 1 ∨ Ω = -1 := by
  by_cases hneg : Ω = -1
  · exact Or.inr hneg
  left
  have witness : ∃ v : Vec 16, Ω *ᵥ v ≠ -v := by
    by_contra hall
    apply hneg
    refine ext_iff_mulVec.mpr fun x => ?_
    rw [neg_mulVec, one_mulVec]
    by_contra hx
    exact hall ⟨x, hx⟩
  obtain ⟨v, hv⟩ := witness
  have hu : v + Ω *ᵥ v ≠ 0 := fun h => hv (add_eq_zero_iff_neg_eq.mp h).symm
  refine omega_eq_one hu ?_
  rw [mulVec_add, mulVec_mulVec, omega_sq, one_mulVec, add_comm]

end Omega

/-- **Lemma 8.1, proof** (lines 46-49): "But `Ω(0) = ±I` on `ℝ^16`" (`H_i(0) = S_i`). -/
theorem lem_8_1_Omega_zero_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) :
    lem81Fam K c 0 = stdSys ∧ (cliffProd stdSys = 1 ∨ cliffProd stdSys = -1) := by
  refine ⟨?_, omega_pm⟩
  funext i
  simp [lem81Fam]

/-- **Lemma 8.1, proof** (lines 46-50): "`Ω(π) = -Ω(0)`" (`H_i(π) = -S_i`: nine sign changes). -/
theorem lem_8_1_Omega_pi_proved (K : Matrix (Fin 16) (Fin 16) ℝ) (c : ℝ) :
    lem81Fam K c Real.pi = (fun i => -stdSys i) ∧ cliffProd (lem81Fam K c Real.pi) = -cliffProd stdSys := by
  have family : lem81Fam K c Real.pi = (fun i => -stdSys i) := by
    funext i
    simp [lem81Fam]
  refine ⟨family, ?_⟩
  have hmap : List.ofFn (fun i => -stdSys i) = (List.ofFn stdSys).map Neg.neg := by
    rw [List.map_ofFn]
    rfl
  rw [family, cliffProd, cliffProd, hmap, prod_map_neg_smul, List.length_ofFn,
    show ((-1 : ℤ) ^ 9) = -1 by norm_num, neg_one_smul]

end Osserman.Proofs.Lem81
