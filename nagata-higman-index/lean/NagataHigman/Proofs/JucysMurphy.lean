/- NagataHigman/Proofs/JucysMurphy.lean — Jucys–Murphy identities in F[S_N] (relation (T2), stars, E and symmetrizer absorption).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Defs.GroupAlgebra

noncomputable section

namespace NagataHigman.Proofs

open NagataHigman Equiv Finset

variable (F : Type*) [Field F]

/-! ## Multiplication rules for basis elements -/

theorem perm_mul_perm {N : ℕ} (σ τ : Perm (Fin N)) : perm F σ * perm F τ = perm F (σ * τ) := by
  simp [perm, MonoidAlgebra.single_mul_single]

theorem perm_one (N : ℕ) : perm F (1 : Perm (Fin N)) = 1 := rfl

theorem perm_swap_mul_self {N : ℕ} (a b : Fin N) : perm F (swap a b) * perm F (swap a b) = 1 := by
  rw [perm_mul_perm, swap_mul_self, perm_one]

/-- `g · (a b) = (g a, g b) · g`. -/
theorem perm_mul_perm_swap {N : ℕ} (g : Perm (Fin N)) (a b : Fin N) :
    perm F g * perm F (swap a b) = perm F (swap (g a) (g b)) * perm F g := by
  rw [perm_mul_perm, perm_mul_perm, swap_apply_apply, inv_mul_cancel_right]

theorem jucysMurphy_def {N : ℕ} (k : Fin N) :
    jucysMurphy F k = ∑ i ∈ univ.filter (fun i : Fin N => i < k), perm F (swap i k) := rfl

theorem card_filter_lt {N : ℕ} (k : Fin N) : (univ.filter (fun i : Fin N => i < k)).card = k := by
  have : univ.filter (fun i : Fin N => i < k) = Iio k := by ext i; simp
  rw [this, Fin.card_Iio]

/-! ## Commuting with `J_i` -/

/-- A permutation fixing `i` and preserving `{a < i}` commutes with `J_i`. -/
theorem perm_mul_jucysMurphy_comm {N : ℕ} (σ : Perm (Fin N)) (i : Fin N) (hfix : σ i = i)
    (hpres : ∀ a, σ a < i ↔ a < i) :
    perm F σ * jucysMurphy F i = jucysMurphy F i * perm F σ := by
  rw [jucysMurphy_def, Finset.mul_sum, Finset.sum_mul]
  have key : ∀ a, perm F σ * perm F (swap a i) = perm F (swap (σ a) i) * perm F σ := by
    intro a; rw [perm_mul_perm_swap, hfix]
  simp_rw [key]
  exact Finset.sum_equiv σ (by simp [hpres]) (by simp)

/-- **D5 (general)**: a permutation fixing every point `≥ k` commutes with `J_k`. -/
theorem perm_mul_jucysMurphy_of_fix_ge {N : ℕ} (σ : Perm (Fin N)) (k : Fin N)
    (hσ : ∀ i, k ≤ i → σ i = i) : perm F σ * jucysMurphy F k = jucysMurphy F k * perm F σ := by
  apply perm_mul_jucysMurphy_comm F σ k (hσ k le_rfl)
  intro a
  constructor
  · intro h
    by_contra hak
    rw [not_lt] at hak
    rw [hσ a hak] at h
    exact absurd h (not_lt.2 hak)
  · intro h
    by_contra hk
    rw [not_lt] at hk
    have h2 := σ.injective (hσ (σ a) hk)
    rw [h2] at hk
    exact absurd h (not_lt.2 hk)

/-- **D5**: for the last point `top`, every `σ ∈ Stab(top)` commutes with `J_top`. -/
theorem perm_mul_jucysMurphy_top {N : ℕ} (σ : Perm (Fin N)) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    (hσ : σ top = top) : perm F σ * jucysMurphy F top = jucysMurphy F top * perm F σ := by
  apply perm_mul_jucysMurphy_of_fix_ge F σ top
  intro i hi
  have : i = top := by
    have := i.isLt
    rw [Fin.le_iff_val_le_val] at hi
    exact Fin.ext (by omega)
  rw [this, hσ]

/-- **D1**: the Jucys–Murphy elements commute. -/
theorem jucysMurphy_comm_of_lt {N : ℕ} (k l : Fin N) (hkl : k < l) :
    jucysMurphy F k * jucysMurphy F l = jucysMurphy F l * jucysMurphy F k := by
  have h : ∀ i ∈ univ.filter (fun i : Fin N => i < k),
      perm F (swap i k) * jucysMurphy F l = jucysMurphy F l * perm F (swap i k) := by
    intro i hi
    rw [mem_filter] at hi
    apply perm_mul_jucysMurphy_of_fix_ge
    intro j hj
    exact swap_apply_of_ne_of_ne (ne_of_gt (lt_of_lt_of_le (hi.2.trans hkl) hj))
      (ne_of_gt (lt_of_lt_of_le hkl hj))
  rw [jucysMurphy_def F k, Finset.sum_mul, Finset.sum_congr rfl h, ← Finset.mul_sum]

theorem jucysMurphy_comm {N : ℕ} (k l : Fin N) :
    jucysMurphy F k * jucysMurphy F l = jucysMurphy F l * jucysMurphy F k := by
  rcases lt_trichotomy k l with h | rfl | h
  · exact jucysMurphy_comm_of_lt F k l h
  · rfl
  · exact (jucysMurphy_comm_of_lt F l k h).symm

/-! ## The relation (T2) -/

/-- **D2 = (T2)**: `s J_{k+1} - J_k s = 1` for `s = (k, k+1)`. -/
theorem R_relation (N : ℕ) (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    perm F (swap k l) * jucysMurphy F l - jucysMurphy F k * perm F (swap k l) = 1 := by
  have hkl' : k ≠ l := fun h => by rw [h] at hkl; omega
  have hsplit : univ.filter (fun i : Fin N => i < l) =
      insert k (univ.filter (fun i : Fin N => i < k)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def, Fin.ext_iff]
    omega
  have hk : k ∉ univ.filter (fun i : Fin N => i < k) := by simp
  have hterm : ∀ i ∈ univ.filter (fun i : Fin N => i < k),
      perm F (swap k l) * perm F (swap i l) = perm F (swap i k) * perm F (swap k l) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and, Fin.lt_def] at hi
    have hik : i ≠ k := fun h => by rw [h] at hi; omega
    have hil : i ≠ l := fun h => by rw [h] at hi; omega
    rw [perm_mul_perm_swap, swap_apply_of_ne_of_ne hik hil, swap_apply_right]
  rw [jucysMurphy_def F l, hsplit, Finset.sum_insert hk, mul_add, perm_swap_mul_self,
    Finset.mul_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← jucysMurphy_def]
  abel

/-! ## D3: `s = (k, k+1)` commutes with `J_i` (`i ≠ k, k+1`), with `J_k + J_{k+1}`, with `J_k J_{k+1}` -/

theorem perm_swap_mul_jucysMurphy_of_ne {N : ℕ} (k l i : Fin N) (hkl : (l : ℕ) = k + 1)
    (hik : i ≠ k) (hil : i ≠ l) :
    perm F (swap k l) * jucysMurphy F i = jucysMurphy F i * perm F (swap k l) := by
  apply perm_mul_jucysMurphy_comm F _ i (swap_apply_of_ne_of_ne hik hil)
  have hik' : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
  have hil' : (i : ℕ) ≠ l := fun h => hil (Fin.ext h)
  intro a
  rcases eq_or_ne a k with rfl | hak
  · rw [swap_apply_left]
    simp only [Fin.lt_def]
    omega
  rcases eq_or_ne a l with rfl | hal
  · rw [swap_apply_right]
    simp only [Fin.lt_def]
    omega
  rw [swap_apply_of_ne_of_ne hak hal]

/-- `s J_k = J_{k+1} s - 1` (conjugate of (T2) by `s`). -/
theorem perm_swap_mul_jucysMurphy_left {N : ℕ} (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    perm F (swap k l) * jucysMurphy F k = jucysMurphy F l * perm F (swap k l) - 1 := by
  have hR := R_relation F N k l hkl
  set s := perm F (swap k l)
  have hss : s * s = 1 := perm_swap_mul_self F k l
  -- multiply (T2) by `s` on both sides: `J_l s - s J_k = 1`
  have h2 : s * (s * jucysMurphy F l - jucysMurphy F k * s) * s = s * 1 * s := by rw [hR]
  rw [mul_sub, sub_mul, ← mul_assoc, hss, one_mul, mul_assoc, mul_assoc, hss, mul_one, mul_one,
    hss] at h2
  rw [← h2]
  abel

theorem perm_swap_mul_jucysMurphy_right {N : ℕ} (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    perm F (swap k l) * jucysMurphy F l = 1 + jucysMurphy F k * perm F (swap k l) := by
  rw [← R_relation F N k l hkl]
  abel

theorem perm_swap_comm_jucysMurphy_add {N : ℕ} (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    perm F (swap k l) * (jucysMurphy F k + jucysMurphy F l) =
      (jucysMurphy F k + jucysMurphy F l) * perm F (swap k l) := by
  rw [mul_add, perm_swap_mul_jucysMurphy_left F k l hkl, perm_swap_mul_jucysMurphy_right F k l hkl,
    add_mul]
  abel

theorem perm_swap_comm_jucysMurphy_mul {N : ℕ} (k l : Fin N) (hkl : (l : ℕ) = k + 1) :
    perm F (swap k l) * (jucysMurphy F k * jucysMurphy F l) =
      (jucysMurphy F k * jucysMurphy F l) * perm F (swap k l) := by
  rw [← mul_assoc, perm_swap_mul_jucysMurphy_left F k l hkl, sub_mul, one_mul, mul_assoc,
    perm_swap_mul_jucysMurphy_right F k l hkl, mul_add, mul_one, ← mul_assoc,
    jucysMurphy_comm F l k, mul_assoc]
  abel

/-! ## D4: star elements -/

/-- **D4**: `g X^{(j)} g⁻¹ = X^{(g j)}`. -/
theorem perm_conj_starElem {N : ℕ} (g : Perm (Fin N)) (j : Fin N) :
    perm F g * starElem F j * perm F g⁻¹ = starElem F (g j) := by
  unfold starElem
  rw [Finset.mul_sum, Finset.sum_mul]
  have key : ∀ i, perm F g * perm F (swap i j) * perm F g⁻¹ = perm F (swap (g i) (g j)) := by
    intro i
    rw [perm_mul_perm_swap, mul_assoc, perm_mul_perm, mul_inv_cancel, perm_one, mul_one]
  simp_rw [key]
  exact Finset.sum_equiv g (by simp) (by simp)

/-- **D4**: the star at the last point is `J_top`. -/
theorem starElem_top {N : ℕ} (top : Fin N) (htop : (top : ℕ) + 1 = N) :
    starElem F top = jucysMurphy F top := by
  unfold starElem jucysMurphy
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, Fin.lt_def, ne_eq, Fin.ext_iff]
  have := i.isLt
  omega

/-! ## D6: absorption by `E` and by the symmetrizer -/

theorem support_mul_left_subset_iff {N : ℕ} (X : Finset (Fin N)) (τ π : Perm (Fin N))
    (hτ : τ.support ⊆ X) : (τ * π).support ⊆ X ↔ π.support ⊆ X := by
  constructor
  · intro h
    have := Perm.support_mul_le τ⁻¹ (τ * π)
    rw [inv_mul_cancel_left, Perm.support_inv] at this
    exact le_trans this (sup_le hτ h)
  · intro h
    exact le_trans (Perm.support_mul_le τ π) (sup_le hτ h)

theorem support_mul_right_subset_iff {N : ℕ} (X : Finset (Fin N)) (τ π : Perm (Fin N))
    (hτ : τ.support ⊆ X) : (π * τ).support ⊆ X ↔ π.support ⊆ X := by
  constructor
  · intro h
    have := Perm.support_mul_le (π * τ) τ⁻¹
    rw [mul_inv_cancel_right, Perm.support_inv] at this
    exact le_trans this (sup_le h hτ)
  · intro h
    exact le_trans (Perm.support_mul_le π τ) (sup_le h hτ)

theorem sign_cast_mul_self {N : ℕ} (τ : Perm (Fin N)) :
    ((Perm.sign τ : ℤ) : F) * ((Perm.sign τ : ℤ) : F) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem perm_mul_altSum {N : ℕ} (X : Finset (Fin N)) (τ : Perm (Fin N)) (hτ : τ.support ⊆ X) :
    perm F τ * altSum F X = ((Perm.sign τ : ℤ) : F) • altSum F X := by
  unfold altSum
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_equiv (Equiv.mulLeft τ) ?_ ?_
  · intro π
    simp [support_mul_left_subset_iff X τ π hτ]
  · intro π _
    rw [mul_smul_comm, perm_mul_perm, smul_smul, coe_mulLeft, Perm.sign_mul, Units.val_mul,
      Int.cast_mul, ← mul_assoc, sign_cast_mul_self, one_mul]

theorem altSum_mul_perm {N : ℕ} (X : Finset (Fin N)) (τ : Perm (Fin N)) (hτ : τ.support ⊆ X) :
    altSum F X * perm F τ = ((Perm.sign τ : ℤ) : F) • altSum F X := by
  unfold altSum
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Finset.sum_equiv (Equiv.mulRight τ) ?_ ?_
  · intro π
    simp [support_mul_right_subset_iff X τ π hτ]
  · intro π _
    rw [smul_mul_assoc, perm_mul_perm, smul_smul, coe_mulRight, Perm.sign_mul, Units.val_mul,
      Int.cast_mul, mul_comm (((Perm.sign π : ℤ) : F)), ← mul_assoc, sign_cast_mul_self, one_mul]

theorem support_swap_subset_altGen {N : ℕ} (n : ℕ) (i k : Fin N) (hik : i < k) (hk : (k : ℕ) ≤ n) :
    (swap i k).support ⊆ univ.filter (fun j : Fin N => (j : ℕ) ≤ n) := by
  rw [Perm.support_swap (ne_of_lt hik)]
  intro j hj
  simp only [mem_insert, mem_singleton] at hj
  rw [Fin.lt_def] at hik
  rcases hj with rfl | rfl <;> simp <;> omega

/-- **D6**: `(i k) E = -E` for `i < k ≤ n`. -/
theorem perm_swap_mul_altGen {N : ℕ} (n : ℕ) (i k : Fin N) (hik : i < k) (hk : (k : ℕ) ≤ n) :
    perm F (swap i k) * altGen F N n = -altGen F N n := by
  rw [altGen, perm_mul_altSum F _ _ (support_swap_subset_altGen n i k hik hk),
    Perm.sign_swap (ne_of_lt hik)]
  simp

/-- **D6**: `E (i k) = -E` for `i < k ≤ n`. -/
theorem altGen_mul_perm_swap {N : ℕ} (n : ℕ) (i k : Fin N) (hik : i < k) (hk : (k : ℕ) ≤ n) :
    altGen F N n * perm F (swap i k) = -altGen F N n := by
  rw [altGen, altSum_mul_perm F _ _ (support_swap_subset_altGen n i k hik hk),
    Perm.sign_swap (ne_of_lt hik)]
  simp

/-- **D6**: `J_k E = -k E` for `k ≤ n`. -/
theorem jucysMurphy_mul_altGen {N : ℕ} (n : ℕ) (k : Fin N) (hk : (k : ℕ) ≤ n) :
    jucysMurphy F k * altGen F N n = -((k : ℕ) : F) • altGen F N n := by
  rw [jucysMurphy_def, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun i hi => perm_swap_mul_altGen F n i k (mem_filter.1 hi).2 hk)]
  rw [Finset.sum_const, card_filter_lt, ← Nat.cast_smul_eq_nsmul F, smul_neg, neg_smul]

/-- The symmetrizer `∑_{π ∈ Sym(X)} π`. -/
def permSum {N : ℕ} (X : Finset (Fin N)) : GrpAlg F N :=
  ∑ π ∈ univ.filter (fun π : Perm (Fin N) => π.support ⊆ X), perm F π

/-- The symmetrizer of the first `n+1` points, `∑_{π ∈ S_{n+1}} π`. -/
def symGen (N n : ℕ) : GrpAlg F N := permSum F (univ.filter (fun i : Fin N => (i : ℕ) ≤ n))

theorem perm_mul_symSum {N : ℕ} (X : Finset (Fin N)) (τ : Perm (Fin N)) (hτ : τ.support ⊆ X) :
    perm F τ * permSum F X = permSum F X := by
  unfold permSum
  rw [Finset.mul_sum]
  refine Finset.sum_equiv (Equiv.mulLeft τ) ?_ ?_
  · intro π
    simp [support_mul_left_subset_iff X τ π hτ]
  · intro π _
    rw [perm_mul_perm, coe_mulLeft]

theorem permSum_mul_perm {N : ℕ} (X : Finset (Fin N)) (τ : Perm (Fin N)) (hτ : τ.support ⊆ X) :
    permSum F X * perm F τ = permSum F X := by
  unfold permSum
  rw [Finset.sum_mul]
  refine Finset.sum_equiv (Equiv.mulRight τ) ?_ ?_
  · intro π
    simp [support_mul_right_subset_iff X τ π hτ]
  · intro π _
    rw [perm_mul_perm, coe_mulRight]

/-- **D6**: `(i k) S = S` for `i < k ≤ n`. -/
theorem perm_swap_mul_symGen {N : ℕ} (n : ℕ) (i k : Fin N) (hik : i < k) (hk : (k : ℕ) ≤ n) :
    perm F (swap i k) * symGen F N n = symGen F N n :=
  perm_mul_symSum F _ _ (support_swap_subset_altGen n i k hik hk)

/-- **D6**: `S (i k) = S` for `i < k ≤ n`. -/
theorem symGen_mul_perm_swap {N : ℕ} (n : ℕ) (i k : Fin N) (hik : i < k) (hk : (k : ℕ) ≤ n) :
    symGen F N n * perm F (swap i k) = symGen F N n :=
  permSum_mul_perm F _ _ (support_swap_subset_altGen n i k hik hk)

/-- **D6**: `J_k S = k S` for `k ≤ n`. -/
theorem jucysMurphy_mul_symGen {N : ℕ} (n : ℕ) (k : Fin N) (hk : (k : ℕ) ≤ n) :
    jucysMurphy F k * symGen F N n = ((k : ℕ) : F) • symGen F N n := by
  rw [jucysMurphy_def, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun i hi => perm_swap_mul_symGen F n i k (mem_filter.1 hi).2 hk)]
  rw [Finset.sum_const, card_filter_lt, ← Nat.cast_smul_eq_nsmul F]

/-! ## D7: `E² = (n+1)! E`, `S² = (n+1)! S` -/

theorem card_perms_supported {N : ℕ} (X : Finset (Fin N)) :
    (univ.filter (fun π : Perm (Fin N) => π.support ⊆ X)).card = X.card.factorial := by
  have h1 : Fintype.card (Perm {a : Fin N // a ∈ X}) = X.card.factorial := by
    rw [Fintype.card_perm, Fintype.card_coe]
  rw [← h1, Fintype.card_congr (Perm.subtypeEquivSubtypePerm (fun a : Fin N => a ∈ X)),
    Fintype.card_subtype]
  congr 1
  ext π
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h a ha
    by_contra hne
    exact ha (h (Perm.mem_support.2 hne))
  · intro h a ha
    by_contra hna
    exact Perm.mem_support.1 ha (h a hna)

theorem card_filter_le {N n : ℕ} (hn : n + 1 ≤ N) :
    (univ.filter (fun i : Fin N => (i : ℕ) ≤ n)).card = n + 1 := by
  have : univ.filter (fun i : Fin N => (i : ℕ) ≤ n) = Iic ⟨n, by omega⟩ := by
    ext i
    simp [Fin.le_iff_val_le_val]
  rw [this, Fin.card_Iic]

theorem altSum_mul_self {N : ℕ} (X : Finset (Fin N)) :
    altSum F X * altSum F X = (X.card.factorial : F) • altSum F X := by
  conv_lhs => arg 1; rw [altSum]
  rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun π hπ => by
    rw [smul_mul_assoc, perm_mul_altSum F X π (mem_filter.1 hπ).2, smul_smul, sign_cast_mul_self,
      one_smul])]
  rw [Finset.sum_const, card_perms_supported, ← Nat.cast_smul_eq_nsmul F]

theorem permSum_mul_self {N : ℕ} (X : Finset (Fin N)) :
    permSum F X * permSum F X = (X.card.factorial : F) • permSum F X := by
  conv_lhs => arg 1; rw [permSum]
  rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun π hπ => perm_mul_symSum F X π (mem_filter.1 hπ).2)]
  rw [Finset.sum_const, card_perms_supported, ← Nat.cast_smul_eq_nsmul F]

/-- **D7**: `E E = (n+1)! E` when `n + 1 ≤ N`. -/
theorem altGen_mul_self {N n : ℕ} (hn : n + 1 ≤ N) :
    altGen F N n * altGen F N n = ((n + 1).factorial : F) • altGen F N n := by
  rw [altGen, altSum_mul_self, card_filter_le hn]

/-- **D7**: `S S = (n+1)! S` when `n + 1 ≤ N`. -/
theorem symGen_mul_self {N n : ℕ} (hn : n + 1 ≤ N) :
    symGen F N n * symGen F N n = ((n + 1).factorial : F) • symGen F N n := by
  rw [symGen, permSum_mul_self, card_filter_le hn]

/-! ## D8: adjacent swaps generate -/

section D8

open Matrix

variable {F} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rho_mulVec_mul {N : ℕ} (ρ : Perm (Fin N) →* Matrix ι ι F) (v : ι → F) (σ τ : Perm (Fin N)) :
    ρ (σ * τ) *ᵥ v = ρ σ *ᵥ (ρ τ *ᵥ v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

/-- Every transposition `(a b)` with `a < b ≤ n` acts by `-1` on `v`. -/
theorem rho_swap_of_lt {N : ℕ} (ρ : Perm (Fin N) →* Matrix ι ι F) (v : ι → F) (n : ℕ)
    (hs : ∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) ≤ n → ρ (swap a b) *ᵥ v = -v)
    (a : Fin N) : ∀ m : ℕ, ∀ b : Fin N, (b : ℕ) = a + 1 + m → (b : ℕ) ≤ n →
      ρ (swap a b) *ᵥ v = -v := by
  intro m
  induction m with
  | zero => intro b hb hbn; exact hs a b hb hbn
  | succ m ih =>
    intro b hb hbn
    set c : Fin N := ⟨(b : ℕ) - 1, by omega⟩ with hc
    have hcv : (c : ℕ) = b - 1 := rfl
    have hac : a ≠ c := fun h => by rw [Fin.ext_iff] at h; omega
    have hab : a ≠ b := fun h => by rw [Fin.ext_iff] at h; omega
    have hcb : c ≠ b := fun h => by rw [Fin.ext_iff] at h; omega
    have hconj : swap a b = swap c b * swap a c * swap c b := by
      have := swap_apply_apply (swap c b) a c
      rwa [swap_apply_of_ne_of_ne hac hab, swap_apply_left, swap_inv] at this
    rw [hconj, rho_mulVec_mul, rho_mulVec_mul, hs c b (by omega) hbn, Matrix.mulVec_neg,
      ih c (by omega) (by omega), neg_neg, hs c b (by omega) hbn]

theorem rho_swap_of_ne {N : ℕ} (ρ : Perm (Fin N) →* Matrix ι ι F) (v : ι → F) (n : ℕ)
    (hs : ∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) ≤ n → ρ (swap a b) *ᵥ v = -v)
    (a b : Fin N) (hab : a ≠ b) (ha : (a : ℕ) ≤ n) (hb : (b : ℕ) ≤ n) :
    ρ (swap a b) *ᵥ v = -v := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [Fin.lt_def] at h
    exact rho_swap_of_lt ρ v n hs a ((b : ℕ) - a - 1) b (by omega) hb
  · rw [Fin.lt_def] at h
    rw [Equiv.swap_comm]
    exact rho_swap_of_lt ρ v n hs b ((a : ℕ) - b - 1) a (by omega) ha

/-- **D8**: if every adjacent swap `(k, k+1)` with `k + 1 ≤ n` acts by `-1` on `v`, then every `π` moving only
points `≤ n` acts on `v` by `sign π`. -/
theorem rho_mulVec_eq_sign {N : ℕ} (ρ : Perm (Fin N) →* Matrix ι ι F) (v : ι → F) (n : ℕ)
    (hs : ∀ a b : Fin N, (b : ℕ) = a + 1 → (b : ℕ) ≤ n → ρ (swap a b) *ᵥ v = -v)
    (π : Perm (Fin N)) (hπ : π.support ⊆ univ.filter (fun i : Fin N => (i : ℕ) ≤ n)) :
    ρ π *ᵥ v = ((Perm.sign π : ℤ) : F) • v := by
  induction h : π.support.card using Nat.strong_induction_on generalizing π with
  | _ m ih =>
    by_cases h1 : π = 1
    · subst h1
      simp
    obtain ⟨x, hx⟩ : ∃ x, π x ≠ x := by
      by_contra hcon
      exact h1 (Equiv.ext fun y => not_not.1 fun hy => hcon ⟨y, hy⟩)
    have hsub : (swap x (π x) * π).support ⊆ π.support := fun z hz =>
      (Perm.mem_support_swap_mul_imp_mem_support_ne hz).1
    have hlt : (swap x (π x) * π).support.card < m := h ▸ Perm.card_support_swap_mul hx
    have ih' := ih _ hlt (swap x (π x) * π) (hsub.trans hπ) rfl
    have hxX := hπ (Perm.mem_support.2 hx)
    have hpxX := hπ (Perm.mem_support.2 (fun e => hx (π.injective e)))
    simp only [mem_filter, mem_univ, true_and] at hxX hpxX
    have hswap := rho_swap_of_ne ρ v n hs x (π x) (Ne.symm hx) hxX hpxX
    conv_lhs => rw [← swap_mul_self_mul x (π x) π]
    rw [rho_mulVec_mul, ih', Matrix.mulVec_smul, hswap, Perm.sign_mul, Perm.sign_swap (Ne.symm hx)]
    simp

end D8

end NagataHigman.Proofs

end
