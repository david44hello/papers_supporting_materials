/-
NagataHigman/Proofs/Steps345.lean — package B2: Proposition 2.1 steps (3), (4), (5) and v1.02 Remark 2.3 (cut in v1.03) by its own route.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.03, lines 307-323, 301-305.
Route of step (4): a permutation all of whose orbits meet X is a full cycle iff its first-return map to X is a cycle
on X (isFullCycle_iff_isCycleOn_firstReturn), and the first-return map of τπ is s∘π (firstReturn_mul).
Route of v1.02 Remark 2.3 (cut in v1.03): rem23_direct uses rem23_proj and the step-(7) duality (prop21_step7_perp and its column twin
perp_blockSum_firstRow_iff); checked with a dependency walk that it never uses signTwist_of_mem_cycleSpan.
-/
import Mathlib
import NagataHigman.Defs.FirstReturn
import NagataHigman.Proofs.Steps21
import NagataHigman.Proofs.JucysMurphy
import NagataHigman.Proofs.Lemma31

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset NagataHigman.FirstReturn

namespace Steps345

variable {N : ℕ}

theorem firstReturn_apply (τ : Perm (Fin N)) (X : Finset (Fin N)) (x : Fin N) :
    firstReturn τ X x = firstReturnFun τ X x := rfl

theorem firstReturn_of_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) :
    firstReturn τ X x = (τ ^ returnTime τ X x) x := by
  rw [firstReturn_apply, firstReturnFun, ite_eq_left hx]

theorem firstReturn_of_not_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∉ X) :
    firstReturn τ X x = x := by
  rw [firstReturn_apply, firstReturnFun, ite_eq_right hx]

theorem firstReturn_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) :
    firstReturn τ X x ∈ X :=
  firstReturnFun_mem hx

/-- Characterization of the return time. -/
theorem returnTime_eq_of {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} {r : ℕ} (hr : 0 < r)
    (hmem : (τ ^ r) x ∈ X) (hmin : ∀ j, 0 < j → j < r → (τ ^ j) x ∉ X) : returnTime τ X x = r := by
  have h : ∃ k, 0 < k ∧ (τ ^ k) x ∈ X := ⟨r, hr, hmem⟩
  obtain ⟨h0, h1⟩ := returnTime_spec h
  refine le_antisymm ?_ ?_
  · by_contra hlt
    exact returnTime_min h hr (by omega) hmem
  · by_contra hlt
    exact hmin _ h0 (by omega) h1

/-- `s` maps `X` onto `X`. -/
theorem bijOn_firstReturn (τ : Perm (Fin N)) (X : Finset (Fin N)) :
    Set.BijOn (firstReturn τ X) (X : Set (Fin N)) (X : Set (Fin N)) := by
  refine ⟨fun x hx => firstReturn_mem (Finset.mem_coe.1 hx), (Equiv.injective _).injOn, fun y hy => ?_⟩
  refine ⟨(firstReturn τ X).symm y, ?_, Equiv.apply_symm_apply _ _⟩
  by_contra hn
  have e := firstReturn_of_not_mem (τ := τ) (Finset.mem_coe.not.1 hn)
  rw [Equiv.apply_symm_apply] at e
  exact hn (e ▸ hy)

theorem sameCycle_self_firstReturn (τ : Perm (Fin N)) (X : Finset (Fin N)) (x : Fin N) :
    τ.SameCycle x (firstReturn τ X x) := by
  by_cases hx : x ∈ X
  · rw [firstReturn_of_mem hx]
    exact ⟨returnTime τ X x, by rw [zpow_natCast]⟩
  · rw [firstReturn_of_not_mem hx]

/-- An `s`-orbit lies in a `τ`-orbit. -/
theorem sameCycle_of_sameCycle_firstReturn {τ : Perm (Fin N)} {X : Finset (Fin N)} {x y : Fin N}
    (h : (firstReturn τ X).SameCycle x y) : τ.SameCycle x y := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ i ih => rw [pow_succ', Perm.mul_apply]; exact ih.trans (sameCycle_self_firstReturn τ X _)

/-- Two points of `X` in one `τ`-orbit lie in one `s`-orbit. -/
theorem sameCycle_firstReturn_of_mem {τ : Perm (Fin N)} {X : Finset (Fin N)} {x y : Fin N} (hx : x ∈ X)
    (hy : y ∈ X) (h : τ.SameCycle x y) : (firstReturn τ X).SameCycle x y := by
  obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
  clear h
  induction j using Nat.strong_induction_on generalizing x with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [pow_zero, Perm.one_apply] at hj
      rw [hj]
    · have hex := exists_return_of_mem (τ := τ) hx
      obtain ⟨hr0, -⟩ := returnTime_spec hex
      have hrj : returnTime τ X x ≤ j := by
        by_contra hlt
        exact returnTime_min hex hj0 (by omega) (hj ▸ hy)
      have key : (τ ^ (j - returnTime τ X x)) (firstReturn τ X x) = y := by
        rw [firstReturn_of_mem hx, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hrj, hj]
      have h1 : (firstReturn τ X).SameCycle x (firstReturn τ X x) := ⟨1, by rw [zpow_one]⟩
      exact h1.trans (ih _ (by omega) (firstReturn_mem hx) key)

/-- For `N ≥ 2`: a full cycle is a permutation with one orbit. -/
theorem isFullCycle_iff_sameCycle (hN : 2 ≤ N) (σ : Perm (Fin N)) :
    IsFullCycle σ ↔ ∀ x y, σ.SameCycle x y := by
  refine ⟨fun h => Arcs.sameCycle_of_isFullCycle h, fun h => ?_⟩
  have hmove : ∀ x, σ x ≠ x := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : Fin N, y ≠ x := by
      by_cases h0 : (x : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun e => h0 (by rw [← e])⟩
    obtain ⟨i, hi⟩ := h x y
    rw [Perm.zpow_apply_eq_self_of_apply_eq_self hx] at hi
    exact hy hi.symm
  refine ⟨⟨⟨0, by omega⟩, hmove _, fun y _ => h _ y⟩, ?_⟩
  ext x
  simp only [Perm.mem_support, Finset.mem_univ, iff_true]
  exact hmove x

theorem two_le_of_isFullCycle {σ : Perm (Fin N)} (h : IsFullCycle σ) : 2 ≤ N := by
  have := h.1.two_le_card_support
  rw [h.2, Finset.card_univ, Fintype.card_fin] at this
  exact this

/-- **The first-return criterion.** If every `σ`-orbit meets `X`, then `σ` is a full cycle iff its first-return map
to `X` is a cycle on `X`. -/
theorem isFullCycle_iff_isCycleOn_firstReturn (hN : 2 ≤ N) (σ : Perm (Fin N)) (X : Finset (Fin N))
    (hmeet : ∀ y, ∃ j : ℕ, (σ ^ j) y ∈ X) :
    IsFullCycle σ ↔ (firstReturn σ X).IsCycleOn (X : Set (Fin N)) := by
  rw [isFullCycle_iff_sameCycle hN]
  constructor
  · intro h
    exact ⟨bijOn_firstReturn σ X, fun x hx y hy =>
      sameCycle_firstReturn_of_mem (Finset.mem_coe.1 hx) (Finset.mem_coe.1 hy) (h x y)⟩
  · intro h y z
    obtain ⟨j, hj⟩ := hmeet y
    obtain ⟨k, hk⟩ := hmeet z
    have h1 : σ.SameCycle y ((σ ^ j) y) := ⟨j, by rw [zpow_natCast]⟩
    have h2 : σ.SameCycle z ((σ ^ k) z) := ⟨k, by rw [zpow_natCast]⟩
    exact h1.trans ((sameCycle_of_sameCycle_firstReturn
      (h.2 (Finset.mem_coe.2 hj) (Finset.mem_coe.2 hk))).trans h2.symm)

/-- For a full cycle `τ` and nonempty `X`, every orbit of `τ` meets `X`. -/
theorem exists_pow_mem {τ : Perm (Fin N)} (hτ : ∀ x y, τ.SameCycle x y) {X : Finset (Fin N)} (hX : X.Nonempty)
    (y : Fin N) : ∃ j : ℕ, (τ ^ j) y ∈ X := by
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j, hj⟩ := (hτ y x0).exists_nat_pow_eq
  exact ⟨j, hj ▸ hx0⟩

theorem apply_mem_of_support_subset {π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) {x : Fin N}
    (hx : x ∈ X) : π x ∈ X := by
  by_cases hs : x ∈ π.support
  · exact hπ (Perm.apply_mem_support.2 hs)
  · rw [Perm.notMem_support.1 hs]; exact hx

theorem apply_eq_of_not_mem {π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) {x : Fin N}
    (hx : x ∉ X) : π x = x :=
  Perm.notMem_support.1 fun h => hx (hπ h)

/-- From `x`, `τπ` follows `τ` from `π(x)` as long as `τ` stays off `X`. -/
theorem mul_pow_apply_eq {τ π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) (x : Fin N) {j : ℕ}
    (hj : 1 ≤ j) (h : ∀ i, 0 < i → i < j → (τ ^ i) (π x) ∉ X) : ((τ * π) ^ j) x = (τ ^ j) (π x) := by
  induction j, hj using Nat.le_induction with
  | base => rw [pow_one, pow_one, Perm.mul_apply]
  | succ j hj ih =>
    rw [pow_succ', Perm.mul_apply, ih (fun i hi hij => h i hi (by omega)), Perm.mul_apply,
      apply_eq_of_not_mem hπ (h j (by omega) (by omega)), ← Perm.mul_apply, ← pow_succ']

/-- Off `X`-free stretches, `τπ = τ`: the first `j` steps from `y` agree when `τ^i(y) ∉ X` for `i < j`. -/
theorem mul_pow_apply_eq' {τ π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) (y : Fin N) (j : ℕ)
    (h : ∀ i, i < j → (τ ^ i) y ∉ X) : ((τ * π) ^ j) y = (τ ^ j) y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Perm.mul_apply, ih (fun i hi => h i (by omega)), Perm.mul_apply,
      apply_eq_of_not_mem hπ (h j (by omega)), ← Perm.mul_apply, ← pow_succ']

/-- The return time of `τπ` at `x ∈ X` is the return time of `τ` at `π(x)`. -/
theorem returnTime_mul {τ π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) {x : Fin N} (hx : x ∈ X) :
    returnTime (τ * π) X x = returnTime τ X (π x) := by
  have hy := apply_mem_of_support_subset hπ hx
  have hex := exists_return_of_mem (τ := τ) hy
  obtain ⟨hr0, hrX⟩ := returnTime_spec hex
  have hmin : ∀ i, 0 < i → i < returnTime τ X (π x) → (τ ^ i) (π x) ∉ X := fun i hi hir =>
    returnTime_min hex hi hir
  refine returnTime_eq_of hr0 ?_ ?_
  · rw [mul_pow_apply_eq hπ x hr0 hmin]; exact hrX
  · intro j hj hjr
    rw [mul_pow_apply_eq hπ x hj (fun i hi hij => hmin i hi (by omega))]
    exact hmin j hj hjr

/-- **"From `x`, `τπ` runs through `Arc(π(x))` and lands on `s(π(x))`"** (paper v1.02 lines 260-261). -/
theorem firstReturn_mul {τ π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) :
    firstReturn (τ * π) X = firstReturn τ X * π := by
  ext x
  by_cases hx : x ∈ X
  · have hy := apply_mem_of_support_subset hπ hx
    have hex := exists_return_of_mem (τ := τ) hy
    obtain ⟨hr0, -⟩ := returnTime_spec hex
    rw [Perm.mul_apply, firstReturn_of_mem hx, firstReturn_of_mem hy, returnTime_mul hπ hx,
      mul_pow_apply_eq hπ x hr0 (fun i hi hir => returnTime_min hex hi hir)]
  · rw [Perm.mul_apply, firstReturn_of_not_mem hx, apply_eq_of_not_mem hπ hx, firstReturn_of_not_mem hx]

theorem arc_mul {τ π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X) {x : Fin N} (hx : x ∈ X) :
    arc (τ * π) X x = arc τ X (π x) := by
  have hy := apply_mem_of_support_subset hπ hx
  have hex := exists_return_of_mem (τ := τ) hy
  unfold arc
  rw [returnTime_mul hπ hx]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  exact mul_pow_apply_eq hπ x (by omega) (fun j hj hji => returnTime_min hex hj (by omega))

/-- Every orbit of `τπ` meets `X` (when every orbit of `τ` does). -/
theorem exists_mul_pow_mem {τ π : Perm (Fin N)} {X : Finset (Fin N)} (hπ : π.support ⊆ X)
    (hmeet : ∀ y, ∃ j : ℕ, (τ ^ j) y ∈ X) (y : Fin N) : ∃ j : ℕ, ((τ * π) ^ j) y ∈ X := by
  classical
  have h := hmeet y
  refine ⟨Nat.find h, ?_⟩
  rw [mul_pow_apply_eq' hπ y _ (fun i hi => Nat.find_min h hi)]
  exact Nat.find_spec h

/-! ### Arcs -/

theorem mem_arc {τ : Perm (Fin N)} {X : Finset (Fin N)} {x y : Fin N} :
    y ∈ arc τ X x ↔ ∃ i, i < returnTime τ X x ∧ (τ ^ (i + 1)) x = y := by
  simp only [arc, List.mem_map, List.mem_range]

theorem arc_ne_nil {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) : arc τ X x ≠ [] := by
  obtain ⟨hr0, -⟩ := returnTime_spec (exists_return_of_mem (τ := τ) hx)
  unfold arc
  simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  omega

theorem arc_getLast? {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) :
    (arc τ X x).getLast? = some (firstReturn τ X x) := by
  obtain ⟨hr0, -⟩ := returnTime_spec (exists_return_of_mem (τ := τ) hx)
  obtain ⟨r, hr⟩ : ∃ r, returnTime τ X x = r + 1 := ⟨returnTime τ X x - 1, by omega⟩
  rw [firstReturn_of_mem hx, arc, hr, List.range_succ, List.map_append, List.map_singleton,
    List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
  rfl

theorem arc_nodup {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X) : (arc τ X x).Nodup := by
  have hex := exists_return_of_mem (τ := τ) hx
  refine List.Nodup.map_on (fun i hi j hj hij => ?_) List.nodup_range
  rw [List.mem_range] at hi hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have e := eq_pow_sub_of_pow_eq (by omega : i + 1 ≤ j + 1) hij
    exact returnTime_min hex (j := j + 1 - (i + 1)) (by omega) (by omega) (e ▸ hx)
  · have e := eq_pow_sub_of_pow_eq (by omega : j + 1 ≤ i + 1) hij.symm
    exact returnTime_min hex (j := i + 1 - (j + 1)) (by omega) (by omega) (e ▸ hx)

/-- The arcs of the points of `X` partition `Fin N` (paper line 313), for a full cycle `τ` and nonempty `X`. -/
theorem existsUnique_mem_arc {τ : Perm (Fin N)} (hτ : ∀ x y, τ.SameCycle x y) {X : Finset (Fin N)}
    (hX : X.Nonempty) (y : Fin N) : ∃! x, x ∈ X ∧ y ∈ arc τ X x := by
  classical
  -- existence: walk back from `y` to the last point of `X` before it
  have hinv : ∀ a b, (τ⁻¹).SameCycle a b := fun a b => Perm.sameCycle_inv.2 (hτ a b)
  have hJ : ∃ j, 0 < j ∧ ((τ⁻¹) ^ j) y ∈ X := by
    obtain ⟨j, hj⟩ := exists_pow_mem hinv hX (τ⁻¹ y)
    exact ⟨j + 1, by omega, by rw [pow_succ, Perm.mul_apply]; exact hj⟩
  set J := Nat.find hJ with hJdef
  obtain ⟨hJ0, hJX⟩ := Nat.find_spec hJ
  set x := ((τ⁻¹) ^ J) y with hxdef
  have hpow : ∀ i, i ≤ J → (τ ^ i) x = ((τ⁻¹) ^ (J - i)) y := by
    intro i hi
    obtain ⟨d, hd⟩ : ∃ d, J = i + d := ⟨J - i, by omega⟩
    rw [hxdef, hd, Nat.add_sub_cancel_left, pow_add, ← Perm.mul_apply, ← mul_assoc, inv_pow, mul_inv_cancel,
      one_mul]
  have hex := exists_return_of_mem (τ := τ) hJX
  have hJr : J ≤ returnTime τ X x := by
    by_contra hlt
    obtain ⟨hr0, hrX⟩ := returnTime_spec hex
    rw [hpow _ (by omega)] at hrX
    exact Nat.find_min hJ (by omega : J - returnTime τ X x < J) ⟨by omega, hrX⟩
  refine ⟨x, ⟨hJX, mem_arc.2 ⟨J - 1, by omega, ?_⟩⟩, ?_⟩
  · rw [Nat.sub_add_cancel hJ0, hpow J le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]
  -- uniqueness
  rintro x' ⟨hx', hy'⟩
  obtain ⟨a, ha, hax⟩ := mem_arc.1 hy'
  obtain ⟨b, hb, hbx⟩ := mem_arc.1 (show y ∈ arc τ X x from mem_arc.2 ⟨J - 1, by omega, by
    rw [Nat.sub_add_cancel hJ0, hpow J le_rfl, Nat.sub_self, pow_zero, Perm.one_apply]⟩)
  have heq : (τ ^ (a + 1)) x' = (τ ^ (b + 1)) x := hax.trans hbx.symm
  have hex' := exists_return_of_mem (τ := τ) hx'
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd ((eq_pow_sub_of_pow_eq (by omega) heq) ▸ hx')
      (returnTime_min hex (j := b + 1 - (a + 1)) (by omega) (by omega))
  · rw [hab] at heq
    exact (τ ^ (b + 1)).injective heq
  · exact absurd ((eq_pow_sub_of_pow_eq (by omega) heq.symm) ▸ hJX)
      (returnTime_min hex' (j := a + 1 - (b + 1)) (by omega) (by omega))

/-! ### Sign of a cycle on `X` -/

/-- A permutation that is a cycle on `X` and fixes every point outside `X` has the sign of an `|X|`-cycle. -/
theorem sign_of_isCycleOn {ρ : Perm (Fin N)} {X : Finset (Fin N)} (hρ : ρ.IsCycleOn (X : Set (Fin N)))
    (hfix : ∀ x, x ∉ X → ρ x = x) :
    Perm.sign ρ = if X.card ≤ 1 then 1 else -(-1) ^ X.card := by
  have hsupp_sub : ρ.support ⊆ X := fun x hx => by
    by_contra hn; exact Perm.mem_support.1 hx (hfix x hn)
  by_cases hc : X.card ≤ 1
  · rw [ite_eq_left hc]
    have h1 : ρ.support.card ≤ 1 := (Finset.card_le_card hsupp_sub).trans hc
    have h0 : ρ.support.card = 0 := by
      have := Perm.card_support_ne_one ρ
      omega
    rw [Finset.card_eq_zero, Perm.support_eq_empty_iff] at h0
    rw [h0, Perm.sign_one]
  · rw [ite_eq_right hc]
    have hnt : (X : Set (Fin N)).Nontrivial := by
      exact Finset.one_lt_card_iff_nontrivial.1 (by omega)
    have hsupp : ρ.support = X := by
      refine le_antisymm hsupp_sub fun x hx => Perm.mem_support.2 (hρ.apply_ne hnt (Finset.mem_coe.2 hx))
    have hcyc : ρ.IsCycle := by
      rw [Perm.isCycle_iff_exists_isCycleOn]
      refine ⟨X, hnt, hρ, fun x hx => ?_⟩
      by_contra hn
      exact hx (hfix x hn)
    rw [hcyc.sign, hsupp]

end Steps345

open Steps345

variable {N : ℕ}

/-- **Proposition 2.1, step (4)** (lines 311-313): for an `N`-cycle `τ` and nonempty `X`, the first-return map `s`
is a cycle on `X` (an `|X|`-cycle; `|X| = n + 1` in the paper) and fixes the points outside `X`. -/
theorem prop21_step4_s {τ : Perm (Fin N)} (hτ : IsFullCycle τ) {X : Finset (Fin N)} (hX : X.Nonempty) :
    (firstReturn τ X).IsCycleOn (X : Set (Fin N)) ∧ ∀ x, x ∉ X → firstReturn τ X x = x :=
  ⟨(isFullCycle_iff_isCycleOn_firstReturn (two_le_of_isFullCycle hτ) τ X
      (exists_pow_mem (Arcs.sameCycle_of_isFullCycle hτ) hX)).1 hτ,
    fun _ hx => firstReturn_of_not_mem hx⟩

/-- **Proposition 2.1, step (4)** (lines 313-314): the arcs `Arc(x)`, `x ∈ X`, are nonempty, have no repeated point,
end at `s(x)`, and partition `[N]` (every point lies in exactly one arc). -/
theorem prop21_step4_arcs {τ : Perm (Fin N)} (hτ : IsFullCycle τ) {X : Finset (Fin N)} (hX : X.Nonempty) :
    (∀ x ∈ X, arc τ X x ≠ [] ∧ (arc τ X x).Nodup ∧ (arc τ X x).getLast? = some (firstReturn τ X x)) ∧
      ∀ y, ∃! x, x ∈ X ∧ y ∈ arc τ X x :=
  ⟨fun _ hx => ⟨arc_ne_nil hx, arc_nodup hx, arc_getLast? hx⟩,
    existsUnique_mem_arc (Arcs.sameCycle_of_isFullCycle hτ) hX⟩

/-- **Proposition 2.1, step (4)** (v1.02 lines 260-261): for `π ∈ Sym(X)`, from `x ∈ X` the permutation `τπ` runs through
`Arc(π(x))` and lands on `s(π(x))`; so the first-return map of `τπ` to `X` is `s ∘ π`. (Any `τ`.) -/
theorem prop21_step4_return (τ π : Perm (Fin N)) (X : Finset (Fin N)) (hπ : π.support ⊆ X) :
    (∀ x ∈ X, arc (τ * π) X x = arc τ X (π x)) ∧ firstReturn (τ * π) X = firstReturn τ X * π :=
  ⟨fun _ hx => arc_mul hπ hx, firstReturn_mul hπ⟩

/-- **Proposition 2.1, step (4)** (v1.02 lines 261-262): for an `N`-cycle `τ`, nonempty `X` and `π ∈ Sym(X)`: `τπ` is an
`N`-cycle iff `s ∘ π` is a cycle on `X` (an `(n+1)`-cycle). -/
theorem prop21_step4_iff {τ : Perm (Fin N)} (hτ : IsFullCycle τ) {X : Finset (Fin N)} (hX : X.Nonempty)
    {π : Perm (Fin N)} (hπ : π.support ⊆ X) :
    IsFullCycle (τ * π) ↔ (firstReturn τ X * π).IsCycleOn (X : Set (Fin N)) := by
  rw [← firstReturn_mul hπ]
  exact isFullCycle_iff_isCycleOn_firstReturn (two_le_of_isFullCycle hτ) _ X
    (exists_mul_pow_mem hπ (exists_pow_mem (Arcs.sameCycle_of_isFullCycle hτ) hX))

/-- **Proposition 2.1, step (5)** (v1.02 lines 264-265), by the paper's route: for an `N`-cycle `τ`, nonempty `X`, and
`π ∈ Π` (`π ∈ Sym(X)` with `s ∘ π` a cycle on `X`), `sgn(π) = sgn(s) sgn(s ∘ π) = +1`. -/
theorem prop21_step5_sign {τ : Perm (Fin N)} (hτ : IsFullCycle τ) {X : Finset (Fin N)} (hX : X.Nonempty)
    {π : Perm (Fin N)} (hπ : π.support ⊆ X) (hPi : (firstReturn τ X * π).IsCycleOn (X : Set (Fin N))) :
    Perm.sign π = 1 := by
  obtain ⟨hs, hsfix⟩ := prop21_step4_s hτ hX
  have h1 := sign_of_isCycleOn hs hsfix
  have h2 := sign_of_isCycleOn hPi (fun x hx => by
    rw [Perm.mul_apply, apply_eq_of_not_mem hπ hx, hsfix x hx])
  rw [Perm.sign_mul, ← h1] at h2
  have hu : Perm.sign (firstReturn τ X) * Perm.sign π = Perm.sign (firstReturn τ X) * 1 := by rw [mul_one, h2]
  exact mul_left_cancel hu

/-- **Step (5) applied** (lines 320-323, 302): for `N`-cycles `τ`, `σ` with `τ⁻¹σ ∈ Sym(X)`, `sgn(τ⁻¹σ) = +1`, by the
paper's route: `π := τ⁻¹σ` has `τπ = σ` an `N`-cycle, so `s ∘ π` is a cycle on `X` (step (4)) and
`sgn π = sgn(s) sgn(s ∘ π) = 1` (step (5)); for `X = ∅`, `π = 1`. (Not via "an `N`-cycle has sign `(-1)^(N-1)`".) -/
theorem sign_inv_mul_eq_one_of_step5 {τ σ : Perm (Fin N)} (hτ : IsFullCycle τ) (hσ : IsFullCycle σ)
    {X : Finset (Fin N)} (hs : (τ⁻¹ * σ).support ⊆ X) : Perm.sign (τ⁻¹ * σ) = 1 := by
  rcases X.eq_empty_or_nonempty with rfl | hX
  · rw [Perm.support_eq_empty_iff.1 (Finset.subset_empty.1 hs), Perm.sign_one]
  · have hfull : IsFullCycle (τ * (τ⁻¹ * σ)) := by rwa [mul_inv_cancel_left]
    exact prop21_step5_sign hτ hX hs ((prop21_step4_iff hτ hX hs).1 hfull)

/-! ### Part 2: the group-algebra side of steps (3), (5) and v1.02 Remark 2.3 (cut in v1.03) -/

namespace Steps345

variable {F : Type*} [Field F]

theorem symGroupSum_eq_permSum (X : Finset (Fin N)) : symGroupSum F X = permSum F X := rfl

/-- `ε` as a linear map. -/
def signTwistLin : GrpAlg F N →ₗ[F] GrpAlg F N where
  toFun := signTwist F
  map_add' a b := signTwist_add a b
  map_smul' r a := signTwist_smul r a

theorem signTwistLin_apply (a : GrpAlg F N) : signTwistLin a = signTwist F a := rfl

/-- `ε(S_X) = E_X`. -/
theorem signTwist_symGroupSum (X : Finset (Fin N)) : signTwist F (symGroupSum F X) = altSum F X := by
  rw [← signTwistLin_apply, symGroupSum, map_sum, altSum]
  exact Finset.sum_congr rfl fun π _ => signTwist_perm π

/-- `ε(E_X) = S_X`. -/
theorem signTwist_altSum (X : Finset (Fin N)) : signTwist F (altSum F X) = symGroupSum F X := by
  rw [← signTwist_symGroupSum, signTwist_involutive]

/-- `ε(τ E_X) = sgn(τ) · τ S_X`. -/
theorem signTwist_perm_mul_altSum (τ : Perm (Fin N)) (X : Finset (Fin N)) :
    signTwist F (perm F τ * altSum F X) = ((Perm.sign τ : ℤ) : F) • (perm F τ * symGroupSum F X) := by
  rw [signTwist_mul, signTwist_perm, signTwist_altSum, smul_mul_assoc]

theorem coeff_perm_mul_symGroupSum (τ σ : Perm (Fin N)) (X : Finset (Fin N)) :
    (perm F τ * symGroupSum F X).coeff σ = if (τ⁻¹ * σ).support ⊆ X then 1 else 0 := by
  classical
  simp only [symGroupSum, perm, Finset.mul_sum, MonoidAlgebra.single_mul_single, mul_one,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp_rw [← eq_inv_mul_iff_mul_eq]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_filter]

open Classical in
theorem cycleProj_apply (a : GrpAlg F N) :
    cycleProj F N a = ∑ σ ∈ univ.filter (fun σ : Perm (Fin N) => IsFullCycle σ), a.coeff σ • perm F σ := rfl

open Classical in
theorem coeff_cycleProj (a : GrpAlg F N) (σ : Perm (Fin N)) :
    (cycleProj F N a).coeff σ = if IsFullCycle σ then a.coeff σ else 0 := by
  rw [cycleProj_apply]
  simp only [perm, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_filter]

/-- For `c ∈ C_N`: `⟨c, P a⟩ = ⟨c, a⟩` (paper v1.02 line 285). -/
theorem coeffPairing_cycleProj {c : GrpAlg F N} (hc : c ∈ cycleSpan F N) (a : GrpAlg F N) :
    coeffPairing F c (cycleProj F N a) = coeffPairing F c a := by
  classical
  unfold coeffPairing
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_cycleProj]
  by_cases hσ : IsFullCycle σ
  · rw [ite_eq_left hσ]
  · rw [ite_eq_right hσ, coeff_eq_zero_of_mem_cycleSpan hc hσ, zero_mul, zero_mul]

/-- `τ E_X = sgn(π₀) · (τπ₀) E_X` for every `π₀ ∈ Sym(X)`. -/
theorem perm_mul_altSum_eq_smul (τ π₀ : Perm (Fin N)) (X : Finset (Fin N)) (hπ₀ : π₀.support ⊆ X) :
    perm F τ * altSum F X = ((Perm.sign π₀ : ℤ) : F) • (perm F (τ * π₀) * altSum F X) := by
  rw [← perm_mul_perm F, mul_assoc, perm_mul_altSum F X π₀ hπ₀, mul_smul_comm, smul_smul,
    sign_mul_sign (F := F) π₀, one_smul]

/-- `τ S_X = (τπ₀) S_X` for every `π₀ ∈ Sym(X)`. -/
theorem perm_mul_symGroupSum_eq (τ π₀ : Perm (Fin N)) (X : Finset (Fin N)) (hπ₀ : π₀.support ⊆ X) :
    perm F τ * symGroupSum F X = perm F (τ * π₀) * symGroupSum F X := by
  rw [← perm_mul_perm F, mul_assoc, symGroupSum_eq_permSum, perm_mul_symSum F X π₀ hπ₀]

/-- If no `τπ` (`π ∈ Sym(X)`) is an `N`-cycle, then `P(τ S_X) = 0`. -/
theorem cycleProj_perm_mul_symGroupSum_eq_zero (τ : Perm (Fin N)) (X : Finset (Fin N))
    (h : ∀ π : Perm (Fin N), π.support ⊆ X → ¬ IsFullCycle (τ * π)) :
    cycleProj F N (perm F τ * symGroupSum F X) = 0 := by
  classical
  rw [cycleProj_apply]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  have hns : ¬ (τ⁻¹ * σ).support ⊆ X := fun hs =>
    h _ hs (by rw [mul_inv_cancel_left]; exact (Finset.mem_filter.1 hσ).2)
  rw [coeff_perm_mul_symGroupSum, ite_eq_right hns, zero_smul]

end Steps345

variable {F : Type*} [Field F]

/-- **Proposition 2.1, step (3)** (line 307): if no `τπ` (`π ∈ Sym(X)`) is an `N`-cycle, then `P(τ E_X) = 0`. -/
theorem prop21_step3_zero (τ : Perm (Fin N)) (X : Finset (Fin N))
    (h : ∀ π : Perm (Fin N), π.support ⊆ X → ¬ IsFullCycle (τ * π)) :
    cycleProj F N (perm F τ * altSum F X) = 0 := by
  classical
  rw [Steps345.cycleProj_apply]
  refine Finset.sum_eq_zero fun σ hσ => ?_
  have hns : ¬ (τ⁻¹ * σ).support ⊆ X := fun hs =>
    h _ hs (by rw [mul_inv_cancel_left]; exact (Finset.mem_filter.1 hσ).2)
  rw [Arcs.coeff_perm_mul_altSum (F := F), ite_eq_right hns, zero_smul]

/-- **Proposition 2.1, step (3)** (lines 307-309): otherwise `τ E_X = sgn(π₀) τ₀ E_X` with `τ₀ = τπ₀` an
`N`-cycle (`π₀ ∈ Sym(X)`). -/
theorem prop21_step3_reduce (τ : Perm (Fin N)) (X : Finset (Fin N))
    (h : ∃ π : Perm (Fin N), π.support ⊆ X ∧ IsFullCycle (τ * π)) :
    ∃ π₀ : Perm (Fin N), π₀.support ⊆ X ∧ IsFullCycle (τ * π₀) ∧
      perm F τ * altSum F X = ((Perm.sign π₀ : ℤ) : F) • (perm F (τ * π₀) * altSum F X) := by
  obtain ⟨π₀, h1, h2⟩ := h
  exact ⟨π₀, h1, h2, Steps345.perm_mul_altSum_eq_smul τ π₀ X h1⟩

open Classical in
/-- **Proposition 2.1, step (5)** (lines 320-323): for an `N`-cycle `τ`, the sign is constant:
`P(τ E_X) = ∑_{π ∈ Π} τπ`, with no sign. -/
theorem prop21_step5_sum {τ : Perm (Fin N)} (hτ : IsFullCycle τ) (X : Finset (Fin N)) :
    cycleProj F N (perm F τ * altSum F X) =
      ∑ π ∈ univ.filter (fun π : Perm (Fin N) => π.support ⊆ X ∧ IsFullCycle (τ * π)), perm F (τ * π) := by
  rw [Steps345.cycleProj_apply]
  have hterm : ∀ σ ∈ univ.filter (fun σ : Perm (Fin N) => IsFullCycle σ),
      (perm F τ * altSum F X).coeff σ • perm F σ = if (τ⁻¹ * σ).support ⊆ X then perm F σ else 0 := by
    intro σ hσ
    rw [Arcs.coeff_perm_mul_altSum (F := F)]
    by_cases hs : (τ⁻¹ * σ).support ⊆ X
    · rw [ite_eq_left hs, ite_eq_left hs, sign_inv_mul_eq_one_of_step5 hτ (Finset.mem_filter.1 hσ).2 hs]
      simp
    · rw [ite_eq_right hs, ite_eq_right hs, zero_smul]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun π => τ * π) (fun σ => τ⁻¹ * σ) ?_ ?_ ?_ ?_ ?_ <;>
    simp_all [Finset.mem_filter]

/-- **v1.02 Remark 2.3 (cut in v1.03)** (v1.02 line 302): for an `N`-cycle `τ`, `P(τ E_X) = P(τ S_X)`. -/
theorem rem23_sign {τ : Perm (Fin N)} (hτ : IsFullCycle τ) (X : Finset (Fin N)) :
    cycleProj F N (perm F τ * altSum F X) = cycleProj F N (perm F τ * symGroupSum F X) := by
  classical
  rw [Steps345.cycleProj_apply, Steps345.cycleProj_apply]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Arcs.coeff_perm_mul_altSum (F := F), Steps345.coeff_perm_mul_symGroupSum]
  by_cases hs : (τ⁻¹ * σ).support ⊆ X
  · rw [ite_eq_left hs, ite_eq_left hs, sign_inv_mul_eq_one_of_step5 hτ (Finset.mem_filter.1 hσ).2 hs]
    simp
  · rw [ite_eq_right hs, ite_eq_right hs]

/-- **v1.02 Remark 2.3 (cut in v1.03)** (v1.02 line 303): in general `P(τ E_X) = ± P(τ S_X)` (by step (3)). -/
theorem rem23_sign_general (τ : Perm (Fin N)) (X : Finset (Fin N)) :
    cycleProj F N (perm F τ * altSum F X) = cycleProj F N (perm F τ * symGroupSum F X) ∨
      cycleProj F N (perm F τ * altSum F X) = -cycleProj F N (perm F τ * symGroupSum F X) := by
  by_cases hex : ∃ π : Perm (Fin N), π.support ⊆ X ∧ IsFullCycle (τ * π)
  · obtain ⟨π₀, h1, h2⟩ := hex
    rw [Steps345.perm_mul_altSum_eq_smul τ π₀ X h1, map_smul, rem23_sign h2 X,
      Steps345.perm_mul_symGroupSum_eq τ π₀ X h1]
    rcases Int.units_eq_one_or (Perm.sign π₀) with hs | hs <;> rw [hs] <;> simp
  · push Not at hex
    left
    rw [prop21_step3_zero τ X hex, Steps345.cycleProj_perm_mul_symGroupSum_eq_zero τ X hex]

/-- **v1.02 Remark 2.3 (cut in v1.03)** (v1.02 line 304): `ε(I) = ⊕_{λ_1 ≥ n+1} I_λ`, i.e. `a ∈ ⊕_{λ_1 ≥ n+1} I_λ ↔ ε(a) ∈ I`
(for any Young system `Y`). -/
theorem rem23_epsI [CharZero F] (Y : YoungSystem F N) (n : ℕ) (h : n + 1 ≤ N) (a : GrpAlg F N) :
    a ∈ Y.blockSum {lam | n + 1 ≤ lam.firstRow} ↔ signTwist F a ∈ altIdeal F N n := by
  rw [YoungSystem.altIdeal_eq_blockSum Y n h, YoungSystem.mem_blockSum_iff Y, YoungSystem.mem_blockSum_iff Y]
  simp only [Set.mem_ofPred_eq, not_le, YoungSystem.rhoAlg_signTwist_eq_zero_iff Y]
  constructor
  · intro ha mu hmu
    have e : n < Shape.numRows mu ↔ n < Shape.firstRow mu.conjugate := by
      have := lt_numRows_conjugate_iff mu.conjugate n
      rwa [Nat.Partition.conjugate_conjugate] at this
    refine ha _ ?_
    by_contra hc
    exact absurd (e.2 (by omega)) (by omega)
  · intro hb mu hmu
    have e := lt_numRows_conjugate_iff mu n
    have := hb mu.conjugate (by by_contra hc; exact absurd (e.1 (by omega)) (by omega))
    rwa [Nat.Partition.conjugate_conjugate] at this

/-- `ε(I)` as a submodule: `⊕_{λ_1 ≥ n+1} I_λ = ε(I)`. -/
theorem blockSum_firstRow_eq_map [CharZero F] (Y : YoungSystem F N) (n : ℕ) (h : n + 1 ≤ N) :
    Y.blockSum {lam | n + 1 ≤ lam.firstRow} = (altIdeal F N n).map (Steps345.signTwistLin (F := F)) := by
  ext a
  rw [rem23_epsI Y n h, Submodule.mem_map]
  constructor
  · intro ha
    exact ⟨signTwist F a, ha, signTwist_involutive a⟩
  · rintro ⟨b, hb, rfl⟩
    rwa [Steps345.signTwistLin_apply, signTwist_involutive]

/-- The column twin of `I^⊥ = A` (step (7) duality applied to `ε(I)`): `ε(I)^⊥ = A' = ⊕_{λ_1 ≤ n} I_λ`. Proved
like `I^⊥ = A` (orthogonality of blocks, and the generator `S = ε(E)` of `ε(I)`), NOT via "ε = ±1 on `C_N`". -/
theorem perp_blockSum_firstRow_iff [CharZero F] (Y : YoungSystem F N) (n : ℕ) (h : n + 1 ≤ N) (f : GrpAlg F N) :
    (∀ a ∈ Y.blockSum {lam | n + 1 ≤ lam.firstRow}, coeffPairing F f a = 0) ↔ f ∈ Y.colSum n := by
  have hS : signTwist F (altGen F N n) = symGen F N n := by
    rw [altGen, Steps345.signTwist_altSum, Steps345.symGroupSum_eq_permSum, symGen]
  constructor
  · intro hf
    unfold NagataHigman.YoungSystem.colSum
    rw [YoungSystem.mem_blockSum_iff Y]
    intro mu hmu
    simp only [Set.mem_ofPred_eq, not_le] at hmu
    refine YoungSystem.rhoAlg_eq_zero_of_pairing Y (symGen F N n) f (fun g k => hf _ ?_) mu ?_
    · rw [rem23_epsI Y n h, signTwist_mul, signTwist_mul, ← hS, signTwist_involutive]
      exact Submodule.subset_span ⟨signTwist F g, signTwist F k, rfl⟩
    · rw [← hS, Ne, YoungSystem.rhoAlg_signTwist_eq_zero_iff Y]
      exact YoungSystem.rhoAlg_altGen_ne_zero_of_rows Y _ n ((lt_numRows_conjugate_iff mu n).2 hmu)
  · intro hf a ha
    exact PropExact.coeffPairing_eq_zero_of_blockSum Y (S := {lam | lam.firstRow ≤ n})
      (S' := {lam | n + 1 ≤ lam.firstRow}) (fun mu h1 h2 => by simp only [Set.mem_ofPred_eq] at h1 h2; omega) hf ha

/-- **v1.02 Remark 2.3 (cut in v1.03)** (v1.02 line 303): `P(I) = P(ε(I))`, `ε(I) = ⊕_{λ_1 ≥ n+1} I_λ` (any Young system `Y`). -/
theorem rem23_proj [CharZero F] (Y : YoungSystem F N) (n : ℕ) (h : n + 1 ≤ N) :
    (altIdeal F N n).map (cycleProj F N) =
      (Y.blockSum {lam | n + 1 ≤ lam.firstRow}).map (cycleProj F N) := by
  rw [blockSum_firstRow_eq_map Y n h, ← Submodule.map_comp, altIdeal_eq_span F h,
    Submodule.map_span, Submodule.map_span]
  set A := {x | ∃ (τ : Perm (Fin N)) (X : Finset (Fin N)), X.card = n + 1 ∧ x = perm F τ * altSum F X}
  -- `P(ε(τ E_X)) = sgn(τ) P(τ S_X)` and `P(τ S_X) = ± P(τ E_X)`
  have hPε : ∀ (τ : Perm (Fin N)) (X : Finset (Fin N)),
      (cycleProj F N ∘ₗ Steps345.signTwistLin) (perm F τ * altSum F X) =
        ((Perm.sign τ : ℤ) : F) • cycleProj F N (perm F τ * symGroupSum F X) := by
    intro τ X
    rw [LinearMap.comp_apply, Steps345.signTwistLin_apply, Steps345.signTwist_perm_mul_altSum, map_smul]
  have hss : ∀ τ : Perm (Fin N), ((Perm.sign τ : ℤ) : F) * ((Perm.sign τ : ℤ) : F) = 1 := fun τ =>
    sign_mul_sign τ
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, ⟨τ, X, hX, rfl⟩, rfl⟩
    have hmem : (cycleProj F N ∘ₗ Steps345.signTwistLin) (perm F τ * altSum F X) ∈
        Submodule.span F ((cycleProj F N ∘ₗ Steps345.signTwistLin) '' A) :=
      Submodule.subset_span ⟨_, ⟨τ, X, hX, rfl⟩, rfl⟩
    have hS : cycleProj F N (perm F τ * symGroupSum F X) =
        ((Perm.sign τ : ℤ) : F) • (cycleProj F N ∘ₗ Steps345.signTwistLin) (perm F τ * altSum F X) := by
      rw [hPε, smul_smul, hss, one_smul]
    rcases rem23_sign_general (F := F) τ X with e | e
    · rw [SetLike.mem_coe, e, hS]
      exact Submodule.smul_mem _ _ hmem
    · rw [SetLike.mem_coe, e, hS]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)
  · rintro _ ⟨x, ⟨τ, X, hX, rfl⟩, rfl⟩
    have hmem : cycleProj F N (perm F τ * altSum F X) ∈ Submodule.span F (cycleProj F N '' A) :=
      Submodule.subset_span ⟨_, ⟨τ, X, hX, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hPε]
    refine Submodule.smul_mem _ _ ?_
    rcases rem23_sign_general (F := F) τ X with e | e
    · rw [← e]; exact hmem
    · rw [neg_eq_iff_eq_neg.1 e.symm]; exact Submodule.neg_mem _ hmem

/-- **v1.02 Remark 2.3 (cut in v1.03)** (v1.02 lines 301-305), by the remark's own route: `C_N ∩ A = C_N ∩ A'` follows from `P(I) = P(ε(I))`
and the duality of step (7) (`I^⊥ = A` and its column twin `ε(I)^⊥ = A'`), WITHOUT "ε is `±1` on `C_N`". -/
theorem rem23_direct [CharZero F] (Y : YoungSystem F N) (n : ℕ) :
    cycleSpan F N ⊓ Y.rowSum n = cycleSpan F N ⊓ Y.colSum n := by
  rcases Nat.lt_or_ge N (n + 1) with hN | h
  · have hrow : Y.rowSum n = ⊤ := eq_top_iff.2 fun a _ => (YoungSystem.mem_blockSum_iff Y).2
      fun mu hmu => absurd ((PropExact.numRows_le mu).trans (by omega)) hmu
    have hcol : Y.colSum n = ⊤ := eq_top_iff.2 fun a _ => (YoungSystem.mem_blockSum_iff Y).2
      fun mu hmu => absurd ((PropExact.firstRow_le mu).trans (by omega)) hmu
    rw [hrow, hcol]
  · ext c
    simp only [Submodule.mem_inf]
    refine and_congr_right fun hc => ?_
    rw [← prop21_step7_perp Y n h c, ← perp_blockSum_firstRow_iff Y n h c]
    have key : ∀ S : Submodule F (GrpAlg F N), (∀ a ∈ S, coeffPairing F c a = 0) ↔
        ∀ b ∈ S.map (cycleProj F N), coeffPairing F c b = 0 := by
      intro S
      constructor
      · rintro hS _ ⟨a, ha, rfl⟩
        rw [Steps345.coeffPairing_cycleProj hc]
        exact hS a ha
      · intro hS a ha
        rw [← Steps345.coeffPairing_cycleProj hc]
        exact hS _ ⟨a, ha, rfl⟩
    rw [key (altIdeal F N n), key (Y.blockSum {lam | n + 1 ≤ lam.firstRow}), rem23_proj Y n h]

end NagataHigman.Proofs

end
