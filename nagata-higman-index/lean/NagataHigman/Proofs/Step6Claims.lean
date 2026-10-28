/-
NagataHigman/Proofs/Step6Claims.lean — r4 F1: the three claims of Proposition 2.1, step (6), as theorems.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.10, lines 352-382.
Routes: formula = forward_block_lemma; its sign is +1 because the coefficient of τ itself in τ E_X is 1 while the
coefficients of a·L(v)·b are natural numbers (characteristic 0). converse = converse_block_lemma's construction,
re-run here so that it also returns IsFullCycle τ (BlockConfig.tau_isFullCycle). bij = s fixes the points off X.
-/
import Mathlib
import NagataHigman.Proofs.Steps345

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset

variable {F : Type*} [Field F]

open Arcs in
/-- `converse_block_lemma`, also returning that `τ = Φ(a v_1 ⋯ v_n b)` is an `N`-cycle (same construction). -/
theorem converse_block_lemma_full {m n : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) (a : List ℕ) (v : Fin n → List ℕ)
    (b : List ℕ) (h : IsMultilinTriple m a v b) :
    ∃ (τ : Perm (Fin (m + 1))) (X : Finset (Fin (m + 1))), IsFullCycle τ ∧ X.card = n + 1 ∧
      ∀ w : Perm (Fin m), (perm F τ * altSum F X).coeff (wordCycle w) =
        (sandwichElem F a v b).coeff (wordMono w) := by
  have hm : 1 ≤ m := le_trans hn hnm
  obtain ⟨hvne, hperm⟩ := h
  let toPt : ℕ → Fin (m + 1) := fun k => Fin.ofNat (m + 1) k
  have hlt : ∀ k ∈ a ++ (List.ofFn v).flatten ++ b, k < m := fun k hk =>
    List.mem_range.mp (hperm.mem_iff.mp hk)
  have hval : ∀ k, k < m → (toPt k : ℕ) = k := fun k hk => by
    simp only [toPt, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hmapval : ∀ L : List ℕ, (∀ k ∈ L, k < m) → (L.map toPt).map Fin.val = L := by
    intro L hL
    rw [List.map_map]
    conv_rhs => rw [← List.map_id L]
    exact List.map_congr_left (fun k hk => hval k (hL k hk))
  have hall : (Fin.last m :: (a.map toPt ++ (List.ofFn fun i => (v i).map toPt).flatten ++ b.map toPt)) =
      Fin.last m :: (a ++ (List.ofFn v).flatten ++ b).map toPt := by
    simp [List.map_flatten, List.map_ofFn, Function.comp_def]
  have hnd0 : (a ++ (List.ofFn v).flatten ++ b).Nodup := hperm.nodup_iff.mpr List.nodup_range
  let K : BlockConfig m n :=
    { a := a.map toPt, b := b.map toPt, v := fun i => (v i).map toPt
      v_ne := fun i => by simpa using hvne i
      nodup := by
        rw [hall]
        refine List.nodup_cons.mpr ⟨?_, hnd0.map_on ?_⟩
        · intro hmem
          obtain ⟨k, hk, hkl⟩ := List.mem_map.mp hmem
          have := congrArg Fin.val hkl
          rw [hval k (hlt k hk), Fin.val_last] at this
          exact absurd (hlt k hk) (by omega)
        · intro x hx y hy hxy
          rw [← hval x (hlt x hx), ← hval y (hlt y hy), hxy]
      cover := by
        intro x
        rw [hall]
        rcases Fin.eq_castSucc_or_eq_last x with ⟨j, rfl⟩ | rfl
        · refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j, hperm.mem_iff.mpr (List.mem_range.mpr j.isLt), ?_⟩)
          ext
          simp [hval j j.isLt]
        · exact List.mem_cons_self }
  refine ⟨K.tau, K.ends, K.tau_isFullCycle hn, K.card_ends, fun w => ?_⟩
  rw [K.coeff_eq F hn hm K.splits_ends w]
  have ha : K.a.map Fin.val = a := hmapval a (fun k hk => hlt k (by simp [hk]))
  have hb : K.b.map Fin.val = b := hmapval b (fun k hk => hlt k (by simp [hk]))
  have hv : (fun i => (K.v i).map Fin.val) = v := by
    funext i
    exact hmapval (v i) (fun k hk => hlt k
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨v i, List.mem_ofFn.mpr ⟨i, rfl⟩, hk⟩))))
  rw [ha, hb, hv]

/-- **Proposition 2.1, step (6)** (line 352): `π ↦ ρ := s ∘ π` is a bijection from `Π` onto the cycles on `X`
fixing the points outside `X` (the `(n+1)`-cycles on `X` when `|X| = n + 1`). (`τ` full and `X ≠ ∅` are not needed.) -/
theorem prop21_step6_bij {N : ℕ} (τ : Perm (Fin N)) (_hτ : IsFullCycle τ) (X : Finset (Fin N))
    (_hX : X.Nonempty) :
    Set.BijOn (fun π => firstReturn τ X * π)
      {π | π.support ⊆ X ∧ (firstReturn τ X * π).IsCycleOn (X : Set (Fin N))}
      {ρ | ρ.support ⊆ X ∧ ρ.IsCycleOn (X : Set (Fin N))} := by
  have hsX : (firstReturn τ X).support ⊆ X := fun x hx => by
    by_contra hn
    exact Perm.mem_support.1 hx (Steps345.firstReturn_of_not_mem hn)
  refine ⟨fun π hπ => ⟨(Perm.support_mul_le _ _).trans (Finset.union_subset hsX hπ.1), hπ.2⟩,
    fun π _ π' _ e => mul_left_cancel e, fun ρ hρ => ⟨(firstReturn τ X)⁻¹ * ρ, ⟨?_, ?_⟩, ?_⟩⟩
  · exact (Perm.support_mul_le _ _).trans (Finset.union_subset (by rwa [Perm.support_inv]) hρ.1)
  · rw [mul_inv_cancel_left]
    exact hρ.2
  · exact mul_inv_cancel_left _ _

/-- **Proposition 2.1, step (6)** (lines 352-367): for an `N`-cycle `τ` and `|X| = n + 1`, `P(τ E_X)` is `Φ` of an
(F1) element: `Φ⁻¹(∑_{π ∈ Π} τπ) = a · L(v_1, …, v_n) · b` with a multilinear triple (`v_i` nonempty; in the paper
`a = x_ξ`, `v_i = x_{Arc_i}`, `b = x_ζ`; that identification is inside `forward_block_lemma`), with sign `+1`. -/
theorem prop21_step6_formula [CharZero F] (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (τ : Perm (Fin (m + 1)))
    (hτ : IsFullCycle τ) (X : Finset (Fin (m + 1))) (hX : X.card = n + 1) :
    ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ) (c : Perm (Fin m) → F), IsMultilinTriple m a v b ∧
      wordLin F m c = sandwichElem F a v b ∧ cycleLin F m c = cycleProj F (m + 1) (perm F τ * altSum F X) := by
  have hm : 1 ≤ m := le_trans hn hnm
  obtain ⟨p, hp, hcoeff⟩ := forward_block_lemma (F := F) hn hnm τ X hX
  obtain ⟨w₀, hw₀⟩ := exists_wordCycle_eq hτ
  -- the coefficient of `τ` itself in `τ E_X` is `1`
  have h1 : (perm F τ * altSum F X).coeff (wordCycle w₀) = 1 := by
    rw [hw₀, Arcs.coeff_perm_mul_altSum (F := F), inv_mul_cancel, ite_eq_left (by simp)]
    simp
  rcases hp with rfl | ⟨a, v, b, s, htrip, hs, rfl⟩
  · have h0 := hcoeff w₀
    rw [h1] at h0
    simp at h0
  · have hcnt := hcoeff w₀
    rw [h1, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      Arcs.coeff_sandwichElem F hn hm a b v htrip.1 w₀, Finset.sum_boole] at hcnt
    rcases hs with rfl | rfl
    · refine ⟨a, v, b, PropExact.cycCoord F m (perm F τ * altSum F X), htrip, ?_,
        (Steps21.cycleProj_eq hm _).symm⟩
      have hc : PropExact.cycCoord F m (perm F τ * altSum F X) =
          PropExact.wordCoord F m (sandwichElem F a v b) := by
        ext w
        show (perm F τ * altSum F X).coeff (wordCycle w) = (sandwichElem F a v b).coeff (wordMono w)
        rw [hcoeff w, one_smul]
      rw [hc, Steps21.wordLin_wordCoord hm (sandwichElem_mem_multilinSpace (F := F) hm a v b htrip)]
    · exfalso
      exact Nat.cast_add_one_ne_zero _ (by linear_combination hcnt)

/-- **Proposition 2.1, step (6), converse** (lines 375-382): every multilinear `a · L(v_1, …, v_n) · b` is `Φ` of
`P(τ E_X)` for an `N`-cycle `τ` (`τ = Φ(a v_1 ⋯ v_n b)`) and some `X` with `|X| = n + 1`. -/
theorem prop21_step6_converse (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (a : List ℕ) (v : Fin n → List ℕ)
    (b : List ℕ) (h : IsMultilinTriple m a v b) :
    ∃ (τ : Perm (Fin (m + 1))) (X : Finset (Fin (m + 1))) (c : Perm (Fin m) → F), IsFullCycle τ ∧
      X.card = n + 1 ∧ wordLin F m c = sandwichElem F a v b ∧
      cycleLin F m c = cycleProj F (m + 1) (perm F τ * altSum F X) := by
  have hm : 1 ≤ m := le_trans hn hnm
  obtain ⟨τ, X, hτ, hX, hco⟩ := converse_block_lemma_full (F := F) hn hnm a v b h
  have hc : PropExact.cycCoord F m (perm F τ * altSum F X) = PropExact.wordCoord F m (sandwichElem F a v b) := by
    ext w
    exact hco w
  refine ⟨τ, X, PropExact.cycCoord F m (perm F τ * altSum F X), hτ, hX, ?_, (Steps21.cycleProj_eq hm _).symm⟩
  rw [hc, Steps21.wordLin_wordCoord hm (sandwichElem_mem_multilinSpace (F := F) hm a v b h)]

end NagataHigman.Proofs

end
