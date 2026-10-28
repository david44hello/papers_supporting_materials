/-
NagataHigman/Proofs/Step6Arcs.lean — Prop 2.1 step (6), the displayed formula with the paper's arcs:
Φ⁻¹(P(τE_X)) = x_ξ · L(x_{Arc_1..n}) · x_ζ.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Mathlib
import NagataHigman.Proofs.Steps345
import NagataHigman.Proofs.Step6Claims
import NagataHigman.Proofs.Arcs

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs.Step6Arcs

open Equiv Finset NagataHigman.FirstReturn

/-! ## 1. One arc: it is a `τ`-chain, its inner points are off `X`, its last point is in `X` -/

section OneArc

variable {N : ℕ}

/-- Consecutive points of `Arc(x)` are related by `τ`. -/
theorem arc_follows (τ : Perm (Fin N)) (X : Finset (Fin N)) (x : Fin N) : Arcs.Follows τ (arc τ X x) := by
  unfold Arcs.Follows arc
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.getElem_map, List.getElem_range]
  rw [pow_succ' τ (i + 1), Perm.mul_apply]

/-- Every point of `Arc(x)` but the last lies off `X`. -/
theorem not_mem_of_mem_dropLast_arc {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X)
    {y : Fin N} (hy : y ∈ (arc τ X x).dropLast) : y ∉ X := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i + 1 < returnTime τ X x := by
    simp only [List.length_dropLast, arc, List.length_map, List.length_range] at hi
    omega
  rw [List.getElem_dropLast]
  simp only [arc, List.getElem_map, List.getElem_range]
  exact returnTime_min (exists_return_of_mem hx) (by omega) hi'

/-- The last point of `Arc(x)` (it is `s(x)`) lies in `X`. -/
theorem mem_of_mem_getLast?_arc {τ : Perm (Fin N)} {X : Finset (Fin N)} {x : Fin N} (hx : x ∈ X)
    {y : Fin N} (hy : y ∈ (arc τ X x).getLast?) : y ∈ X := by
  rw [Steps345.arc_getLast? hx, Option.mem_some_iff] at hy
  exact hy ▸ Steps345.firstReturn_mem hx

end OneArc

/-! ## 2. Several arcs: no repeated point, every point covered, `τ` agrees with their cycle off `X` -/

section Arcs

variable {N : ℕ}

/-- The arcs of distinct points of `X`, concatenated, have no repeated point. -/
theorem flatten_map_arc_nodup {τ : Perm (Fin N)} (hτ : IsFullCycle τ) {X : Finset (Fin N)} (hX : X.Nonempty)
    {pts : List (Fin N)} (hnd : pts.Nodup) (hpts : ∀ x ∈ pts, x ∈ X) : (pts.map (arc τ X)).flatten.Nodup := by
  rw [List.nodup_flatten, List.pairwise_map]
  refine ⟨fun l hl => ?_, List.Pairwise.imp_of_mem (fun {x y} hx hy hxy => ?_) hnd⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    exact Steps345.arc_nodup (hpts x hx)
  · intro z hzx hzy
    exact hxy ((Steps345.existsUnique_mem_arc (Arcs.sameCycle_of_isFullCycle hτ) hX z).unique
      ⟨hpts x hx, hzx⟩ ⟨hpts y hy, hzy⟩)

/-- If the points `pts` include all of `X`, their arcs cover every point. -/
theorem mem_flatten_map_arc {τ : Perm (Fin N)} (hτ : IsFullCycle τ) {X : Finset (Fin N)} (hX : X.Nonempty)
    {pts : List (Fin N)} (hpts : ∀ x ∈ X, x ∈ pts) (y : Fin N) : y ∈ (pts.map (arc τ X)).flatten := by
  obtain ⟨x, ⟨hx, hy⟩, -⟩ := Steps345.existsUnique_mem_arc (Arcs.sameCycle_of_isFullCycle hτ) hX y
  exact List.mem_flatten.mpr ⟨arc τ X x, List.mem_map.mpr ⟨x, hpts x hx, rfl⟩, hy⟩

/-- A permutation that follows each block of a covering nodup block list, whose block ends lie in `X`, agrees off
`X` with the cycle of the concatenated blocks. -/
theorem agree_off (τ : Perm (Fin N)) (X : Finset (Fin N)) (Bs : List (List (Fin N)))
    (hnd : Bs.flatten.Nodup) (hcov : ∀ x, x ∈ Bs.flatten) (hfol : ∀ B ∈ Bs, Arcs.Follows τ B)
    (hend : ∀ B ∈ Bs, ∀ x ∈ B.getLast?, x ∈ X) :
    ∀ x, x ∉ X → τ x = List.formPerm Bs.flatten x := by
  intro x hx
  obtain ⟨B, hB, hxB⟩ := List.mem_flatten.mp (hcov x)
  have hxd : x ∈ B.dropLast := by
    refine List.mem_dropLast_of_mem_of_ne_getLast hxB (fun hl => hx (hend B hB x ?_))
    rw [List.getLast?_eq_some_getLast (List.ne_nil_of_mem hxB)]
    exact Option.mem_some_iff.mpr hl.symm
  obtain ⟨P, S, y, hsplit⟩ := Arcs.exists_split_of_mem_dropLast hxd
  have hinf : B <:+: Bs.flatten := by
    obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hB
    exact ⟨L1.flatten, L2.flatten, by simp⟩
  have h1 := hfol B hB
  have h2 := (Arcs.follows_formPerm hnd).infix hinf
  rw [hsplit] at h1 h2
  rw [h1.apply, h2.apply]

/-- `(ζ, z, ξ)` followed by `L`, read cyclically from `z`, is `z, ξ, L, ζ`. -/
theorem rotated_split {α : Type*} (ζ ξ L : List α) (z : α) : (ζ ++ z :: ξ) ++ L ~r z :: (ξ ++ L ++ ζ) := by
  have e1 : (ζ ++ z :: ξ) ++ L = ζ ++ (z :: (ξ ++ L)) := by simp
  have e2 : z :: (ξ ++ L ++ ζ) = (z :: (ξ ++ L)) ++ ζ := by simp
  rw [e1, e2]
  exact List.isRotated_append

/-- The base points `w₀, e 0, …, e (n-1)`: no repeats, all in `X`, and all of `X` (by counting). -/
theorem pts_spec {n : ℕ} {X : Finset (Fin N)} (hX : X.card = n + 1) {w₀ : Fin N} (hw₀ : w₀ ∈ X)
    {e : Fin n → Fin N} (he : Function.Injective e) (heX : ∀ i, e i ∈ X ∧ e i ≠ w₀) :
    (w₀ :: List.ofFn e).Nodup ∧ (∀ x ∈ w₀ :: List.ofFn e, x ∈ X) ∧ ∀ x ∈ X, x ∈ w₀ :: List.ofFn e := by
  have hnd : (w₀ :: List.ofFn e).Nodup := by
    refine List.nodup_cons.mpr ⟨fun h => ?_, List.nodup_ofFn.mpr he⟩
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
    exact (heX i).2 hi
  have hin : ∀ x ∈ w₀ :: List.ofFn e, x ∈ X := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hw₀
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact (heX i).1
  have heq : (w₀ :: List.ofFn e).toFinset = X :=
    Finset.eq_of_subset_of_card_le (fun y hy => hin y (List.mem_toFinset.mp hy))
      (by rw [List.toFinset_card_of_nodup hnd, hX]; simp)
  exact ⟨hnd, hin, fun x hx => List.mem_toFinset.mp (heq ▸ hx)⟩

end Arcs

/-! ## 3. The formula -/

/-- **Proposition 2.1, step (6), the displayed formula with the paper's arcs** (lines 329-339): write the arc
containing `N` as `Arc_0 = (ζ, N, ξ)` and number the other `n` arcs `Arc_1, …, Arc_n` in any way (`e`). Then
`(ξ, Arc_1, …, Arc_n, ζ)` is a multilinear triple and `Φ⁻¹(P(τ E_X)) = x_ξ · L(x_{Arc_1}, …, x_{Arc_n}) · x_ζ`. -/
theorem step6_formula_arcs {F : Type*} [Field F] [CharZero F] (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (τ : Equiv.Perm (Fin (m + 1))) (hτ : IsFullCycle τ) (X : Finset (Fin (m + 1))) (hX : X.card = n + 1)
    (w₀ : Fin (m + 1)) (hw₀ : w₀ ∈ X) (ζ ξ : List (Fin (m + 1)))
    (hsplit : arc τ X w₀ = ζ ++ [Fin.last m] ++ ξ)
    (e : Fin n → Fin (m + 1)) (he : Function.Injective e) (heX : ∀ i, e i ∈ X ∧ e i ≠ w₀) :
    IsMultilinTriple m (ξ.map Fin.val) (fun i => (arc τ X (e i)).map Fin.val) (ζ.map Fin.val) ∧
      ∃ c : Equiv.Perm (Fin m) → F,
        cycleLin F m c = cycleProj F (m + 1) (perm F τ * altSum F X) ∧
        wordLin F m c = sandwichElem F (ξ.map Fin.val) (fun i => (arc τ X (e i)).map Fin.val) (ζ.map Fin.val) := by
  have hm : 1 ≤ m := le_trans hn hnm
  have hXne : X.Nonempty := ⟨w₀, hw₀⟩
  obtain ⟨hptsnd, hptsX, hXpts⟩ := pts_spec hX hw₀ he heX
  have hA : arc τ X w₀ = ζ ++ Fin.last m :: ξ := by rw [hsplit]; simp
  -- the arcs `Arc_0, Arc_1, …, Arc_n`, concatenated
  have hflat : ((w₀ :: List.ofFn e).map (arc τ X)).flatten =
      (ζ ++ Fin.last m :: ξ) ++ (List.ofFn fun i => arc τ X (e i)).flatten := by
    rw [List.map_cons, List.flatten_cons, hA, List.map_ofFn]
    rfl
  have hBnd := flatten_map_arc_nodup hτ hXne hptsnd hptsX
  have hBcov := mem_flatten_map_arc hτ hXne hXpts
  have hD : ((ζ ++ Fin.last m :: ξ) ++ (List.ofFn fun i => arc τ X (e i)).flatten).Nodup := hflat ▸ hBnd
  have hrot := rotated_split ζ ξ (List.ofFn fun i => arc τ X (e i)).flatten (Fin.last m)
  -- the block configuration `N → ξ → Arc_1 → ⋯ → Arc_n → ζ → N`
  let K : Arcs.BlockConfig m n :=
    { a := ξ, b := ζ, v := fun i => arc τ X (e i)
      v_ne := fun i => Steps345.arc_ne_nil (heX i).1
      nodup := hrot.nodup_iff.mp hD
      cover := fun x => hrot.mem_iff.mp (hflat ▸ hBcov x) }
  have hblk : ∀ B, (B = K.B0 ∨ B ∈ List.ofFn K.v) → ∃ x ∈ X, B = arc τ X x := by
    rintro B (rfl | hB)
    · exact ⟨w₀, hw₀, hA.symm⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
      exact ⟨e i, (heX i).1, rfl⟩
  have hsplits : K.Splits X := by
    constructor
    · intro B hB x hx
      obtain ⟨y, hy, rfl⟩ := hblk B hB
      exact not_mem_of_mem_dropLast_arc hy hx
    · intro B hB x hx
      obtain ⟨y, hy, rfl⟩ := hblk B hB
      exact mem_of_mem_getLast?_arc hy hx
  -- `τ` agrees off `X` with the cycle `K.tau` (the arcs taken in the order `e`)
  have hagree : ∀ x, x ∉ X → τ x = K.tau x := by
    intro x hx
    have h1 := agree_off τ X ((w₀ :: List.ofFn e).map (arc τ X)) hBnd hBcov
      (fun B hB => by obtain ⟨y, -, rfl⟩ := List.mem_map.mp hB; exact arc_follows τ X y)
      (fun B hB => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hB
        exact fun z hz => mem_of_mem_getLast?_arc (hptsX y hy) hz) x hx
    rw [h1, hflat, List.formPerm_eq_of_isRotated hD hrot]
    rfl
  -- coefficientwise: `P(τ E_X) = P(K.tau E_X) = Φ(x_ξ · L(x_{Arc_i}) · x_ζ)`
  have hcoeff : ∀ w : Perm (Fin m), (perm F τ * altSum F X).coeff (wordCycle w) =
      (sandwichElem F (ξ.map Fin.val) (fun i => (arc τ X (e i)).map Fin.val) (ζ.map Fin.val)).coeff
        (wordMono w) := by
    intro w
    have hK := K.coeff_eq F hn hm hsplits w
    rw [Arcs.coeff_fullCycle F (K.tau_isFullCycle hn) (wordCycle_isFullCycle hm w)] at hK
    rw [Arcs.coeff_fullCycle F hτ (wordCycle_isFullCycle hm w)]
    have hPQ : (∀ x, x ∉ X → wordCycle w x = τ x) ↔ (∀ x, x ∉ X → wordCycle w x = K.tau x) :=
      forall_congr' fun x => imp_congr_right fun hx => by rw [hagree x hx]
    simp only [hPQ]
    exact hK
  have htrip : IsMultilinTriple m (ξ.map Fin.val) (fun i => (arc τ X (e i)).map Fin.val) (ζ.map Fin.val) := by
    refine ⟨fun i => by simpa using Steps345.arc_ne_nil (heX i).1, ?_⟩
    obtain ⟨w, hw⟩ := Arcs.exists_cycList_eq K.nodup K.list_length rfl
    have htail : List.ofFn (fun i => (w i).castSucc) =
        ξ ++ (List.ofFn fun i => arc τ X (e i)).flatten ++ ζ := congrArg List.tail hw
    have heq : ξ.map Fin.val ++ (List.ofFn fun i => (arc τ X (e i)).map Fin.val).flatten ++ ζ.map Fin.val =
        wordList w := by
      rw [← Arcs.map_val_cycList_tail, htail]
      simp [List.map_flatten, List.map_ofFn, Function.comp_def]
    rw [heq]
    exact Arcs.wordList_perm_range w
  refine ⟨htrip, PropExact.cycCoord F m (perm F τ * altSum F X), (Steps21.cycleProj_eq hm _).symm, ?_⟩
  have hc : PropExact.cycCoord F m (perm F τ * altSum F X) = PropExact.wordCoord F m
      (sandwichElem F (ξ.map Fin.val) (fun i => (arc τ X (e i)).map Fin.val) (ζ.map Fin.val)) := by
    ext w
    exact hcoeff w
  rw [hc, Steps21.wordLin_wordCoord hm (sandwichElem_mem_multilinSpace (F := F) hm _ _ _ htrip)]

/-- The naming hypotheses of `step6_formula_arcs` can always be met: `N` lies on the arc of some `w₀ ∈ X`. -/
theorem step6_names_exist {N : ℕ} (τ : Equiv.Perm (Fin (N + 1))) (hτ : IsFullCycle τ) (X : Finset (Fin (N + 1)))
    (hX : X.Nonempty) :
    ∃ w₀ ∈ X, ∃ ζ ξ : List (Fin (N + 1)), arc τ X w₀ = ζ ++ [Fin.last N] ++ ξ := by
  obtain ⟨w₀, ⟨hw₀, hmem⟩, -⟩ :=
    Steps345.existsUnique_mem_arc (Arcs.sameCycle_of_isFullCycle hτ) hX (Fin.last N)
  obtain ⟨ζ, ξ, h⟩ := List.append_of_mem hmem
  exact ⟨w₀, hw₀, ζ, ξ, by rw [h]; simp⟩

end NagataHigman.Proofs.Step6Arcs

end
