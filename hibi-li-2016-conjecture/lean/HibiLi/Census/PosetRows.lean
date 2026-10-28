/-
HibiLi/Census/PosetRows.lean — the order and chain polytopes of a census poset as explicit integer row systems, with
their 0/1 hull and full dimension (the inputs of `fNum_eq_of_check`, FaceCount.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Rows (paper lines 222–225): order polytope `0 ≤ x_p`, `x_p ≤ 1`, `x_p − x_q ≤ 0` for `p ≤ q`;
chain polytope `0 ≤ x_p`, `∑_{p ∈ K} x_p ≤ 1` for every chain `K` (all chains, the empty one included), a chain being
given by its bitmask `K < 2^d`.
-/
import HibiLi.Census.ClosedFaces
import HibiLi.Defs.Census
import HibiLi.Example21.ZeroOneResult

namespace HibiLi.Census

variable {d : ℕ}

/-- The row `−x_p ≤ 0`. -/
def rowNonneg (p : Fin d) : Row d := (fun j => if j = p then -1 else 0, 0)

/-- The row `x_p ≤ 1`. -/
def rowLeOne (p : Fin d) : Row d := (fun j => if j = p then 1 else 0, 1)

/-- The row `x_p − x_q ≤ 0`. -/
def rowMono (p q : Fin d) : Row d := (fun j => (if j = p then 1 else 0) - (if j = q then 1 else 0), 0)

/-- The row `∑_{j ∈ K} x_j ≤ 1` for the bitmask `K`. -/
def rowChain (K : ℕ) : Row d := (fun j => if K.testBit j then 1 else 0, 1)

/-- The bitmask `K` is a chain of the order `le`. -/
def chainMaskOK (le : Fin d → Fin d → Bool) (K : ℕ) : Bool :=
  (List.finRange d).all fun p => (List.finRange d).all fun q =>
    !(K.testBit p && K.testBit q) || le p q || le q p

/-- Order polytope rows of the order `le` on `Fin d`. -/
def orderRows (le : Fin d → Fin d → Bool) : List (Row d) :=
  (List.finRange d).map rowNonneg ++ (List.finRange d).map rowLeOne ++
    (List.finRange d).flatMap fun p => ((List.finRange d).filter (le p)).map (rowMono p)

/-- Chain polytope rows of the order `le` on `Fin d`. -/
def chainRows (le : Fin d → Fin d → Bool) : List (Row d) :=
  (List.finRange d).map rowNonneg ++ ((List.range (2 ^ d)).filter (chainMaskOK le)).map rowChain

/-! ### Generic row computations (any `d`, any `le`) -/

theorem rowForm_rowNonneg (p : Fin d) (x : Fin d → ℝ) : rowForm (rowNonneg p) x = -x p := by
  simp [rowForm_apply, rowNonneg]

theorem rowForm_rowLeOne (p : Fin d) (x : Fin d → ℝ) : rowForm (rowLeOne p) x = x p := by
  simp [rowForm_apply, rowLeOne]

theorem rowForm_rowMono (p q : Fin d) (x : Fin d → ℝ) : rowForm (rowMono p q) x = x p - x q := by
  simp [rowForm_apply, rowMono, sub_mul, Finset.sum_sub_distrib]

theorem rowForm_rowChain (K : ℕ) (x : Fin d → ℝ) :
    rowForm (rowChain K : Row d) x = ∑ j ∈ Finset.univ.filter (fun j : Fin d => K.testBit j = true), x j := by
  simp [rowForm_apply, rowChain, Finset.sum_filter]

theorem mem_polyOf_orderRows (le : Fin d → Fin d → Bool) (x : Fin d → ℝ) :
    x ∈ polyOf (orderRows le) ↔ (∀ p, 0 ≤ x p ∧ x p ≤ 1) ∧ ∀ p q, le p q = true → x p ≤ x q := by
  simp only [polyOf, Set.mem_ofPred_eq, orderRows, List.forall_mem_append, List.forall_mem_map,
    List.forall_mem_flatMap, List.mem_finRange, List.mem_filter, forall_const, true_and,
    rowForm_rowNonneg, rowForm_rowLeOne, rowForm_rowMono]
  simp [rowNonneg, rowLeOne, rowMono, forall_and]

theorem mem_polyOf_chainRows (le : Fin d → Fin d → Bool) (x : Fin d → ℝ) :
    x ∈ polyOf (chainRows le) ↔ (∀ p, 0 ≤ x p) ∧ ∀ m < 2 ^ d, chainMaskOK le m = true →
      ∑ j ∈ Finset.univ.filter (fun j : Fin d => m.testBit j = true), x j ≤ 1 := by
  simp only [polyOf, Set.mem_ofPred_eq, chainRows, List.forall_mem_append, List.forall_mem_map,
    List.mem_finRange, List.mem_filter, List.mem_range, forall_const, and_imp,
    rowForm_rowNonneg, rowForm_rowChain]
  simp [rowNonneg, rowChain]

theorem chainMaskOK_iff (le : Fin d → Fin d → Bool) (m : ℕ) :
    chainMaskOK le m = true ↔
      ∀ p q : Fin d, m.testBit p = true → m.testBit q = true → le p q = true ∨ le q p = true := by
  simp only [chainMaskOK, List.all_eq_true, List.mem_finRange, forall_const]
  refine forall_congr' fun p => forall_congr' fun q => ?_
  cases m.testBit p <;> cases m.testBit q <;> simp

/-- Every subset `K` of `Fin d` is the bitmask of some `m < 2 ^ d` (namely `m = ∑_{j ∈ K} 2^j`). -/
theorem exists_mask (K : Finset (Fin d)) : ∃ m < 2 ^ d, ∀ j : Fin d, m.testBit j = true ↔ j ∈ K := by
  classical
  let f : Fin d → Fin 2 := fun j => if j ∈ K then 1 else 0
  refine ⟨finFunctionFinEquiv f, (finFunctionFinEquiv f).isLt, fun j => ?_⟩
  have hj : (finFunctionFinEquiv f : ℕ) / 2 ^ (j : ℕ) % 2 = (f j : ℕ) :=
    congrArg (fun g => (g j : ℕ)) (finFunctionFinEquiv.symm_apply_apply f)
  rw [Nat.testBit_eq_decide_div_mod_eq, hj, decide_eq_true_iff]
  by_cases hK : j ∈ K <;> simp [f, hK]

/-! ### The census posets -/

theorem card_censusPoset (i : Fin 16) : Fintype.card (censusPoset i) = 6 := rfl

/-- A bitmask passing `chainMaskOK` gives a chain of `censusPoset i`. -/
theorem isChainSet_of_chainMaskOK (i : Fin 16) {m : ℕ} (hm : chainMaskOK (censusLe i) m = true) :
    IsChainSet (censusPoset i) (Finset.univ.filter fun j : Fin 6 => m.testBit j = true) := by
  intro a ha b hb _
  exact (chainMaskOK_iff _ m).1 hm a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2

/-- The bitmask of a chain of `censusPoset i` passes `chainMaskOK`. -/
theorem chainMaskOK_of_isChainSet (i : Fin 16) {K : Finset (censusPoset i)} (hK : IsChainSet (censusPoset i) K)
    {m : ℕ} (hmK : ∀ j : Fin 6, m.testBit j = true ↔ j ∈ K) : chainMaskOK (censusLe i) m = true := by
  refine (chainMaskOK_iff _ m).2 fun p q hp hq => ?_
  by_cases hpq : p = q
  · subst hpq
    exact Or.inl (censusLe_refl i p)
  · exact hK ((hmK p).1 hp) ((hmK q).1 hq) hpq

theorem orderPolytope_census (i : Fin 16) :
    orderPolytope (censusPoset i) = polyOf (orderRows (censusLe i)) := by
  ext x
  exact (mem_polyOf_orderRows (censusLe i) x).symm

theorem chainPolytope_census (i : Fin 16) :
    chainPolytope (censusPoset i) = polyOf (chainRows (censusLe i)) := by
  ext x
  refine Iff.trans ?_ (mem_polyOf_chainRows (censusLe i) x).symm
  refine and_congr Iff.rfl ⟨fun h m _ hm => h _ (isChainSet_of_chainMaskOK i hm), fun h K hK => ?_⟩
  obtain ⟨m, hm64, hmK⟩ := exists_mask (d := 6) K
  have hfilter : (Finset.univ.filter fun j : Fin 6 => m.testBit j = true) = K := by
    ext j
    simp [hmK]
  have := h m hm64 (chainMaskOK_of_isChainSet i hK hmK)
  rwa [hfilter] at this

theorem orderRows_hull (i : Fin 16) :
    polyOf (orderRows (censusLe i)) =
      convexHull ℝ (polyOf (orderRows (censusLe i)) ∩ zeroOneVectors (Fin 6)) := by
  have h := orderPolytope_eq_convexHull_zeroOne (censusPoset i)
  rw [orderPolytope_census] at h
  exact h

theorem chainRows_hull (i : Fin 16) :
    polyOf (chainRows (censusLe i)) =
      convexHull ℝ (polyOf (chainRows (censusLe i)) ∩ zeroOneVectors (Fin 6)) := by
  have h := chainPolytope_eq_convexHull_zeroOne (censusPoset i)
  rw [chainPolytope_census] at h
  exact h

theorem orderRows_adim (i : Fin 16) : adim (polyOf (orderRows (censusLe i))) = 6 := by
  have h := (sec1_zero_one_polytopes_proved (censusPoset i)).2.2.1
  rw [orderPolytope_census, card_censusPoset] at h
  exact h

theorem chainRows_adim (i : Fin 16) : adim (polyOf (chainRows (censusLe i))) = 6 := by
  have h := (sec1_zero_one_polytopes_proved (censusPoset i)).2.2.2
  rw [chainPolytope_census, card_censusPoset] at h
  exact h

end HibiLi.Census
