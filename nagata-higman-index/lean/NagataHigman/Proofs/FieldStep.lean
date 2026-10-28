/-
NagataHigman/Proofs/FieldStep.lean — package Q3: `dim (C_N ∩ B_n)` is the same over every field of characteristic 0.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.02, lines 339-341 (Section 4.1:
"We work over ℂ" — the dimension of C_N ∩ B_n does not depend on the field of characteristic 0).
Route: by Proposition 2.1 (PropExact.prop_2_1_general) it suffices that dim W_{n,m} is field-independent. By (F1)
(PropExact.F1_spanning_proved), W_{n,m} is spanned by the multilinear a · L(v) · b, whose coordinates in the word basis
are natural numbers that do not depend on the field; and the rank of rational vectors does not change under a field
extension of ℚ (R1 below).
-/
import Mathlib
import NagataHigman.Proofs.PropExact
import NagataHigman.Cited.Classical

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv

namespace FieldStep

/-! ## R1. The rank of rational vectors is the same over every field of characteristic 0 -/

section RankBaseChange

variable {k : Type*} (K : Type*) [Field K] [CharZero K]

/-- The entrywise map `ℚ^k → K^k` (ℚ-linear). -/
def castVec : (k → ℚ) →ₗ[ℚ] (k → K) where
  toFun x := fun j => algebraMap ℚ K (x j)
  map_add' x y := by
    ext j
    simp
  map_smul' c x := by
    ext j
    simp [Algebra.smul_def]

theorem castVec_apply (x : k → ℚ) (j : k) : castVec K x j = algebraMap ℚ K (x j) := rfl

/-- ℚ-linearly independent rational vectors stay linearly independent over `K`. -/
theorem linearIndependent_castVec {ι : Type*} {x : ι → (k → ℚ)} (hx : LinearIndependent ℚ x) :
    LinearIndependent K (fun i => castVec K (x i)) := by
  rw [linearIndependent_iff'] at hx ⊢
  intro s c hsum i hi
  by_contra hci
  have hnot : ¬ ∀ lam : Module.Dual ℚ K, lam (c i) = 0 :=
    fun h => hci ((Module.forall_dual_apply_eq_zero_iff ℚ (c i)).mp h)
  obtain ⟨lam, hlam⟩ := not_forall.mp hnot
  refine hlam (hx s (fun i => lam (c i)) ?_ i hi)
  ext j
  have hj := congrFun hsum j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castVec_apply, Pi.zero_apply] at hj
  have h2 := congrArg lam hj
  rw [map_sum, map_zero] at h2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← h2]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [mul_comm (c i'), ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

/-- **R1**: `dim_K span_K (S) = dim_ℚ span_ℚ (S)` for a set `S` of rational vectors. -/
theorem finrank_span_castVec [Fintype k] (S : Set (k → ℚ)) :
    Module.finrank K (Submodule.span K (castVec K '' S)) = Module.finrank ℚ (Submodule.span ℚ S) := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℚ S
  have htfin : t.Finite := hli.setFinite
  have : Fintype t := htfin.fintype
  have hQ : Module.finrank ℚ (Submodule.span ℚ S) = Fintype.card t := by
    have h := finrank_span_eq_card hli
    rw [Subtype.range_val] at h
    rw [← hspan]
    exact h
  have hspanK : Submodule.span K (castVec K '' S) =
      Submodule.span K (Set.range (fun i : t => castVec K (i : k → ℚ))) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      have hs' : s ∈ Submodule.span ℚ t := hspan ▸ Submodule.subset_span hs
      have h1 : castVec K s ∈ Submodule.span ℚ (castVec K '' t) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map_of_mem hs'
      have h2 := Submodule.span_le_restrictScalars ℚ K (castVec K '' t) h1
      rw [Submodule.restrictScalars_mem, Set.image_eq_range] at h2
      exact h2
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, htS i.2, rfl⟩
  rw [hspanK, finrank_span_eq_card (linearIndependent_castVec K hli), hQ]

end RankBaseChange

/-! ## R2. The word coordinates of the spanning elements are natural numbers -/

/-- The number of orderings `π` with `a v_π b = w`: the coefficient of `x_w` in `a · L(v) · b`. -/
def count (n m : ℕ) (a b : List ℕ) (v : Fin n → List ℕ) (w : Perm (Fin m)) : ℕ :=
  (Finset.univ.filter (fun π : Perm (Fin n) => a ++ (List.ofFn (v ∘ π)).flatten ++ b = wordList w)).card

/-- The rational coordinate vectors of the multilinear spanning elements of (F1). -/
def coeffVecs (n m : ℕ) : Set (Perm (Fin m) → ℚ) :=
  {x | ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ), IsMultilinTriple m a v b ∧
    x = fun w => (count n m a b v w : ℚ)}

theorem wordCoord_sandwichElem (K : Type*) [Field K] {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (a b : List ℕ)
    (v : Fin n → List ℕ) (hv : ∀ i, v i ≠ []) :
    PropExact.wordCoord K m (sandwichElem K a v b) = fun w => (count n m a b v w : K) := by
  ext w
  show (sandwichElem K a v b).coeff (wordMono w) = _
  rw [Arcs.coeff_sandwichElem K hn hm a b v hv w, Finset.sum_boole]
  rfl

/-- `dim P` is unchanged by the word coordinates, for `P ⊆ V_m`. -/
theorem finrank_map_wordCoord (K : Type*) [Field K] {m : ℕ} (hm : 1 ≤ m) (P : Submodule K (FreeNUAlg K))
    (hP : P ≤ multilinSpace K m) :
    Module.finrank K (P.map (PropExact.wordCoord K m)) = Module.finrank K P := by
  have e : P.map (PropExact.wordCoord K m) = LinearMap.range ((PropExact.wordCoord K m).comp P.subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [e]
  exact LinearMap.finrank_range_of_inj
    (fun p q h => Subtype.ext (PropExact.wordCoord_injOn hm (hP p.2) (hP q.2) h))

/-- **R3**: `dim_K W_{n,m}` is the rank of one fixed set of rational vectors, for every field `K` of
characteristic `0`. -/
theorem finrank_multilinIdentities_eq_rat (K : Type*) [Field K] [CharZero K] (n m : ℕ) (hn : 1 ≤ n)
    (hm : 1 ≤ m) :
    Module.finrank K (multilinIdentities K n m) = Module.finrank ℚ (Submodule.span ℚ (coeffVecs n m)) := by
  rw [← finrank_map_wordCoord K hm (multilinIdentities K n m) inf_le_left, F1_spanning_proved n m hn, Submodule.map_span,
    ← finrank_span_castVec K (coeffVecs n m)]
  have hset : PropExact.wordCoord K m '' {p | ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ),
      IsMultilinTriple m a v b ∧ p = sandwichElem K a v b} = castVec K '' coeffVecs n m := by
    ext x
    constructor
    · rintro ⟨p, ⟨a, v, b, htr, rfl⟩, rfl⟩
      refine ⟨_, ⟨a, v, b, htr, rfl⟩, ?_⟩
      rw [wordCoord_sandwichElem K hn hm a b v htr.1]
      ext w
      simp [castVec_apply]
    · rintro ⟨y, ⟨a, v, b, htr, rfl⟩, rfl⟩
      refine ⟨_, ⟨a, v, b, htr, rfl⟩, ?_⟩
      rw [wordCoord_sandwichElem K hn hm a b v htr.1]
      ext w
      simp [castVec_apply]
  rw [hset]

/-! ## The small cases -/

theorem cycleSpan_eq_bot_of_le_one (K : Type*) [Field K] {N : ℕ} (hN : N ≤ 1) : cycleSpan K N = ⊥ := by
  unfold cycleSpan
  rw [Submodule.span_eq_bot]
  rintro _ ⟨σ, hσ, rfl⟩
  exfalso
  obtain ⟨x, hx, _⟩ := hσ.1
  have : Subsingleton (Fin N) := Fin.subsingleton_iff_le_one.mpr hN
  exact hx (Subsingleton.elim _ _)

theorem boxSum_zero_eq_bot {K : Type*} [Field K] {N : ℕ} (hN : 1 ≤ N) (Y : YoungSystem K N) : Y.boxSum 0 = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Submodule.mem_bot]
  refine YoungSystem.eq_zero_of_forall_rhoAlg Y a (fun mu => (YoungSystem.mem_blockSum_iff Y).mp ha mu ?_)
  rintro ⟨hrows, _⟩
  have h0 : mu.parts = 0 := Multiset.card_eq_zero.mp (Nat.le_zero.mp hrows)
  have := mu.parts_sum
  rw [h0, Multiset.sum_zero] at this
  omega

end FieldStep

open FieldStep NagataHigman.Cited in
/-- **Q3, Section 4.1** (v1.02 lines 339-341): `dim (C_N ∩ B_n)` is the same over every field `F` of characteristic `0` as over
`ℂ` (for the cited Young systems `youngSystem F N` and `youngSystemC N`). -/
theorem sec_4_1_field_proved (F : Type*) [Field F] [CharZero F] (n N : ℕ) :
    Module.finrank F (cycleSpan F N ⊓ (youngSystem F N).boxSum n : Submodule F (GrpAlg F N)) =
      Module.finrank ℂ (cycleSpan ℂ N ⊓ (youngSystemC N).boxSum n : Submodule ℂ (GrpAlg ℂ N)) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [cycleSpan_eq_bot_of_le_one F (by omega), cycleSpan_eq_bot_of_le_one ℂ (by omega), bot_inf_eq,
      bot_inf_eq, finrank_bot, finrank_bot]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [boxSum_zero_eq_bot (by omega), boxSum_zero_eq_bot (by omega), inf_bot_eq, inf_bot_eq, finrank_bot,
      finrank_bot]
  · have h1 := prop_2_1_general n m hn hm (youngSystem F (m + 1))
    have h2 := prop_2_1_general n m hn hm (youngSystemC (m + 1))
    have h3 := finrank_multilinIdentities_eq_rat F n m hn hm
    have h4 := finrank_multilinIdentities_eq_rat ℂ n m hn hm
    omega

open FieldStep in
/-- The dimension of `C_N ∩ B_n` is the same for ANY two fields of characteristic 0 and ANY Young system over
each (the route of `sec_4_1_field_proved` never uses which Young system was chosen: Proposition 2.1 holds for every
one, `prop_2_1_general`). Standard axioms only. -/
theorem finrank_inf_boxSum_eq (K K' : Type*) [Field K] [CharZero K] [Field K'] [CharZero K'] (n N : ℕ)
    (Y : YoungSystem K N) (Y' : YoungSystem K' N) :
    Module.finrank K (cycleSpan K N ⊓ Y.boxSum n : Submodule K (GrpAlg K N)) =
      Module.finrank K' (cycleSpan K' N ⊓ Y'.boxSum n : Submodule K' (GrpAlg K' N)) := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [cycleSpan_eq_bot_of_le_one K (by omega), cycleSpan_eq_bot_of_le_one K' (by omega), bot_inf_eq,
      bot_inf_eq, finrank_bot, finrank_bot]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [boxSum_zero_eq_bot (by omega), boxSum_zero_eq_bot (by omega), inf_bot_eq, inf_bot_eq, finrank_bot,
      finrank_bot]
  · have h1 := prop_2_1_general n m hn hm Y
    have h2 := prop_2_1_general n m hn hm Y'
    have h3 := finrank_multilinIdentities_eq_rat K n m hn hm
    have h4 := finrank_multilinIdentities_eq_rat K' n m hn hm
    omega

/-- **Section 4.1** (paper v1.02 lines 339-341), for ANY Young system `Y` over `F` and ANY Young system `Y'` over `ℂ`:
`dim_F (C_N ∩ B_n) = dim_ℂ (C_N ∩ B_n)`. Standard axioms only. -/
theorem sec_4_1_field_general (F : Type*) [Field F] [CharZero F] (n N : ℕ) (Y : YoungSystem F N)
    (Y' : YoungSystem ℂ N) :
    Module.finrank F (cycleSpan F N ⊓ Y.boxSum n : Submodule F (GrpAlg F N)) =
      Module.finrank ℂ (cycleSpan ℂ N ⊓ Y'.boxSum n : Submodule ℂ (GrpAlg ℂ N)) :=
  finrank_inf_boxSum_eq F ℂ n N Y Y'

/-- Over one field `F` of characteristic 0, `dim (C_N ∩ B_n)` does not depend on the Young system. Standard axioms
only. -/
theorem finrank_inf_boxSum_indep (F : Type*) [Field F] [CharZero F] (n N : ℕ) (Y Y' : YoungSystem F N) :
    Module.finrank F (cycleSpan F N ⊓ Y.boxSum n : Submodule F (GrpAlg F N)) =
      Module.finrank F (cycleSpan F N ⊓ Y'.boxSum n : Submodule F (GrpAlg F N)) :=
  finrank_inf_boxSum_eq F F n N Y Y'

end NagataHigman.Proofs

end
