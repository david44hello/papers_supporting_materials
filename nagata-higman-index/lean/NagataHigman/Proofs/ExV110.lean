/-
NagataHigman/Proofs/ExV110.lean — proofs for the new v1.10 examples: the Example after
Proposition 2.1 (n = m = 2, N = 3; claim N7) and the Section 1 box examples (claim N3). The rows are in
Paper/Statements.lean. Paper: v1.10; "v1.10 l. N" = line N of its LaTeX source.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Route: as the paper — W_{2,2} from (F1); the components from the 1-dimensional blocks; C_3 ∩ I_(2,1) from the
components; the count 2 - 1 = 1 is then a CHECK of Proposition 2.1, not a use of it. An ARBITRARY Young system.
-/
import NagataHigman.Cited.Classical
import NagataHigman.Defs.Spanning
import NagataHigman.Proofs.Shapes
import NagataHigman.Proofs.BlocksOrth
import NagataHigman.Proofs.JucysMurphy
import NagataHigman.Proofs.TwoCorner.Gamma
import NagataHigman.Proofs.TwoCorner.GammaC
import NagataHigman.Proofs.TwoCorner.Spectral
import NagataHigman.Proofs.SignTwist
import NagataHigman.Proofs.BlockIdeal
import NagataHigman.Proofs.FreeAlgebraLayer
import NagataHigman.Proofs.Tableaux
import NagataHigman.Proofs.Lemma31
import NagataHigman.Proofs.Restriction
import NagataHigman.Proofs.TwoCorner.Section4
import NagataHigman.Proofs.MainTheorems
import NagataHigman.Proofs.PropExact
import NagataHigman.Proofs.Section4Remarks
import NagataHigman.Proofs.FieldStep
import NagataHigman.Proofs.BoxExists
import NagataHigman.Proofs.Steps21
import NagataHigman.Proofs.NonVacuity
import NagataHigman.Proofs.Surfaced
import NagataHigman.Proofs.CentralIdempotent
import NagataHigman.Proofs.YoungIdemCoeff
import NagataHigman.Proofs.TwoCorner.Lemma42Steps
import NagataHigman.Proofs.RectangleCommutant
import NagataHigman.Proofs.Steps345
import NagataHigman.Proofs.F1Span
import NagataHigman.Proofs.TwoCorner.Lemma42Chain
import NagataHigman.Proofs.TwoCorner.Theorem44
import NagataHigman.Proofs.SquareSpanCorners
import NagataHigman.Proofs.Step6Claims
import NagataHigman.Proofs.IdemPrimitive
import NagataHigman.Proofs.DiagonalHooks
import NagataHigman.Proofs.MatrixInvariants
import NagataHigman.Cited.MatrixInvariants
import NagataHigman.Proofs.Examples
import NagataHigman.Proofs.Step6Arcs
import NagataHigman.Proofs.FieldIndep

noncomputable section

/-! ## Part A — proofs -/

namespace NagataHigman.Proofs.ExV110

open NagataHigman Equiv Finset

variable {F : Type*} [Field F]

/-! ### The three shapes of 3 -/

/-- The shape `(2, 1)`. -/
def shape21 : Shape 3 := ⟨{2, 1}, fun {i} hi => by simp at hi; omega, by simp⟩

/-- The shape `(3)`: one row. -/
def shape3 : Shape 3 := ⟨{3}, fun {i} hi => by simp at hi; omega, by simp⟩

/-- The shape `(1, 1, 1)`: one column. -/
def shape111 : Shape 3 := ⟨{1, 1, 1}, fun {i} hi => by simp at hi; omega, by simp⟩

/-- Only `(2, 1)` fits in the `2 × 2` box. -/
theorem inBox_two_iff (lam : Shape 3) : lam.InBox 2 ↔ lam = shape21 := by
  constructor
  · intro h
    have hparts := sec_4_1_nu_proved 2 le_rfl lam h
    apply Nat.Partition.ext
    rw [hparts]
    decide
  · rintro rfl
    unfold Shape.InBox Shape.numRows Shape.firstRow
    decide

/-- The other two shapes of 3 are the row and the column. -/
theorem not_inBox_two_iff (lam : Shape 3) : ¬ lam.InBox 2 ↔ lam = shape3 ∨ lam = shape111 := by
  constructor
  · intro h
    have hsum := lam.parts_sum
    rcases shape_three_outside_box lam h with hr | hc
    · left
      unfold Shape.numRows at hr
      apply Nat.Partition.ext
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with h0 | h1
      · rw [Multiset.card_eq_zero] at h0
        rw [h0] at hsum
        simp at hsum
      · obtain ⟨x, hx⟩ := Multiset.card_eq_one.1 h1
        rw [hx] at hsum ⊢
        simp only [Multiset.sum_singleton] at hsum
        rw [hsum]
        rfl
    · right
      unfold Shape.firstRow at hc
      have hall : ∀ p ∈ lam.parts, p = 1 := fun p hp => by
        have h1 := Multiset.le_sup hp
        have h2 := lam.parts_pos hp
        omega
      have hrep := Multiset.eq_replicate.2 ⟨rfl, hall⟩
      rw [hrep, Multiset.sum_replicate, smul_eq_mul, mul_one] at hsum
      apply Nat.Partition.ext
      rw [hrep, hsum]
      decide
  · rintro (rfl | rfl)
    · unfold Shape.InBox Shape.numRows Shape.firstRow
      decide
    · unfold Shape.InBox Shape.numRows Shape.firstRow
      decide

instance : Subsingleton (SYT shape3) :=
  syt_subsingleton_of_row (row_eq_zero_of_numRows_le_one (by unfold Shape.numRows; decide))

instance : Subsingleton (SYT shape111) :=
  syt_subsingleton_of_col (col_eq_zero_of_firstRow_le_one (by unfold Shape.firstRow; decide))

/-! ### The word side: `W_{2,2}` -/

/-- `L(y_1, y_2) = y_1 y_2 + y_2 y_1`. -/
theorem symSum_two {R : Type*} [NonUnitalRing R] (y : Fin 2 → R) : symSum 2 y = y 0 * y 1 + y 1 * y 0 := by
  unfold symSum
  rw [show (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} from by decide,
    Finset.sum_pair (show (1 : Perm (Fin 2)) ≠ swap 0 1 by decide)]
  rfl

/-- For `n = m = 2`, the (F1) triples are `([], (x_i, x_j), [])` with `{i, j} = {0, 1}`. -/
theorem triple_two {a b : List ℕ} {v : Fin 2 → List ℕ} (h : IsMultilinTriple 2 a v b) :
    a = [] ∧ b = [] ∧ ((v 0 = [0] ∧ v 1 = [1]) ∨ (v 0 = [1] ∧ v 1 = [0])) := by
  obtain ⟨hne, hperm⟩ := h
  have hof : List.ofFn v = [v 0, v 1] := rfl
  rw [hof] at hperm
  have hlen := hperm.length_eq
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append, List.length_range] at hlen
  have h0 := List.length_pos_of_ne_nil (hne 0)
  have h1 := List.length_pos_of_ne_nil (hne 1)
  have ha : a = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hb : b = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 (show (v 0).length = 1 by omega)
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 (show (v 1).length = 1 by omega)
  subst ha hb
  have hp : [x, y].Perm (List.range 2) := by simpa [hx, hy] using hperm
  have hxm : x < 2 := List.mem_range.1 (hp.subset (by simp))
  have hym : y < 2 := List.mem_range.1 (hp.subset (by simp))
  have hxy : x ≠ y := by
    have hnd := hp.nodup_iff.2 List.nodup_range
    simpa using hnd
  refine ⟨rfl, rfl, ?_⟩
  rw [hx, hy]
  simp only [List.cons.injEq, and_true]
  omega

/-- `L(x_1, x_2)` in Lean's letters `x_0, x_1`. -/
abbrev L01 : FreeNUAlg F := letter F 0 * letter F 1 + letter F 1 * letter F 0

/-- Every (F1) spanning element for `n = m = 2` is `L(x_1, x_2)`. -/
theorem sandwichElem_two {a b : List ℕ} {v : Fin 2 → List ℕ} (h : IsMultilinTriple 2 a v b) :
    sandwichElem F a v b = L01 (F := F) := by
  obtain ⟨rfl, rfl, hv⟩ := triple_two h
  have hw : ∀ k : ℕ, wordOf F [k] = letter F k := fun k => rfl
  show symSum 2 (fun i => wordOf F (v i)) = _
  rw [symSum_two]
  rcases hv with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [h0, h1, hw, hw]
  · rw [h0, h1, hw, hw, add_comm]

/-- The triple `([], (x_0, x_1), [])`. -/
theorem triple_01 : IsMultilinTriple 2 [] ![[0], [1]] [] :=
  ⟨fun i => by fin_cases i <;> simp, by decide⟩

/-- **Example, (F1)** (v1.10 l. 400): `W_{2,2} = span L(x_1, x_2)`. -/
theorem W22_eq [CharZero F] : multilinIdentities F 2 2 = Submodule.span F {L01 (F := F)} := by
  rw [F1_spanning_proved (F := F) 2 2 (by norm_num)]
  congr 1
  ext p
  constructor
  · rintro ⟨a, v, b, hT, rfl⟩
    exact sandwichElem_two hT
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact ⟨[], ![[0], [1]], [], triple_01, (sandwichElem_two triple_01).symm⟩

theorem L01_ne_zero : L01 (F := F) ≠ 0 := by
  intro h
  have hne : (FreeSemigroup.of 1 * FreeSemigroup.of 0 : FreeSemigroup ℕ) ≠ FreeSemigroup.of 0 * FreeSemigroup.of 1 := by
    decide
  have h1 := congrArg (fun p : FreeNUAlg F => p.coeff (FreeSemigroup.of 0 * FreeSemigroup.of 1)) h
  simp [L01, letter, MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    hne] at h1

/-- **Example** (v1.10 l. 400):`dim W_{2,2} = 1`. -/
theorem finrank_W22 [CharZero F] : Module.finrank F (multilinIdentities F 2 2) = 1 := by
  rw [W22_eq]
  exact finrank_span_singleton L01_ne_zero

/-- **Example** (v1.10 l. 400-401):`x_1 x_2 ∉ T` (as `dim W_{2,2} = 1 < 2 = dim V_2`). -/
theorem not_mem_T [CharZero F] : firstLettersProd F 2 ∉ TIdeal F 2 := by
  intro h
  have hW := (F0_mem_iff_proved F 2 2 (by norm_num)).1 h
  have h1 : Module.finrank F (multilinIdentities F 2 2) = 1 := finrank_W22
  rw [hW, finrank_multilinSpace (F := F) (m := 2) (by norm_num)] at h1
  exact absurd h1 (by decide)

/-! ### The group side: `C_3`, `Φ`, the blocks -/

/-- **Example** (v1.10 l. 401-402):`C_3` is spanned by the 3-cycles `(1 2 3)`, `(1 3 2)` (Lean: `(0 1 2)`, `(0 2 1)`). -/
theorem cycleSpan_three :
    cycleSpan F 3 = Submodule.span F {perm F (finRotate 3), perm F (finRotate 3)⁻¹} := by
  have hfull : IsFullCycle (finRotate 3) := ⟨isCycle_finRotate, support_finRotate⟩
  have hfull' : IsFullCycle (finRotate 3)⁻¹ := ⟨hfull.1.inv, by rw [Perm.support_inv]; exact hfull.2⟩
  have key : ∀ τ : Perm (Fin 3), τ.support = Finset.univ → τ = finRotate 3 ∨ τ = (finRotate 3)⁻¹ := by
    decide
  have hset : {σ : Perm (Fin 3) | IsFullCycle σ} = {finRotate 3, (finRotate 3)⁻¹} := by
    ext σ
    constructor
    · intro hσ
      rcases key σ hσ.2 with h | h <;> simp [h]
    · rintro (rfl | rfl)
      · exact hfull
      · exact hfull'
  unfold cycleSpan
  rw [hset, Set.image_pair]

/-- **Example** (v1.10 l. 402):the two 3-cycles are `Φ(x_1 x_2)` and `Φ(x_2 x_1)`. -/
theorem Phi_two :
    multilinWord F (1 : Perm (Fin 2)) = letter F 0 * letter F 1 ∧ wordCycle (1 : Perm (Fin 2)) = finRotate 3 ∧
      multilinWord F (swap 0 1 : Perm (Fin 2)) = letter F 1 * letter F 0 ∧
      wordCycle (swap 0 1 : Perm (Fin 2)) = (finRotate 3)⁻¹ :=
  ⟨rfl, by decide, rfl, by decide⟩

/-- On a shape with one standard tableau, `ρ_μ((0 1 2)) = ρ_μ((0 2 1)) = 1`. -/
theorem rho_rot_eq_one (Y : YoungSystem F 3) (mu : Shape 3) [Subsingleton (SYT mu)] :
    Y.rho mu (finRotate 3) = 1 ∧ Y.rho mu (finRotate 3)⁻¹ = 1 := by
  have hrot := rhoAlg_rot_sub_eq_zero Y mu
  rw [map_sub, NagataHigman.Proofs.YoungSystem.rhoAlg_perm Y, NagataHigman.Proofs.YoungSystem.rhoAlg_perm Y,
    sub_eq_zero] at hrot
  have hinv : Y.rho mu (finRotate 3) * Y.rho mu (finRotate 3)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [← hrot] at hinv
  have hcube : Y.rho mu (finRotate 3) * Y.rho mu (finRotate 3) * Y.rho mu (finRotate 3) = 1 := by
    rw [← map_mul, ← map_mul, show finRotate 3 * finRotate 3 * finRotate 3 = (1 : Perm (Fin 3)) by decide,
      map_one]
  have hone : Y.rho mu (finRotate 3) = 1 := by
    calc Y.rho mu (finRotate 3)
        = Y.rho mu (finRotate 3) * (Y.rho mu (finRotate 3) * Y.rho mu (finRotate 3)) := by rw [hinv, mul_one]
      _ = 1 := by rw [← mul_assoc, hcube]
  exact ⟨hone, by rw [← hrot]; exact hone⟩

/-- **Example** (v1.10 l. 403-404):on a block with one standard tableau (the row `(3)` and the column `(1^3)`), the
component `e_μ f` of `f = a(1 2 3) + b(1 3 2)` is `(a + b) e_μ`. -/
theorem component_eq [CharZero F] (Y : YoungSystem F 3) (mu : Shape 3) [Subsingleton (SYT mu)] (a b : F) :
    youngIdem F mu * (a • perm F (finRotate 3) + b • perm F (finRotate 3)⁻¹) = (a + b) • youngIdem F mu := by
  obtain ⟨hone, hone'⟩ := rho_rot_eq_one Y mu
  apply NagataHigman.Proofs.YoungSystem.ext_of_rhoAlg Y
  intro lam
  rw [map_mul, map_smul, NagataHigman.Proofs.YoungSystem.rhoAlg_youngIdem Y mu lam]
  by_cases h : lam = mu
  · subst h
    simp [NagataHigman.Proofs.YoungSystem.rhoAlg_perm Y, hone, hone', add_smul]
  · simp [h]

/-- **Example** (v1.10 l. 404):`C_3 ∩ I_(2,1)` is spanned by `(1 2 3) - (1 3 2)`. -/
theorem cycleSpan_inf_block [CharZero F] (Y : YoungSystem F 3) :
    cycleSpan F 3 ⊓ Y.block shape21 = Submodule.span F {perm F (finRotate 3) - perm F (finRotate 3)⁻¹} := by
  have hB : Y.boxSum 2 = Y.block shape21 :=
    boxSum_nu_eq_block 2 le_rfl Y shape21 ((inBox_two_iff shape21).2 rfl)
  apply le_antisymm
  · rintro x ⟨hxC, hxB⟩
    rw [cycleSpan_three] at hxC
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hxC
    have hzero : youngIdem F shape3 * (a • perm F (finRotate 3) + b • perm F (finRotate 3)⁻¹) = 0 := by
      apply NagataHigman.Proofs.YoungSystem.eq_zero_of_forall_rhoAlg Y
      intro lam
      rw [map_mul, NagataHigman.Proofs.YoungSystem.rhoAlg_youngIdem Y shape3 lam]
      by_cases h : lam = shape3
      · subst h
        rw [(NagataHigman.Proofs.YoungSystem.mem_block_iff Y).1 hxB shape3 (by decide), mul_zero]
      · simp [h]
    rw [component_eq Y shape3 a b] at hzero
    have hab : a + b = 0 := by
      by_contra hne
      exact NagataHigman.Proofs.YoungSystem.youngIdem_ne_zero Y shape3 ((smul_eq_zero.1 hzero).resolve_left hne)
    have hb : b = -a := by linear_combination hab
    rw [Submodule.mem_span_singleton]
    exact ⟨a, by rw [hb]; module⟩
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    have h := (rem_4_5_element_of Y).1
    rw [hB] at h
    exact h

/-- **Example** (v1.10 l. 405):`dim(C_3 ∩ B_2^(3)) = 1`, so `m! - dim(C_3 ∩ B_2^(3)) = 2 - 1 = dim W_{2,2}`. -/
theorem finrank_inter [CharZero F] (Y : YoungSystem F 3) :
    Module.finrank F (cycleSpan F 3 ⊓ Y.boxSum 2 : Submodule F (GrpAlg F 3)) = 1 := by
  have hB : Y.boxSum 2 = Y.block shape21 :=
    boxSum_nu_eq_block 2 le_rfl Y shape21 ((inBox_two_iff shape21).2 rfl)
  rw [hB, cycleSpan_inf_block Y]
  exact finrank_span_singleton (rem_4_5_element_of Y).2

/-! ### Step (7): the orthogonal complement -/

theorem wordLin_injective_two : Function.Injective (wordLin F 2) := by
  have hli : LinearIndependent F (multilinWord F (m := 2)) := by
    refine LinearIndependent.of_comp (PropExact.wordCoord F 2) ?_
    have e : (PropExact.wordCoord F 2) ∘ (multilinWord F (m := 2)) = fun w => Pi.single w (1 : F) := by
      funext w
      ext w'
      show (multilinWord F w).coeff (wordMono w') = (Pi.single w (1 : F) : Perm (Fin 2) → F) w'
      rw [PropExact.coeff_multilinWord (by norm_num), Pi.single_apply]
      by_cases h : w = w'
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]
    rw [e]
    exact Pi.linearIndependent_single_one (Perm (Fin 2)) F
  exact hli.fintypeLinearCombination_injective

theorem wordLin_ones : wordLin F 2 (fun _ => 1) = L01 (F := F) := by
  unfold wordLin
  rw [Fintype.linearCombination_apply]
  rw [show (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} from by decide,
    Finset.sum_pair (show (1 : Perm (Fin 2)) ≠ swap 0 1 by decide), one_smul, one_smul]
  rfl

theorem cycleLin_ones : cycleLin F 2 (fun _ => 1) = perm F (finRotate 3) + perm F (finRotate 3)⁻¹ := by
  unfold cycleLin
  rw [Fintype.linearCombination_apply]
  rw [show (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} from by decide,
    Finset.sum_pair (show (1 : Perm (Fin 2)) ≠ swap 0 1 by decide), one_smul, one_smul, (Phi_two (F := F)).2.1,
    (Phi_two (F := F)).2.2.2]

/-- **Example, step (7)** (v1.10 l. 405-406):`Φ(W_{2,2}) = F · ((1 2 3) + (1 3 2))`. -/
theorem Phi_W22 [CharZero F] :
    ((multilinIdentities F 2 2).comap (wordLin F 2)).map (cycleLin F 2) =
      Submodule.span F {perm F (finRotate 3) + perm F (finRotate 3)⁻¹} := by
  rw [W22_eq, ← wordLin_ones, ← Set.image_singleton, ← Submodule.map_span,
    Submodule.comap_map_eq_of_injective wordLin_injective_two, Submodule.map_span, Set.image_singleton,
    cycleLin_ones]

theorem coeffPairing_add_right {N : ℕ} (a b c : GrpAlg F N) :
    coeffPairing F a (b + c) = coeffPairing F a b + coeffPairing F a c := by
  simp only [coeffPairing, MonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem coeffPairing_smul_right {N : ℕ} (a b : GrpAlg F N) (t : F) :
    coeffPairing F a (t • b) = t * coeffPairing F a b := by
  simp only [coeffPairing, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- `⟨a(1 2 3) + b(1 3 2), (1 2 3) + (1 3 2)⟩ = a + b`. -/
theorem pairing_sum (a b : F) :
    coeffPairing F (a • perm F (finRotate 3) + b • perm F (finRotate 3)⁻¹)
      (perm F (finRotate 3) + perm F (finRotate 3)⁻¹) = a + b := by
  have hne : (finRotate 3)⁻¹ ≠ finRotate 3 := by decide
  rw [coeffPairing_add_right, NagataHigman.Proofs.coeffPairing_perm, NagataHigman.Proofs.coeffPairing_perm]
  simp [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, NagataHigman.Proofs.coeff_perm, hne, Ne.symm hne]

/-- **Example, step (7)** (v1.10 l. 405-407):the orthogonal complement of `Φ(W_{2,2})` in `C_3` is
`F · ((1 2 3) - (1 3 2))`. -/
theorem perp_Phi_W22 [CharZero F] :
    {c | c ∈ cycleSpan F 3 ∧
        ∀ x ∈ ((multilinIdentities F 2 2).comap (wordLin F 2)).map (cycleLin F 2), coeffPairing F c x = 0} =
      (Submodule.span F {perm F (finRotate 3) - perm F (finRotate 3)⁻¹} : Set (GrpAlg F 3)) := by
  rw [Phi_W22]
  ext c
  constructor
  · rintro ⟨hc, hperp⟩
    rw [cycleSpan_three] at hc
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hc
    have h := hperp _ (Submodule.mem_span_singleton_self _)
    rw [pairing_sum] at h
    have hb : b = -a := by linear_combination h
    exact Submodule.mem_span_singleton.2 ⟨a, by rw [hb]; module⟩
  · intro hc
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hc
    refine ⟨?_, fun x hx => ?_⟩
    · rw [cycleSpan_three]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp)))
    · obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [coeffPairing_smul_right, show t • (perm F (finRotate 3) - perm F (finRotate 3)⁻¹) =
        t • perm F (finRotate 3) + (-t) • perm F (finRotate 3)⁻¹ by module, pairing_sum]
      ring

end NagataHigman.Proofs.ExV110
