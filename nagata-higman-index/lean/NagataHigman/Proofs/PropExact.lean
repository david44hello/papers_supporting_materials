/-
NagataHigman/Proofs/PropExact.lean — package Q: (F1) spanning set, Proposition 2.1 exact, for any Young system.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.02, lines 173-184 ((F1)),
229-287 (Proposition 2.1 and its proof).
-/
import Mathlib
import NagataHigman.Proofs.WordSide
import NagataHigman.Proofs.BaseChange
import NagataHigman.Proofs.AltIdeal

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv

namespace PropExact

/-! ## 1. The span `G` of all elements `a · L(v_1, …, v_n) · b` (words `v_i` nonempty) is a T-ideal -/

/-- `G`: the span of the elements `a · L(v_1, …, v_n) · b` with nonempty words `v_i` and words `a`, `b`
(possibly empty) — paper (F1), line 223: "spanned by the elements `p · L(h_1, …, h_n) · q`". -/
def sandwichSpan (F : Type*) [Field F] (n : ℕ) : Submodule F (FreeNUAlg F) :=
  Submodule.span F {p | ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ), (∀ i, v i ≠ []) ∧ p = sandwichElem F a v b}

/-- The letters of a monomial. -/
def lettersOf (μ : FreeSemigroup ℕ) : List ℕ := μ.head :: μ.tail

theorem lettersOf_ne_nil (μ : FreeSemigroup ℕ) : lettersOf μ ≠ [] := by simp [lettersOf]

theorem monoOf_lettersOf (μ : FreeSemigroup ℕ) : monoOf (lettersOf μ) = μ := by
  cases μ
  rfl

variable {F : Type*} [Field F]

theorem single_eq_wordOf (μ : FreeSemigroup ℕ) :
    (MonoidAlgebra.single μ (1 : F) : FreeNUAlg F) = wordOf F (lettersOf μ) := by
  rw [Arcs.wordOf_eq F (lettersOf_ne_nil μ), monoOf_lettersOf]

theorem wordOf_append {l₁ l₂ : List ℕ} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    wordOf F (l₁ ++ l₂) = wordOf F l₁ * wordOf F l₂ := by
  rw [Arcs.wordOf_eq F (by simp [h₁]), Arcs.wordOf_eq F h₁, Arcs.wordOf_eq F h₂, MonoidAlgebra.single_mul_single,
    mul_one, Arcs.monoOf_append h₁ h₂]

theorem wordOf_mul_sandwichElem {n : ℕ} {l : List ℕ} (hl : l ≠ []) (a b : List ℕ) (v : Fin n → List ℕ) :
    wordOf F l * sandwichElem F a v b = sandwichElem F (l ++ a) v b := by
  have hla : l ++ a ≠ [] := by simp [hl]
  unfold sandwichElem sandwich
  dsimp only
  by_cases hb : b = []
  · rw [ite_eq_left hb, ite_eq_left hb, ite_eq_right hla]
    by_cases ha : a = []
    · rw [ite_eq_left ha, ha, List.append_nil]
    · rw [ite_eq_right ha, ← mul_assoc, ← wordOf_append hl ha]
  · rw [ite_eq_right hb, ite_eq_right hb, ite_eq_right hla]
    by_cases ha : a = []
    · rw [ite_eq_left ha, ha, List.append_nil, mul_assoc]
    · rw [ite_eq_right ha, ← mul_assoc, ← mul_assoc, ← wordOf_append hl ha]

theorem sandwichElem_mul_wordOf {n : ℕ} {l : List ℕ} (hl : l ≠ []) (a b : List ℕ) (v : Fin n → List ℕ) :
    sandwichElem F a v b * wordOf F l = sandwichElem F a v (b ++ l) := by
  have hbl : b ++ l ≠ [] := by simp [hl]
  unfold sandwichElem sandwich
  dsimp only
  rw [ite_eq_right hbl]
  by_cases hb : b = []
  · rw [ite_eq_left hb, hb, List.nil_append]
  · rw [ite_eq_right hb, mul_assoc, ← wordOf_append hb hl]

theorem mul_mem_sandwichSpan {n : ℕ} (r : FreeNUAlg F) {g : FreeNUAlg F} (hg : g ∈ sandwichSpan F n) :
    r * g ∈ sandwichSpan F n := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, v, b, hv, rfl⟩ := hx
    rw [eq_sum_smul_single r r.coeff.support subset_rfl, Finset.sum_mul]
    refine Submodule.sum_mem _ (fun μ _ => ?_)
    rw [smul_mul_assoc, single_eq_wordOf, wordOf_mul_sandwichElem (lettersOf_ne_nil _)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, v, b, hv, rfl⟩)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

theorem mem_sandwichSpan_mul {n : ℕ} (r : FreeNUAlg F) {g : FreeNUAlg F} (hg : g ∈ sandwichSpan F n) :
    g * r ∈ sandwichSpan F n := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, v, b, hv, rfl⟩ := hx
    rw [eq_sum_smul_single r r.coeff.support subset_rfl, Finset.mul_sum]
    refine Submodule.sum_mem _ (fun μ _ => ?_)
    rw [mul_smul_comm, single_eq_wordOf, sandwichElem_mul_wordOf (lettersOf_ne_nil _)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, v, _, hv, rfl⟩)
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- `L` of single words is an element of `G`. -/
theorem symSum_singles_mem {n : ℕ} (w : Fin n → FreeSemigroup ℕ) :
    symSum n (fun i => MonoidAlgebra.single (w i) (1 : F)) ∈ sandwichSpan F n := by
  refine Submodule.subset_span ⟨[], fun i => lettersOf (w i), [], fun i => lettersOf_ne_nil _, ?_⟩
  unfold sandwichElem sandwich
  dsimp only
  rw [ite_eq_left rfl, ite_eq_left rfl]
  simp only [single_eq_wordOf]

/-- `L(y_1, …, y_n) ∈ G` for all `y_i` (multilinearity). -/
theorem symSum_mem_sandwichSpan {n : ℕ} (y : Fin n → FreeNUAlg F) : symSum n y ∈ sandwichSpan F n :=
  symSum_mem_of_words _ symSum_singles_mem y

theorem map_mem_sandwichSpan {n : ℕ} (φ : FreeNUAlg F →ₙₐ[F] FreeNUAlg F) {g : FreeNUAlg F}
    (hg : g ∈ sandwichSpan F n) : φ g ∈ sandwichSpan F n := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, v, b, hv, rfl⟩ := hx
    have hX : φ (symSum n (fun i => wordOf F (v i))) ∈ sandwichSpan F n := by
      rw [map_symSum]
      exact symSum_mem_sandwichSpan _
    unfold sandwichElem sandwich
    dsimp only
    split_ifs
    · exact hX
    · rw [map_mul]
      exact mul_mem_sandwichSpan _ hX
    · rw [map_mul]
      exact mem_sandwichSpan_mul _ hX
    · rw [map_mul, map_mul]
      exact mem_sandwichSpan_mul _ (mul_mem_sandwichSpan _ hX)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem isTIdeal_sandwichSpan (n : ℕ) : IsTIdeal F (sandwichSpan F n) where
  mul_left r _ ha := mul_mem_sandwichSpan r ha
  mul_right r _ ha := mem_sandwichSpan_mul r ha
  endo φ _ ha := map_mem_sandwichSpan φ ha

/-- In characteristic `0`, `T ⊆ G` (paper (F1): `T = (L)^T` is spanned by the `p · L(h) · q`). -/
theorem TIdeal_le_sandwichSpan [CharZero F] (n : ℕ) (hn : 1 ≤ n) : TIdeal F n ≤ sandwichSpan F n := by
  rw [F1_TIdeal_eq_proved F n hn]
  refine sInf_le ⟨isTIdeal_sandwichSpan n, ?_⟩
  have e : (fun i : Fin n => letter F (i : ℕ)) =
      fun i : Fin n => MonoidAlgebra.single (FreeSemigroup.of (i : ℕ)) (1 : F) := rfl
  rw [e]
  exact symSum_singles_mem _

/-! ## 2. The coordinate projection onto `V_m` -/

/-- The coordinate projection onto `V_m`: keep the multilinear words in `x_0, …, x_{m-1}`. -/
def projV (F : Type*) [Field F] (m : ℕ) : FreeNUAlg F →ₗ[F] FreeNUAlg F where
  toFun p := ∑ w : Perm (Fin m), p.coeff (wordMono w) • multilinWord F w
  map_add' x y := by
    simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

theorem projV_of_mem {m : ℕ} (hm : 1 ≤ m) {p : FreeNUAlg F} (hp : p ∈ multilinSpace F m) :
    projV F m p = p :=
  (WordSide.eq_sum_coeff_multilinWord hm hp).symm

/-- A non-multilinear `a · L(v) · b` has no multilinear word: its projection to `V_m` is `0`. -/
theorem projV_sandwichElem_of_not {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (a b : List ℕ) (v : Fin n → List ℕ)
    (hv : ∀ i, v i ≠ []) (hnot : ¬ IsMultilinTriple m a v b) : projV F m (sandwichElem F a v b) = 0 := by
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [Arcs.coeff_sandwichElem F hn hm a b v hv w, Finset.sum_eq_zero, zero_smul]
  intro π _
  refine ite_eq_right (fun h => hnot ⟨hv, ?_⟩)
  have hp : (a ++ (List.ofFn v).flatten ++ b).Perm (a ++ (List.ofFn (v ∘ π)).flatten ++ b) :=
    (((π.ofFn_comp_perm v).flatten.symm).append_left a).append_right b
  rw [h] at hp
  exact hp.trans (Arcs.wordList_perm_range w)

end PropExact

open PropExact

variable {F : Type*} [Field F]

/-- **Q1, (F1) spanning set** (paper v1.02 lines 175-184): in characteristic `0`, `W_{n,m} = V_m ∩ T` is spanned by the
multilinear elements `a · L(v_1, …, v_n) · b`. -/
theorem F1_spanning_proved [CharZero F] (n m : ℕ) (hn : 1 ≤ n) :
    multilinIdentities F n m =
      Submodule.span F {p | ∃ (a : List ℕ) (v : Fin n → List ℕ) (b : List ℕ),
        IsMultilinTriple m a v b ∧ p = sandwichElem F a v b} := by
  apply le_antisymm
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- `V_0 = 0`
      intro p hp
      have hV : multilinSpace F 0 = ⊥ := by
        refine (Submodule.span_eq_bot).mpr ?_
        rintro x ⟨w, rfl⟩
        rfl
      have := (Submodule.mem_inf.mp hp).1
      rw [hV, Submodule.mem_bot] at this
      rw [this]
      exact Submodule.zero_mem _
    · intro p hp
      obtain ⟨hpV, hpT⟩ := Submodule.mem_inf.mp hp
      rw [← projV_of_mem hm hpV]
      have hpG := TIdeal_le_sandwichSpan n hn hpT
      clear hp hpV hpT
      induction hpG using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, v, b, hv, rfl⟩ := hx
        by_cases htr : IsMultilinTriple m a v b
        · rw [projV_of_mem hm (sandwichElem_mem_multilinSpace F hm a v b htr)]
          exact Submodule.subset_span ⟨a, v, b, htr, rfl⟩
        · rw [projV_sandwichElem_of_not hn hm a b v hv htr]
          exact Submodule.zero_mem _
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · refine Submodule.span_le.mpr ?_
    rintro p ⟨a, v, b, htr, rfl⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exfalso
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (htr.1 ⟨0, hn⟩)
      have hmem : x ∈ a ++ (List.ofFn v).flatten ++ b :=
        List.mem_append_left _ (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨⟨0, hn⟩, rfl⟩, hx⟩))
      simpa using htr.2.mem_iff.mp hmem
    · exact Submodule.mem_inf.mpr ⟨sandwichElem_mem_multilinSpace F hm a v b htr, sandwichElem_mem_TIdeal F n hn a v b⟩

/-! ## 3. Coordinates on words and on `N`-cycles; the dot product -/

namespace PropExact

/-- Coordinates on the multilinear words: `p ↦ (p(x_w))_w`. -/
def wordCoord (F : Type*) [Field F] (m : ℕ) : FreeNUAlg F →ₗ[F] (Perm (Fin m) → F) where
  toFun p := fun w => p.coeff (wordMono w)
  map_add' x y := by
    ext w
    simp [MonoidAlgebra.coeff_add]
  map_smul' c x := by
    ext w
    simp [MonoidAlgebra.coeff_smul]

/-- Coordinates on the `N`-cycles: `c ↦ (c(Φ w))_w`. -/
def cycCoord (F : Type*) [Field F] (m : ℕ) : GrpAlg F (m + 1) →ₗ[F] (Perm (Fin m) → F) where
  toFun c := fun w => c.coeff (wordCycle w)
  map_add' x y := by
    ext w
    simp [MonoidAlgebra.coeff_add]
  map_smul' c x := by
    ext w
    simp [MonoidAlgebra.coeff_smul]

/-- The dot product on `F^{S_m}` (the `N`-cycles are orthonormal for `⟨ , ⟩`). -/
def dotForm (k : Type*) [Fintype k] (F : Type*) [Field F] : LinearMap.BilinForm F (k → F) :=
  LinearMap.mk₂ F (fun x y => ∑ i, x i * y i)
    (fun x x' y => by simp [add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_assoc])
    (fun x y y' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [Finset.mul_sum, mul_left_comm])

theorem dotForm_apply {k : Type*} [Fintype k] (x y : k → F) : dotForm k F x y = ∑ i, x i * y i := rfl

theorem dotForm_ker {k : Type*} [Fintype k] [DecidableEq k] : LinearMap.ker (dotForm k F) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext i
  have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) (Pi.single i 1)
  simpa [dotForm_apply, Pi.single_apply] using h

/-- A multilinear `p` is `Σ_w p(x_w) x_w`; so `wordCoord` is injective on `V_m`. -/
theorem wordCoord_injOn {m : ℕ} (hm : 1 ≤ m) {p q : FreeNUAlg F} (hp : p ∈ multilinSpace F m)
    (hq : q ∈ multilinSpace F m) (h : wordCoord F m p = wordCoord F m q) : p = q := by
  rw [WordSide.eq_sum_coeff_multilinWord hm hp, WordSide.eq_sum_coeff_multilinWord hm hq]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [show p.coeff (wordMono w) = q.coeff (wordMono w) from congrFun h w]

theorem coeff_multilinWord {m : ℕ} (hm : 1 ≤ m) (w w' : Perm (Fin m)) :
    (multilinWord F w).coeff (wordMono w') = if w = w' then 1 else 0 := by
  rw [multilinWord_eq_single F hm, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : w = w'
  · rw [ite_eq_left (congrArg wordMono h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (WordSide.wordMono_injective hm h')), ite_eq_right h]

theorem coeff_perm_wordCycle {m : ℕ} (w w' : Perm (Fin m)) :
    (perm F (wordCycle w)).coeff (wordCycle w') = if w = w' then 1 else 0 := by
  rw [perm, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : w = w'
  · rw [ite_eq_left (congrArg wordCycle h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (wordCycle_injective h')), ite_eq_right h]

/-- Every `c ∈ C_N` is `Σ_w c(Φ w) Φ(w)`. -/
theorem eq_sum_of_mem_cycleSpan {m : ℕ} {c : GrpAlg F (m + 1)} (hc : c ∈ cycleSpan F (m + 1)) :
    c = ∑ w : Perm (Fin m), c.coeff (wordCycle w) • perm F (wordCycle w) := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨σ, hσ, rfl⟩ := hx
    obtain ⟨w₀, rfl⟩ := exists_wordCycle_eq hσ
    rw [Finset.sum_eq_single w₀]
    · rw [coeff_perm_wordCycle, ite_eq_left rfl, one_smul]
    · intro w _ hw
      rw [coeff_perm_wordCycle, ite_eq_right (fun h => hw h.symm), zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_smul]
  | smul r x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, mul_smul]

theorem cycCoord_injOn {m : ℕ} {c d : GrpAlg F (m + 1)} (hc : c ∈ cycleSpan F (m + 1))
    (hd : d ∈ cycleSpan F (m + 1)) (h : cycCoord F m c = cycCoord F m d) : c = d := by
  rw [eq_sum_of_mem_cycleSpan hc, eq_sum_of_mem_cycleSpan hd]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [show c.coeff (wordCycle w) = d.coeff (wordCycle w) from congrFun h w]

/-- The element `Σ_w x_w Φ(w)` of `C_N` with prescribed coordinates. -/
theorem cycCoord_sum (m : ℕ) (x : Perm (Fin m) → F) :
    cycCoord F m (∑ w : Perm (Fin m), x w • perm F (wordCycle w)) = x := by
  ext w'
  show (∑ w : Perm (Fin m), x w • perm F (wordCycle w)).coeff (wordCycle w') = x w'
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single w']
  · rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_perm_wordCycle, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro w _ hw
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_perm_wordCycle, ite_eq_right hw, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_mem_cycleSpan (m : ℕ) (x : Perm (Fin m) → F) (hm : 1 ≤ m) :
    ∑ w : Perm (Fin m), x w • perm F (wordCycle w) ∈ cycleSpan F (m + 1) :=
  Submodule.sum_mem _ (fun w _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨wordCycle w, wordCycle_isFullCycle hm w, rfl⟩))

/-- For `c ∈ C_N`: `⟨c, a⟩ = Σ_w c(Φ w) a(Φ w)`. -/
theorem coeffPairing_of_mem_cycleSpan {m : ℕ} {c : GrpAlg F (m + 1)} (hc : c ∈ cycleSpan F (m + 1))
    (a : GrpAlg F (m + 1)) :
    coeffPairing F c a = ∑ w : Perm (Fin m), c.coeff (wordCycle w) * a.coeff (wordCycle w) := by
  have e := eq_sum_of_mem_cycleSpan hc
  calc coeffPairing F c a
      = ∑ σ : Perm (Fin (m + 1)), (∑ w : Perm (Fin m), c.coeff (wordCycle w) •
          perm F (wordCycle w)).coeff σ * a.coeff σ := by
        unfold coeffPairing
        rw [← e]
    _ = ∑ w : Perm (Fin m), c.coeff (wordCycle w) * a.coeff (wordCycle w) := by
        simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_smul,
          Finsupp.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        simp only [perm, MonoidAlgebra.coeff_single, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
          ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp

/-- Disjoint block sums are orthogonal (paper (F3)). -/
theorem coeffPairing_eq_zero_of_blockSum {N : ℕ} (Y : YoungSystem F N) {S S' : Set (Shape N)}
    (hdisj : ∀ mu, mu ∈ S → mu ∉ S') {a b : GrpAlg F N} (ha : a ∈ Y.blockSum S) (hb : b ∈ Y.blockSum S') :
    coeffPairing F a b = 0 := by
  rw [YoungSystem.coeffPairing_eq_sum Y]
  refine Finset.sum_eq_zero (fun mu _ => ?_)
  by_cases hmu : mu ∈ S
  · rw [(YoungSystem.mem_blockSum_iff Y).mp hb mu (hdisj mu hmu), Matrix.mul_zero, Matrix.trace_zero, mul_zero]
  · rw [(YoungSystem.phiMat_eq_zero_iff Y mu a).mpr ((YoungSystem.mem_blockSum_iff Y).mp ha mu hmu),
      Matrix.zero_mul, Matrix.trace_zero, mul_zero]

theorem boxSum_le_rowSum {N : ℕ} (Y : YoungSystem F N) (n : ℕ) : Y.boxSum n ≤ Y.rowSum n := by
  rw [← YoungSystem.rowSum_inf_colSum Y n]
  exact inf_le_left

theorem numRows_le {N : ℕ} (lam : Shape N) : lam.numRows ≤ N := by
  unfold Shape.numRows
  calc Multiset.card lam.parts = (lam.parts.map (fun _ => 1)).sum := by simp
    _ ≤ (lam.parts.map id).sum := Multiset.sum_map_le_sum_map _ _ (fun p hp => lam.parts_pos hp)
    _ = N := by simp [lam.parts_sum]

theorem firstRow_le {N : ℕ} (lam : Shape N) : lam.firstRow ≤ N := by
  unfold Shape.firstRow
  refine Multiset.sup_le.mpr (fun p hp => ?_)
  rw [← lam.parts_sum]
  exact Multiset.le_sum_of_mem hp

/-- If `N ≤ n`, every shape of `N` fits in the box, so `B_n = F[S_N]`. -/
theorem boxSum_eq_top {N : ℕ} (Y : YoungSystem F N) {n : ℕ} (h : N ≤ n) : Y.boxSum n = ⊤ := by
  rw [eq_top_iff]
  intro a _
  refine (YoungSystem.mem_blockSum_iff Y).mpr (fun mu hmu => absurd ⟨?_, ?_⟩ hmu)
  · exact (numRows_le mu).trans h
  · exact (firstRow_le mu).trans h

/-- A multilinear triple with `n` nonempty blocks needs `n ≤ m` letters. -/
theorem le_of_isMultilinTriple {n m : ℕ} {a b : List ℕ} {v : Fin n → List ℕ} (h : IsMultilinTriple m a v b) :
    n ≤ m := by
  have hlen := h.2.length_eq
  simp only [List.length_append, List.length_range] at hlen
  have hfl : n ≤ (List.ofFn v).flatten.length := by
    rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
    calc n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i : Fin n, (v i).length :=
        Finset.sum_le_sum (fun i _ => List.length_pos_of_ne_nil (h.1 i))
  omega

/-- The functional `p ↦ Σ_w y_w p(x_w)` on `F⟨X⟩`. -/
def dotFunctional (m : ℕ) (y : Perm (Fin m) → F) : FreeNUAlg F →ₗ[F] F where
  toFun p := ∑ w, y w * p.coeff (wordMono w)
  map_add' p q := by simp [MonoidAlgebra.coeff_add, mul_add, Finset.sum_add_distrib]
  map_smul' c p := by simp [MonoidAlgebra.coeff_smul, Finset.mul_sum, mul_left_comm]

theorem dotFunctional_multilinWord {m : ℕ} (hm : 1 ≤ m) (y : Perm (Fin m) → F) (w : Perm (Fin m)) :
    dotFunctional m y (multilinWord F w) = y w := by
  show ∑ w', y w' * (multilinWord F w).coeff (wordMono w') = y w
  rw [Finset.sum_eq_single w]
  · rw [coeff_multilinWord hm, ite_eq_left rfl, mul_one]
  · intro w' _ hw'
    rw [coeff_multilinWord hm, ite_eq_right (fun h => hw' h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end PropExact

/-! ## 4. Proposition 2.1, exact, for any Young system -/

section Exact

variable [CharZero F]

open PropExact in
/-- The `N`-cycle coordinates of `C_N ∩ B_n` are exactly the vectors orthogonal to the word coordinates of
`W_{n,m}` (paper, steps (6)-(7)). -/
theorem cycCoord_range_eq_orthogonal (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (Y : YoungSystem F (m + 1)) :
    LinearMap.range ((cycCoord F m).comp (cycleSpan F (m + 1) ⊓ Y.boxSum n).subtype) =
      (dotForm (Perm (Fin m)) F).orthogonal
        (LinearMap.range ((wordCoord F m).comp (multilinIdentities F n m).subtype)) := by
  rcases lt_or_ge m n with hmn | hnm
  · -- `m < n`: `W = 0` and `B_n = F[S_N]`
    have hW : multilinIdentities F n m = ⊥ := by
      rw [F1_spanning_proved n m hn, Submodule.span_eq_bot]
      rintro p ⟨a, v, b, htr, rfl⟩
      exact absurd (le_of_isMultilinTriple htr) (by omega)
    have hB : Y.boxSum n = ⊤ := boxSum_eq_top Y (by omega)
    ext y
    constructor
    · intro _
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      rintro u ⟨⟨p, hp⟩, rfl⟩
      rw [hW, Submodule.mem_bot] at hp
      simp [hp]
    · intro _
      refine ⟨⟨∑ w, y w • perm F (wordCycle w), ?_⟩, ?_⟩
      · rw [hB, inf_top_eq]
        exact sum_mem_cycleSpan m y hm
      · exact cycCoord_sum m y
  · ext y
    constructor
    · -- `⊆`: a `c ∈ C_N ∩ B_n` is orthogonal to `Φ(W)`
      rintro ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨hcC, hcB⟩ := Submodule.mem_inf.mp hc
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      rintro u ⟨⟨p, hp⟩, rfl⟩
      show ∑ w, p.coeff (wordMono w) * c.coeff (wordCycle w) = 0
      -- the functional `p ↦ Σ_w p(x_w) c(Φ w)` vanishes on the spanning set of (F1)
      rw [F1_spanning_proved n m hn] at hp
      induction hp using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, v, b, htr, rfl⟩ := hx
        obtain ⟨τ, X, hX, hco⟩ := converse_block_lemma F hn hnm a v b htr
        have hτE : perm F τ * altSum F X ∈ Y.blockSum {lam | n + 1 ≤ lam.numRows} := by
          rw [← YoungSystem.altIdeal_eq_blockSum Y n (by omega), altIdeal_eq_span F (by omega)]
          exact Submodule.subset_span ⟨τ, X, hX, rfl⟩
        have hzero := coeffPairing_eq_zero_of_blockSum Y (S := {lam | lam.numRows ≤ n})
          (S' := {lam | n + 1 ≤ lam.numRows}) (fun mu h1 h2 => by simp only [Set.mem_ofPred_eq] at h1 h2; omega)
          (boxSum_le_rowSum Y n hcB) hτE
        rw [coeffPairing_of_mem_cycleSpan hcC] at hzero
        rw [← hzero]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [← hco w, mul_comm]
      | zero => simp
      | add x z _ _ hx hz =>
        simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib, hx, hz, add_zero]
      | smul r x _ hx =>
        simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx,
          mul_zero]
    · -- `⊇`: a vector orthogonal to `Φ(W)` is the coordinate vector of some `c ∈ C_N ∩ B_n`
      intro hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
      have hφ : ∀ p ∈ multilinIdentities F n m, dotFunctional m y p = 0 := by
        intro p hp
        have := hy (wordCoord F m p) ⟨⟨p, hp⟩, rfl⟩
        rw [dotForm_apply] at this
        rw [← this]
        show ∑ w, y w * p.coeff (wordMono w) = ∑ w, p.coeff (wordMono w) * y w
        exact Finset.sum_congr rfl (fun w _ => mul_comm _ _)
      have hC := cycleElem_mem_cycleSpan m hm (dotFunctional m y)
      have hperp := cycleElem_perp_altIdeal n m hn hnm (dotFunctional m y) hφ
      have hA : cycleElem F m (dotFunctional m y) ∈ Y.rowSum n :=
        YoungSystem.mem_rowSum_of_perp_altIdeal Y n (by omega) _ hperp
      have hB : cycleElem F m (dotFunctional m y) ∈ Y.boxSum n :=
        YoungSystem.cycleSpan_inf_rowSum_le_boxSum Y n (Submodule.mem_inf.mpr ⟨hC, hA⟩)
      refine ⟨⟨cycleElem F m (dotFunctional m y), Submodule.mem_inf.mpr ⟨hC, hB⟩⟩, ?_⟩
      ext w
      show (cycleElem F m (dotFunctional m y)).coeff (wordCycle w) = y w
      rw [coeff_cycleElem, dotFunctional_multilinWord hm]

open PropExact in
/-- **Q2, Proposition 2.1** (lines 280-286), for an arbitrary Young system `Y` of `S_{m+1}` over `F`:
`dim W_{n,m} + dim (C_N ∩ B_n) = m!` (both `m ≥ n` and, trivially, `1 ≤ m < n`). -/
theorem prop_2_1_general (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (Y : YoungSystem F (m + 1)) :
    Module.finrank F (multilinIdentities F n m) +
      Module.finrank F (cycleSpan F (m + 1) ⊓ Y.boxSum n : Submodule F (GrpAlg F (m + 1))) = m.factorial := by
  classical
  have hU : Module.finrank F (LinearMap.range ((wordCoord F m).comp (multilinIdentities F n m).subtype)) =
      Module.finrank F (multilinIdentities F n m) := by
    refine LinearMap.finrank_range_of_inj (fun p q h => Subtype.ext ?_)
    exact wordCoord_injOn hm (Submodule.mem_inf.mp p.2).1 (Submodule.mem_inf.mp q.2).1 h
  have hK : Module.finrank F (LinearMap.range ((cycCoord F m).comp
      (cycleSpan F (m + 1) ⊓ Y.boxSum n).subtype)) =
      Module.finrank F (cycleSpan F (m + 1) ⊓ Y.boxSum n : Submodule F (GrpAlg F (m + 1))) := by
    refine LinearMap.finrank_range_of_inj (fun c d h => Subtype.ext ?_)
    exact cycCoord_injOn (Submodule.mem_inf.mp c.2).1 (Submodule.mem_inf.mp d.2).1 h
  rw [← hU, ← hK, cycCoord_range_eq_orthogonal n m hn hm Y,
    LinearMap.BilinForm.finrank_add_finrank_orthogonal', dotForm_ker, inf_bot_eq, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, Fintype.card_perm, Fintype.card_fin]

omit [CharZero F] in
open PropExact in
theorem finrank_multilinSpace {m : ℕ} (hm : 1 ≤ m) : Module.finrank F (multilinSpace F m) = m.factorial := by
  have hli : LinearIndependent F (multilinWord F (m := m)) := by
    refine LinearIndependent.of_comp (wordCoord F m) ?_
    have e : (wordCoord F m) ∘ (multilinWord F (m := m)) = fun w => Pi.single w (1 : F) := by
      funext w
      ext w'
      show (multilinWord F w).coeff (wordMono w') = (Pi.single w (1 : F) : Perm (Fin m) → F) w'
      rw [coeff_multilinWord hm, Pi.single_apply]
      by_cases h : w = w'
      · rw [ite_eq_left h, ite_eq_left h.symm]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]
    rw [e]
    exact Pi.linearIndependent_single_one (Perm (Fin m)) F
  unfold multilinSpace
  rw [finrank_span_eq_card hli, Fintype.card_perm, Fintype.card_fin]

/-- **Q2, Proposition 2.1, "in particular"** (line 285): `x_1 ⋯ x_m ∈ T` iff `C_N ∩ B_n = 0`, for any Young system. -/
theorem prop_2_1_iff_general (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (Y : YoungSystem F (m + 1)) :
    firstLettersProd F m ∈ TIdeal F n ↔ cycleSpan F (m + 1) ⊓ Y.boxSum n = ⊥ := by
  have hdim := prop_2_1_general n m hn hm Y
  rw [F0_mem_iff_proved F n m hm, ← Submodule.finrank_eq_zero]
  have hle : multilinIdentities F n m ≤ multilinSpace F m := inf_le_left
  have : FiniteDimensional F (multilinSpace F m) := FiniteDimensional.span_of_finite F (Set.finite_range _)
  constructor
  · intro h
    rw [h, finrank_multilinSpace hm] at hdim
    omega
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [finrank_multilinSpace hm]
    omega

end Exact

end NagataHigman.Proofs

end
