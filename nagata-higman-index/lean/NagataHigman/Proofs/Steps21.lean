/-
NagataHigman/Proofs/Steps21.lean — package S: the named steps (1), (2), (6), (7) of the proof of Proposition 2.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.02, lines 248-287.
`Φ = cycleLin ∘ wordLin⁻¹` and `P = cycleProj` are defined in NagataHigman/Defs/WordCycle.lean.
-/
import Mathlib
import NagataHigman.Proofs.PropExact

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv PropExact

namespace Steps21

variable {F : Type*} [Field F]

theorem wordLin_apply (m : ℕ) (c : Perm (Fin m) → F) : wordLin F m c = ∑ w, c w • multilinWord F w := by
  simp [wordLin, Fintype.linearCombination_apply]

theorem cycleLin_apply (m : ℕ) (c : Perm (Fin m) → F) :
    cycleLin F m c = ∑ w, c w • perm F (wordCycle w) := by
  simp [cycleLin, Fintype.linearCombination_apply]

/-- The word coordinates of `Σ_w c_w x_w` are `c`. -/
theorem wordCoord_wordLin {m : ℕ} (hm : 1 ≤ m) (c : Perm (Fin m) → F) : wordCoord F m (wordLin F m c) = c := by
  ext w'
  show (wordLin F m c).coeff (wordMono w') = c w'
  rw [wordLin_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single w']
  · rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_multilinWord hm, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro w _ hw
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_multilinWord hm, ite_eq_right hw, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem wordLin_wordCoord {m : ℕ} (hm : 1 ≤ m) {p : FreeNUAlg F} (hp : p ∈ multilinSpace F m) :
    wordLin F m (wordCoord F m p) = p := by
  rw [wordLin_apply]
  exact (WordSide.eq_sum_coeff_multilinWord hm hp).symm

theorem cycCoord_cycleLin (m : ℕ) (c : Perm (Fin m) → F) : cycCoord F m (cycleLin F m c) = c := by
  rw [cycleLin_apply]
  exact cycCoord_sum m c

theorem cycleLin_cycCoord {m : ℕ} {c : GrpAlg F (m + 1)} (hc : c ∈ cycleSpan F (m + 1)) :
    cycleLin F m (cycCoord F m c) = c := by
  rw [cycleLin_apply]
  exact (eq_sum_of_mem_cycleSpan hc).symm

/-- `P(a) = Σ_w a(Φ w) Φ(w)`: the projection onto `C_N` in the word coordinates. -/
theorem cycleProj_eq {m : ℕ} (hm : 1 ≤ m) (a : GrpAlg F (m + 1)) :
    cycleProj F (m + 1) a = cycleLin F m (cycCoord F m a) := by
  classical
  have himg : Finset.univ.filter (fun σ : Perm (Fin (m + 1)) => IsFullCycle σ) =
      Finset.univ.image (wordCycle (m := m)) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun h => exists_wordCycle_eq h, fun ⟨w, hw⟩ => hw ▸ wordCycle_isFullCycle hm w⟩
  show ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin (m + 1)) => IsFullCycle σ), a.coeff σ • perm F σ = _
  rw [himg, Finset.sum_image (fun w _ w' _ h => wordCycle_injective h), cycleLin_apply]
  rfl

end Steps21

open Steps21

variable {F : Type*} [Field F]

/-- **Step (1)** (line 297), first half: `Φ` is a bijection from the multilinear words onto the `N`-cycles. -/
theorem prop21_step1_words (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (wordCycle (m := m)) ∧
      ∀ σ : Perm (Fin (m + 1)), IsFullCycle σ ↔ ∃ w : Perm (Fin m), wordCycle w = σ :=
  ⟨wordCycle_injective, fun _ => ⟨exists_wordCycle_eq, fun ⟨w, hw⟩ => hw ▸ wordCycle_isFullCycle hm w⟩⟩

/-- **Step (1)** (line 298), second half, in coordinates: the multilinear words are a basis of `V_m` and the `N`-cycles
are a basis of `C_N`; so `Φ = cycleLin ∘ wordLin⁻¹ : V_m → C_N` is a linear isomorphism. -/
theorem prop21_step1_linear (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (wordLin F m) ∧ LinearMap.range (wordLin F m) = multilinSpace F m ∧
      Function.Injective (cycleLin F m) ∧ LinearMap.range (cycleLin F m) = cycleSpan F (m + 1) := by
  refine ⟨(Function.LeftInverse.injective (wordCoord_wordLin hm)), ?_,
    (Function.LeftInverse.injective (cycCoord_cycleLin m)), ?_⟩
  · rw [wordLin, Fintype.range_linearCombination]
    rfl
  · rw [cycleLin, Fintype.range_linearCombination]
    unfold cycleSpan
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨wordCycle w, wordCycle_isFullCycle hm w, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      obtain ⟨w, rfl⟩ := exists_wordCycle_eq hσ
      exact ⟨w, rfl⟩

/-- **Step (1)** (line 298), as the paper words it: a linear isomorphism `Φ : V_m → C_N` with `Φ(x_w) = Φ(w)`. -/
theorem prop21_step1_iso (m : ℕ) (hm : 1 ≤ m) :
    ∃ Φ : multilinSpace F m ≃ₗ[F] cycleSpan F (m + 1), ∀ w : Perm (Fin m),
      (Φ ⟨multilinWord F w, Submodule.subset_span ⟨w, rfl⟩⟩ : GrpAlg F (m + 1)) = perm F (wordCycle w) := by
  classical
  obtain ⟨hWi, hWr, hCi, hCr⟩ := prop21_step1_linear (F := F) m hm
  let eW := (LinearEquiv.ofEq _ _ hWr.symm).trans (LinearEquiv.ofInjective _ hWi).symm
  let eC := (LinearEquiv.ofInjective _ hCi).trans (LinearEquiv.ofEq _ _ hCr)
  refine ⟨eW.trans eC, fun w => ?_⟩
  have hw : eW ⟨multilinWord F w, Submodule.subset_span ⟨w, rfl⟩⟩ = Pi.single w 1 := by
    apply (LinearEquiv.ofInjective _ hWi).injective
    simp only [eW, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    ext1
    simp only [LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]
    rw [wordLin_apply, Finset.sum_eq_single w]
    · simp
    · intro w' _ hw'
      simp [hw']
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [LinearEquiv.trans_apply, hw, eC, LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply]
  rw [cycleLin_apply, Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp [hw']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Step (6), forward half** (lines 323-337; used by Theorems A and B, Remark 2.2): `P(I) ⊆ Φ(W_{n,m})`. -/
theorem prop21_step6_forward (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) :
    (altIdeal F (m + 1) n).map (cycleProj F (m + 1)) ≤
      ((multilinIdentities F n m).comap (wordLin F m)).map (cycleLin F m) := by
  have hm : 1 ≤ m := le_trans hn hnm
  rw [altIdeal_eq_span F (by omega), Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨τ, X, hX, rfl⟩, rfl⟩
  obtain ⟨p, hp, hco⟩ := forward_block_lemma F hn hnm τ X hX
  have hpV : p ∈ multilinSpace F m := by
    rcases hp with rfl | ⟨a, v, b, s, htr, _, rfl⟩
    · exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ s (sandwichElem_mem_multilinSpace F hm a v b htr)
  have hpT : p ∈ TIdeal F n := by
    rcases hp with rfl | ⟨a, v, b, s, htr, _, rfl⟩
    · exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ s (sandwichElem_mem_TIdeal F n hn a v b)
  have hcoord : cycCoord F m (perm F τ * altSum F X) = wordCoord F m p := funext hco
  refine ⟨wordCoord F m p, ?_, ?_⟩
  · show wordLin F m (wordCoord F m p) ∈ multilinIdentities F n m
    rw [wordLin_wordCoord hm hpV]
    exact Submodule.mem_inf.mpr ⟨hpV, hpT⟩
  · rw [cycleProj_eq hm, hcoord]

/-- **Step (6)** (lines 323-349): `P(I) = Φ(W_{n,m})`. -/
theorem prop21_step6 [CharZero F] (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) :
    (altIdeal F (m + 1) n).map (cycleProj F (m + 1)) =
      ((multilinIdentities F n m).comap (wordLin F m)).map (cycleLin F m) := by
  have hm : 1 ≤ m := le_trans hn hnm
  refine le_antisymm (prop21_step6_forward n m hn hnm) ?_
  rintro _ ⟨c, hc, rfl⟩
  have hq : wordLin F m c ∈ multilinIdentities F n m := hc
  have key : ∀ q ∈ multilinIdentities F n m,
      cycleLin F m (wordCoord F m q) ∈ (altIdeal F (m + 1) n).map (cycleProj F (m + 1)) := by
    intro q hq'
    rw [F1_spanning_proved n m hn] at hq'
    induction hq' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, v, b, htr, rfl⟩ := hx
      obtain ⟨τ, X, hX, hco⟩ := converse_block_lemma F hn hnm a v b htr
      have hcoord : wordCoord F m (sandwichElem F a v b) = cycCoord F m (perm F τ * altSum F X) :=
        (funext hco).symm
      rw [hcoord, ← cycleProj_eq hm]
      exact Submodule.mem_map_of_mem
        (by rw [altIdeal_eq_span F (by omega)]; exact Submodule.subset_span ⟨τ, X, hX, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ r hx
  have := key _ hq
  rwa [wordCoord_wordLin hm] at this

/-- **Step (7)** (line 344): `I^⊥ = A`, for any Young system. -/
theorem prop21_step7_perp [CharZero F] {N : ℕ} (Y : YoungSystem F N) (n : ℕ) (h : n + 1 ≤ N) (f : GrpAlg F N) :
    (∀ a ∈ altIdeal F N n, coeffPairing F f a = 0) ↔ f ∈ Y.rowSum n := by
  constructor
  · exact YoungSystem.mem_rowSum_of_perp_altIdeal Y n h f
  · intro hf a ha
    rw [YoungSystem.altIdeal_eq_blockSum Y n h] at ha
    exact coeffPairing_eq_zero_of_blockSum Y (S := {lam | lam.numRows ≤ n})
      (S' := {lam | n + 1 ≤ lam.numRows}) (fun mu h1 h2 => by simp only [Set.mem_ofPred_eq] at h1 h2; omega) hf ha

/-- **Step (7)** (v1.02 lines 281-283): `C_N ∩ A = C_N ∩ B_n`, for any Young system. -/
theorem prop21_step7_box {N : ℕ} (Y : YoungSystem F N) (n : ℕ) :
    cycleSpan F N ⊓ Y.rowSum n = cycleSpan F N ⊓ Y.boxSum n := by
  apply le_antisymm
  · exact le_inf inf_le_left (YoungSystem.cycleSpan_inf_rowSum_le_boxSum Y n)
  · exact inf_le_inf_left _ (boxSum_le_rowSum Y n)

/-- **Step (7)** (lines 338-350), the conclusion: for `c ∈ C_N`, `c ⊥ Φ(W_{n,m})` iff `c ∈ B_n`
(i.e. `C_N ∩ Φ(W_{n,m})^⊥ = C_N ∩ B_n`), for any Young system. -/
theorem prop21_step7_dual [CharZero F] (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (Y : YoungSystem F (m + 1))
    (c : GrpAlg F (m + 1)) (hc : c ∈ cycleSpan F (m + 1)) :
    (∀ x ∈ ((multilinIdentities F n m).comap (wordLin F m)).map (cycleLin F m), coeffPairing F c x = 0) ↔
      c ∈ Y.boxSum n := by
  have hm : 1 ≤ m := le_trans hn hnm
  have horth := cycCoord_range_eq_orthogonal n m hn hm Y
  -- `⟨c, Σ_w d_w Φ(w)⟩ = Σ_w d_w c(Φ w)`
  have hpair : ∀ d : Perm (Fin m) → F, coeffPairing F c (cycleLin F m d) = ∑ w, d w * c.coeff (wordCycle w) := by
    intro d
    rw [coeffPairing_of_mem_cycleSpan hc]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [show (cycleLin F m d).coeff (wordCycle w) = d w from congrFun (cycCoord_cycleLin m d) w, mul_comm]
  constructor
  · intro h
    have hmem : cycCoord F m c ∈ (dotForm (Perm (Fin m)) F).orthogonal
        (LinearMap.range ((wordCoord F m).comp (multilinIdentities F n m).subtype)) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      rintro u ⟨⟨p, hp⟩, rfl⟩
      have hx : cycleLin F m (wordCoord F m p) ∈
          ((multilinIdentities F n m).comap (wordLin F m)).map (cycleLin F m) := by
        refine ⟨wordCoord F m p, ?_, rfl⟩
        show wordLin F m (wordCoord F m p) ∈ multilinIdentities F n m
        rw [wordLin_wordCoord hm (Submodule.mem_inf.mp hp).1]
        exact hp
      have h0 := h _ hx
      rw [hpair] at h0
      rw [dotForm_apply]
      exact h0
    rw [← horth] at hmem
    obtain ⟨⟨c', hc'⟩, hcc'⟩ := hmem
    have : c' = c := cycCoord_injOn (Submodule.mem_inf.mp hc').1 hc hcc'
    rw [← this]
    exact (Submodule.mem_inf.mp hc').2
  · intro hB
    have hmem : cycCoord F m c ∈ LinearMap.range ((cycCoord F m).comp (cycleSpan F (m + 1) ⊓ Y.boxSum n).subtype) :=
      ⟨⟨c, Submodule.mem_inf.mpr ⟨hc, hB⟩⟩, rfl⟩
    rw [horth, LinearMap.BilinForm.mem_orthogonal_iff] at hmem
    rintro _ ⟨d, hd, rfl⟩
    have hd' : wordLin F m d ∈ multilinIdentities F n m := hd
    have h0 := hmem (wordCoord F m (wordLin F m d)) ⟨⟨wordLin F m d, hd'⟩, rfl⟩
    rw [wordCoord_wordLin hm, dotForm_apply] at h0
    rw [hpair]
    exact h0

end NagataHigman.Proofs

end
