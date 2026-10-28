/-
NagataHigman/Proofs/WordSide.lean — package P2: the word side of Proposition 2.1, forward direction.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Paper v1.02, lines 266-287
(step (6), forward half: P(I) ⊆ Φ(W_{n,m}); step (7), duality: f ⊥ Φ(W) ⇒ f ⊥ I for f ∈ C_N).
A vector `f ∈ C_N` is written `cycleElem F m φ = Σ_w φ(x_w) Φ(w)` for a linear functional `φ` on `F⟨X⟩`.
-/
import Mathlib
import NagataHigman.Proofs.Arcs
import NagataHigman.Proofs.FreeAlgebraLayer

set_option autoImplicit false

noncomputable section

namespace NagataHigman.Proofs

open Equiv

/-- The element `Σ_w φ(x_w) · Φ(w)` of `C_N` attached to a linear functional `φ` on `F⟨X⟩` (paper, step (7):
`f ∈ C_N` in the basis of `N`-cycles, with `f(Φ(w)) = φ(x_w)`). -/
def cycleElem (F : Type*) [Field F] (m : ℕ) (φ : FreeNUAlg F →ₗ[F] F) : GrpAlg F (m + 1) :=
  ∑ w : Perm (Fin m), φ (multilinWord F w) • perm F (wordCycle w)

namespace WordSide

variable {F : Type*} [Field F]

theorem coeff_cycleElem_apply (m : ℕ) (φ : FreeNUAlg F →ₗ[F] F) (σ : Perm (Fin (m + 1))) :
    (cycleElem F m φ).coeff σ = ∑ w : Perm (Fin m), if wordCycle w = σ then φ (multilinWord F w) else 0 := by
  classical
  unfold cycleElem perm
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- `⟨Σ_w φ(x_w) Φ(w), a⟩ = Σ_w φ(x_w) a(Φ(w))`. -/
theorem coeffPairing_cycleElem (m : ℕ) (φ : FreeNUAlg F →ₗ[F] F) (a : GrpAlg F (m + 1)) :
    coeffPairing F (cycleElem F m φ) a =
      ∑ w : Perm (Fin m), φ (multilinWord F w) * a.coeff (wordCycle w) := by
  unfold coeffPairing
  simp_rw [coeff_cycleElem_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

theorem coeffPairing_add_right {N : ℕ} (c x y : GrpAlg F N) :
    coeffPairing F c (x + y) = coeffPairing F c x + coeffPairing F c y := by
  simp [coeffPairing, MonoidAlgebra.coeff_add, mul_add, Finset.sum_add_distrib]

theorem coeffPairing_smul_right {N : ℕ} (c x : GrpAlg F N) (r : F) :
    coeffPairing F c (r • x) = r * coeffPairing F c x := by
  simp [coeffPairing, MonoidAlgebra.coeff_smul, Finset.mul_sum, mul_left_comm]

theorem wordMono_injective {m : ℕ} (hm : 1 ≤ m) : Function.Injective (wordMono (m := m)) := by
  intro w₁ w₂ h
  have hne : ∀ w : Perm (Fin m), wordList w ≠ [] := by
    intro w hnil
    have := congrArg List.length hnil
    simp [wordList] at this
    omega
  have hl := Arcs.monoOf_inj (hne w₁) (hne w₂) h
  apply Equiv.ext
  intro i
  exact Fin.ext (congrFun (List.ofFn_injective hl) i)

/-- Every `p ∈ V_m` is `Σ_w p(x_w) · x_w` in the basis of multilinear words. -/
theorem eq_sum_coeff_multilinWord {m : ℕ} (hm : 1 ≤ m) {p : FreeNUAlg F} (hp : p ∈ multilinSpace F m) :
    p = ∑ w : Perm (Fin m), p.coeff (wordMono w) • multilinWord F w := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w₀, rfl⟩ := hx
    rw [Finset.sum_eq_single w₀]
    · rw [multilinWord_eq_single F hm, MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_smul]
    · intro w _ hw
      have hne : wordMono w₀ ≠ wordMono w := fun h => hw (wordMono_injective hm h).symm
      rw [multilinWord_eq_single F hm w₀, MonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hne,
        zero_smul]
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

end WordSide

open WordSide

/-- **P2a**: `Σ_w φ(x_w) Φ(w) ∈ C_N`. -/
theorem cycleElem_mem_cycleSpan {F : Type*} [Field F] (m : ℕ) (hm : 1 ≤ m) (φ : FreeNUAlg F →ₗ[F] F) :
    cycleElem F m φ ∈ cycleSpan F (m + 1) := by
  unfold cycleElem cycleSpan
  exact Submodule.sum_mem _ (fun w _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨wordCycle w, wordCycle_isFullCycle hm w, rfl⟩))

/-- **P2c**: the coefficient of `Φ(w)` in `Σ_w φ(x_w) Φ(w)` is `φ(x_w)`. -/
theorem coeff_cycleElem {F : Type*} [Field F] (m : ℕ) (φ : FreeNUAlg F →ₗ[F] F) (w : Perm (Fin m)) :
    (cycleElem F m φ).coeff (wordCycle w) = φ (multilinWord F w) := by
  rw [coeff_cycleElem_apply, Finset.sum_eq_single w]
  · exact ite_eq_left rfl
  · intro w' _ hw'
    exact ite_eq_right (fun h => hw' (wordCycle_injective h))
  · intro h
    exact absurd (Finset.mem_univ w) h

/-- **P2d** ((F1), forward half): every `a · L(v_1, …, v_n) · b` lies in `T = (x^n)^T`. -/
theorem sandwichElem_mem_TIdeal (F : Type*) [Field F] (n : ℕ) (hn : 1 ≤ n) (a : List ℕ) (v : Fin n → List ℕ)
    (b : List ℕ) : sandwichElem F a v b ∈ TIdeal F n := by
  unfold sandwichElem sandwich
  dsimp only
  by_cases ha : a = [] <;> by_cases hb : b = []
  · rw [ite_eq_left hb, ite_eq_left ha]
    exact F1_symSum_mem_proved F n hn _
  · rw [ite_eq_right hb, ite_eq_left ha]
    exact symSum_mul_mem F n hn _ _
  · rw [ite_eq_left hb, ite_eq_right ha]
    exact mul_symSum_mem F n hn _ _
  · rw [ite_eq_right hb, ite_eq_right ha]
    exact mul_symSum_mul_mem F n hn _ _ _

/-- **P2b** (paper, steps (6)-(7), forward half): if `φ` vanishes on `W_{n,m} = V_m ∩ T`, then
`Σ_w φ(x_w) Φ(w)` is orthogonal to the ideal `I` generated by `E`. -/
theorem cycleElem_perp_altIdeal {F : Type*} [Field F] (n m : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (φ : FreeNUAlg F →ₗ[F] F) (hφ : ∀ p ∈ multilinIdentities F n m, φ p = 0) :
    ∀ a ∈ altIdeal F (m + 1) n, coeffPairing F (cycleElem F m φ) a = 0 := by
  have hm : 1 ≤ m := le_trans hn hnm
  -- the generators `τ E_X`, `|X| = n + 1`
  have hgen : ∀ (τ : Perm (Fin (m + 1))) (X : Finset (Fin (m + 1))), X.card = n + 1 →
      coeffPairing F (cycleElem F m φ) (perm F τ * altSum F X) = 0 := by
    intro τ X hX
    obtain ⟨p, hp, hcoeff⟩ := forward_block_lemma F hn hnm τ X hX
    have hpW : p ∈ multilinIdentities F n m := by
      rcases hp with rfl | ⟨a, v, b, s, htriple, _, rfl⟩
      · exact Submodule.zero_mem _
      · exact Submodule.mem_inf.mpr ⟨Submodule.smul_mem _ s (sandwichElem_mem_multilinSpace F hm a v b htriple),
          Submodule.smul_mem _ s (sandwichElem_mem_TIdeal F n hn a v b)⟩
    rw [coeffPairing_cycleElem]
    simp_rw [hcoeff]
    have hexp : ∑ w : Perm (Fin m), φ (multilinWord F w) * p.coeff (wordMono w) = φ p := by
      conv_rhs => rw [eq_sum_coeff_multilinWord hm (Submodule.mem_inf.mp hpW).1]
      rw [map_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hexp]
    exact hφ p hpW
  intro a ha
  rw [altIdeal_eq_span F (by omega)] at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨τ, X, hX, rfl⟩ := hx
    exact hgen τ X hX
  | zero => simp [coeffPairing]
  | add x y _ _ hx hy => rw [coeffPairing_add_right, hx, hy, add_zero]
  | smul r x _ hx => rw [coeffPairing_smul_right, hx, mul_zero]

end NagataHigman.Proofs

end
