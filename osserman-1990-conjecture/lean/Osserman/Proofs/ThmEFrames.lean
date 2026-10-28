/-
ThmEFrames.lean — linear polynomial fields and Clifford frames, paper 013, lines 747–766.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.ThreeRoot
import Osserman.Proofs.Threshold

namespace Osserman.Proofs.ThmEFrames

open Osserman Matrix MvPolynomial Osserman.Proofs.Threshold

lemma eval_linear_of_homogeneous (p : MvPolynomial (Fin 16) ℝ) (hp : p.IsHomogeneous 1) :
    ∃ f : Vec 16 →ₗ[ℝ] ℝ, ∀ x : Vec 16, eval x p = f x := by
  have member : p ∈ Submodule.span ℝ (Set.range (X : Fin 16 → MvPolynomial (Fin 16) ℝ)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hp
  clear hp
  induction member using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    exact ⟨LinearMap.proj i, fun x => eval_X i⟩
  | zero => exact ⟨0, by intro x; simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨f, hf⟩ := ihp
    obtain ⟨g, hg⟩ := ihq
    exact ⟨f + g, by intro x; simp only [eval_add, hf, hg, LinearMap.add_apply]⟩
  | smul c p hp ih =>
    obtain ⟨f, hf⟩ := ih
    exact ⟨c • f, by intro x; simp only [smul_eval, hf, LinearMap.smul_apply, smul_eq_mul]⟩

theorem thm_E_linear_fields_proved (E : Fin 16 → MvPolynomial (Fin 16) ℝ) (d : ℕ)
    (hodd : Odd d) (hd : d ≤ 2) (hE : ∀ j, (E j).IsHomogeneous d) :
    ∃ J : Matrix (Fin 16) (Fin 16) ℝ, ∀ x : Vec 16, evalField E x = J *ᵥ x := by
  have degree : d = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  subst d
  choose f hf using fun j => eval_linear_of_homogeneous (E j) (hE j)
  let F : Vec 16 →ₗ[ℝ] Vec 16 := LinearMap.pi f
  refine ⟨LinearMap.toMatrix' F, ?_⟩
  intro x
  rw [LinearMap.toMatrix'_mulVec]
  ext j
  exact hf j x

theorem thm_E_frame_clifford_proved {n t : ℕ} (J : Fin t → Matrix (Fin n) (Fin n) ℝ)
    (horth : ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ a b, (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0)
    (hperp : ∀ x : Vec n, x ⬝ᵥ x = 1 → ∀ a, x ⬝ᵥ (J a *ᵥ x) = 0) :
    IsCliffordStr J ∧ ∀ a, (J a)ᵀ * J a = 1 := by
  have norm_all (x : Vec n) (a b : Fin t) :
      (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then x ⬝ᵥ x else 0 := by
    by_cases zero : x = 0
    · subst x; simp
    obtain ⟨c, unit⟩ := unit_rescale x zero
    have cne : c ≠ 0 := by intro equal; simp [equal] at unit
    have scaled := horth (c • x) unit a b
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at scaled unit
    by_cases equal : a = b
    · simp only [equal, ite_true]
      simp only [equal, ite_true] at scaled
      apply mul_left_cancel₀ (mul_ne_zero cne cne)
      nlinarith
    · simp only [equal, ite_false] at scaled ⊢
      apply (mul_eq_zero.mp (show (c * c) * ((J a *ᵥ x) ⬝ᵥ (J b *ᵥ x)) = 0 by nlinarith)).resolve_left
      exact mul_ne_zero cne cne
  have perp_all (x : Vec n) (a : Fin t) : x ⬝ᵥ (J a *ᵥ x) = 0 := by
    by_cases zero : x = 0
    · subst x; simp
    obtain ⟨c, unit⟩ := unit_rescale x zero
    have cne : c ≠ 0 := by intro equal; simp [equal] at unit
    have scaled := hperp (c • x) unit a
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at scaled
    exact (mul_eq_zero.mp (show (c * c) * (x ⬝ᵥ (J a *ᵥ x)) = 0 by nlinarith)).resolve_left (mul_ne_zero cne cne)
  have skew (a : Fin t) : (J a)ᵀ = -J a := by
    ext i j
    have hii := perp_all (Pi.single i 1) a
    have hjj := perp_all (Pi.single j 1) a
    have sum := perp_all (Pi.single i 1 + Pi.single j 1) a
    simp only [Matrix.mulVec_add, Matrix.mulVec_single_one, add_dotProduct,
      dotProduct_add, single_one_dotProduct, Pi.add_apply, Matrix.col_apply] at hii hjj sum
    change J a j i = -J a i j
    linarith
  have skew_move (a : Fin t) (x y : Vec n) : x ⬝ᵥ (J a *ᵥ y) = -((J a *ᵥ x) ⬝ᵥ y) := by
    have equal := Matrix.dotProduct_transpose_mulVec (J a) y x
    rw [skew, Matrix.neg_mulVec, dotProduct_neg, dotProduct_comm y (J a *ᵥ x)] at equal
    exact equal.symm
  have anti (a b : Fin t) : J a * J b + J b * J a = if a = b then -2 else 0 := by
    have symmetric : (J a * J b + J b * J a).IsSymm := by
      simp only [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_mul, skew, neg_mul_neg]
      exact add_comm _ _
    have target : (if a = b then (-2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) else 0) =
        (if a = b then (-2 : Matrix (Fin n) (Fin n) ℝ) else 0) := by
      split_ifs <;> norm_num [two_smul]
    rw [← target]
    apply symm_eq_of_quadratic _ _ symmetric (by split_ifs <;> simp [Matrix.IsSymm])
    intro x
    have qab : x ⬝ᵥ ((J a * J b) *ᵥ x) = -((J a *ᵥ x) ⬝ᵥ (J b *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, skew_move]
    have qba : x ⬝ᵥ ((J b * J a) *ᵥ x) = -((J b *ᵥ x) ⬝ᵥ (J a *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, skew_move]
    rw [Matrix.add_mulVec, dotProduct_add, qab, qba, norm_all, norm_all]
    by_cases equal : a = b
    · simp only [equal, ite_true, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
      ring
    · have reverse : b ≠ a := Ne.symm equal
      simp only [equal, reverse, ite_false, neg_zero, add_zero, Matrix.zero_mulVec, dotProduct_zero]
  refine ⟨⟨skew, anti⟩, ?_⟩
  intro a
  have symmetric : ((J a)ᵀ * J a).IsSymm := by simp [Matrix.IsSymm, Matrix.transpose_mul]
  apply symm_eq_of_quadratic _ _ symmetric (by simp [Matrix.IsSymm])
  intro x
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, norm_all, if_pos rfl, Matrix.one_mulVec]

theorem thm_E_frame_span_proved (R : CurvTensor 16) (m : Fin 3 → ℕ) (ev : Fin 3 → ℝ)
    (J : Fin (m 2) → Matrix (Fin 16) (Fin 16) ℝ) (h : ThmEFrame R m ev J) :
    ∀ x : Vec 16, x ⬝ᵥ x = 1 → (∀ a b, (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0) ∧
      Module.End.eigenspace (R.jacobiMap x) (ev 2) ⊓ perp x = Submodule.span ℝ (Set.range fun a => J a *ᵥ x) := by
  intro x hx
  have system := h.2.2.2.1
  have skew := system.1
  have orthogonal (a b : Fin (m 2)) : (J a *ᵥ x) ⬝ᵥ (J b *ᵥ x) = if a = b then 1 else 0 := by
    have relation := congrArg (fun M : Matrix (Fin 16) (Fin 16) ℝ => x ⬝ᵥ (M *ᵥ x)) (system.2 a b)
    have moved (a : Fin (m 2)) (y : Vec 16) : x ⬝ᵥ (J a *ᵥ y) = -((J a *ᵥ x) ⬝ᵥ y) := by
      have equal := Matrix.dotProduct_transpose_mulVec (J a) y x
      rw [skew, Matrix.neg_mulVec, dotProduct_neg, dotProduct_comm y (J a *ᵥ x)] at equal
      exact equal.symm
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, dotProduct_add, moved,
      dotProduct_comm (J b *ᵥ x) (J a *ᵥ x)] at relation
    by_cases equal : a = b
    · subst b
      have two : (-2 : Matrix (Fin 16) (Fin 16) ℝ) = (-2 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) := by norm_num [two_smul]
      simp only [ite_true, two, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hx, smul_eq_mul] at relation
      simp only [ite_true]
      linarith
    · simp only [equal, ite_false, Matrix.zero_mulVec, dotProduct_zero] at relation ⊢
      linarith
  have perpendicular (a : Fin (m 2)) : x ⬝ᵥ (J a *ᵥ x) = 0 := by
    have equal := Matrix.dotProduct_transpose_mulVec (J a) x x
    rw [skew, Matrix.neg_mulVec, dotProduct_neg] at equal
    linarith
  let E := Module.End.eigenspace (R.jacobiMap x) (ev 2) ⊓ perp x
  have inclusion : Submodule.span ℝ (Set.range fun a => J a *ᵥ x) ≤ E := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨h.2.2.2.2 x hx a, perpendicular a⟩
  have independent : LinearIndependent ℝ (fun a => J a *ᵥ x) := by
    rw [linearIndependent_iff']
    intro s c zero a ha
    have image := congrArg (fun y : Vec 16 => (J a *ᵥ x) ⬝ᵥ y) zero
    simpa only [dotProduct_sum, dotProduct_smul, orthogonal, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, ha, ite_true, dotProduct_zero] using image
  have span_dim := finrank_span_eq_card independent
  have e_dim : Module.finrank ℝ E = m 2 := h.2.2.1 x hx 2
  have same : Submodule.span ℝ (Set.range fun a => J a *ᵥ x) = E := by
    apply Submodule.eq_of_le_of_finrank_eq inclusion
    simpa only [Fintype.card_fin, e_dim] using span_dim
  exact ⟨orthogonal, same.symm⟩

end Osserman.Proofs.ThmEFrames

