/-
Lem82R1.lean — Lemma 8.2 of paper 013, the case r = 1, second half (sec_small_roots.tex of the posting copy, lines 124-135):
the third identity in lifted form, the hyperplane `φ = 0`, the factorization `Ψ̃(x) = φ(C̃x)B'x`, the step to `r = 2`,
and the conclusion `q ∣ Ψ`. Rows lem_8_2_r1_third, _hyperplane, _nonvanish, _factor, _not_div, _to_r2 are PROVED here;
lem_8_2_r1 is proved from the exact types of the six rows it uses (`lem_8_2_r1_given`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Osserman.Defs.SmallRoots
import Osserman.Proofs.Poly
import Osserman.Proofs.S8Tools
import Osserman.Proofs.Lem82Common
import Mathlib.Topology.Algebra.MvPolynomial

namespace Osserman.Proofs.Lem82R1

open Osserman Matrix MvPolynomial Osserman.Proofs.Lem82Common

/-! ### Evaluation of the polynomial fields -/

lemma evalField_apply (E : Fin 16 → MvPolynomial (Fin 16) ℝ) (x : Vec 16) (j : Fin 16) :
    evalField E x j = eval x (E j) := rfl

/-- `g(σ(x))`: evaluating a substitution evaluates `g` at the field `σ(x)`. -/
lemma eval_bind₁ (σ : Fin 16 → MvPolynomial (Fin 16) ℝ) (g : MvPolynomial (Fin 16) ℝ) (x : Vec 16) :
    eval x (bind₁ σ g) = eval (evalField σ x) g :=
  eval₂Hom_bind₁ (RingHom.id ℝ) x σ g

lemma eval_bind₁_linP (M : Matrix (Fin 16) (Fin 16) ℝ) (g : MvPolynomial (Fin 16) ℝ) (x : Vec 16) :
    eval x (bind₁ (linP M) g) = eval (M *ᵥ x) g := by
  rw [eval_bind₁, S8Tools.evalField_linP]

/-- `P(y) = φ(y)Ψ̃(y) + q(y)C̃y` at every point. -/
lemma evalField_dec {P Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ} {f : Vec 16} {Ct : Matrix (Fin 16) (Fin 16) ℝ}
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (y : Vec 16) :
    evalField P y = (f ⬝ᵥ y) • evalField Ψt y + (y ⬝ᵥ y) • (Ct *ᵥ y) := by
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evalField_apply, hdec k, map_add, map_mul, eval_formP,
    Poly.eval_sqP, Lem82DivQ.eval_linP]

/-! ### Linear algebra and homogeneity -/

lemma sq_eq_neg_one {S : Matrix (Fin 16) (Fin 16) ℝ} (hS : Sᵀ = -S) (hSo : Sᵀ * S = 1) : S * S = -1 := by
  rw [hS, neg_mul] at hSo
  exact neg_eq_iff_eq_neg.mp hSo

lemma dot_self_ne_zero {v : Vec 16} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_self_eq_zero.mp h)

lemma isHomogeneous_linP (M : Matrix (Fin 16) (Fin 16) ℝ) (j : Fin 16) : (linP M j).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_C_mul_X (M j k) k

lemma isHomogeneous_bind₁_linP (M : Matrix (Fin 16) (Fin 16) ℝ) {g : MvPolynomial (Fin 16) ℝ} {n : ℕ}
    (hg : g.IsHomogeneous n) : (bind₁ (linP M) g).IsHomogeneous n := by
  have h := hg.aeval (linP M) (isHomogeneous_linP M)
  rw [one_mul] at h
  exact h

/-- `φ(Sx) = ⟨Sᵀf, x⟩`. -/
lemma bind₁_linP_formP (S : Matrix (Fin 16) (Fin 16) ℝ) (f : Vec 16) :
    bind₁ (linP S) (formP f) = formP (Sᵀ *ᵥ f) := by
  apply MvPolynomial.funext
  intro x
  rw [eval_bind₁_linP, eval_formP, eval_formP, dotProduct_mulVec, mulVec_transpose]

/-- The substitution `x ↦ x - (⟨f,x⟩/|f|²) f`, the orthogonal projection onto `f^⊥`. -/
noncomputable def projP (f : Vec 16) (k : Fin 16) : MvPolynomial (Fin 16) ℝ :=
  X k - C (f k / (f ⬝ᵥ f)) * formP f

/-- A polynomial that vanishes on the hyperplane `⟨f,x⟩ = 0` is divisible by `⟨f,x⟩`: modulo `⟨f,x⟩` the projection
`projP f` is the identity substitution, and `G ∘ projP f` vanishes everywhere. -/
lemma dvd_formP_of_vanish {f : Vec 16} (hf : f ≠ 0) (G : MvPolynomial (Fin 16) ℝ)
    (hG : ∀ x : Vec 16, f ⬝ᵥ x = 0 → eval x G = 0) : formP f ∣ G := by
  have hff := dot_self_ne_zero hf
  have h1 : bind₁ (projP f) G = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_bind₁, map_zero]
    apply hG
    have hy : evalField (projP f) x = x - ((f ⬝ᵥ x) / (f ⬝ᵥ f)) • f := by
      funext k
      simp only [projP, evalField_apply, map_sub, eval_X, map_mul, eval_C, eval_formP, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
    rw [hy, dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hff, sub_self]
  have h2 : (Ideal.Quotient.mkₐ ℝ (Ideal.span {formP f})).comp (bind₁ (projP f)) =
      Ideal.Quotient.mkₐ ℝ (Ideal.span {formP f}) := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [AlgHom.comp_apply, bind₁_X_right, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-C (f k / (f ⬝ᵥ f)), by simp only [projP]; ring⟩
  have h3 := AlgHom.congr_fun h2 G
  rw [AlgHom.comp_apply, h1, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h3
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h3.symm)

/-- A nonzero vector orthogonal to `f ≠ 0`. -/
lemma exists_perp_ne_zero {f : Vec 16} (hf : f ≠ 0) : ∃ u : Vec 16, f ⬝ᵥ u = 0 ∧ u ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
  have hne : ∀ k : Fin 16, k + 1 ≠ k := by decide
  refine ⟨Pi.single i (f (i + 1)) - Pi.single (i + 1) (f i), ?_, fun h0 => ?_⟩
  · rw [dotProduct_sub, dotProduct_single, dotProduct_single, mul_comm, sub_self]
  · have e := congrFun h0 (i + 1)
    simp [hne i] at e
    exact hi e

/-! ### The rows -/

/-- **lem_8_2_r1_third** (lines 124-126): "The third identity in (eq:cubicidentities) now reads
$\varphi(P(x))\tilde \Psi(P(x))=-q^3\varphi(x)\tilde C\tilde \Psi(x)$". -/
theorem lem_8_2_r1_third_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1) :
    ∀ j, bind₁ P (formP f) * bind₁ P (Ψt j) =
      -(sqP 16 ^ 3 * formP f * ∑ k, MvPolynomial.C (Ct j k) * Ψt k) := by
  intro j
  apply MvPolynomial.funext
  intro x
  obtain ⟨-, hq, h3⟩ := hP x
  have hCp : Ct *ᵥ evalField P x = (f ⬝ᵥ x) • (Ct *ᵥ evalField Ψt x) - (x ⬝ᵥ x) • x := by
    rw [evalField_dec hdec x, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, sq_eq_neg_one hCt hCo,
      neg_mulVec, one_mulVec, smul_neg, ← sub_eq_add_neg]
  have hCψ : (Ct *ᵥ evalField Ψt x) j = ∑ k, Ct j k * eval x (Ψt k) := by
    simp [mulVec, dotProduct, evalField_apply]
  have hj := congrFun h3 j
  rw [evalField_dec hdec (evalField P x), hq, hCp] at hj
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, evalField_apply, hCψ] at hj
  simp only [map_mul, map_neg, map_pow, eval_bind₁, eval_formP, Poly.eval_sqP, map_sum, eval_C]
  linear_combination hj

/-- **lem_8_2_r1_hyperplane** (lines 126-128): "On the hyperplane $\varphi=0$ we have $P(x)=q\tilde Cx$, so
$\varphi(\tilde Cx)\tilde \Psi(\tilde Cx)$ vanishes there". -/
theorem lem_8_2_r1_hyperplane_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1)
    (hΨt : ∀ j, (Ψt j).IsHomogeneous 2) :
    ∀ x : Vec 16, f ⬝ᵥ x = 0 → evalField P x = (x ⬝ᵥ x) • (Ct *ᵥ x) ∧
      ∀ j, (f ⬝ᵥ (Ct *ᵥ x)) * eval (Ct *ᵥ x) (Ψt j) = 0 := by
  intro x hx
  have hPx : evalField P x = (x ⬝ᵥ x) • (Ct *ᵥ x) := by
    rw [evalField_dec hdec x, hx, zero_smul, zero_add]
  refine ⟨hPx, fun j => ?_⟩
  have h := congrArg (eval x) (lem_8_2_r1_third_proved P hP f Ψt Ct hdec hCt hCo j)
  simp only [map_mul, map_neg, map_pow, eval_bind₁, eval_formP, hx, mul_zero, zero_mul, neg_zero] at h
  rw [hPx, dotProduct_smul, S8Tools.eval_smul_of_homogeneous (hΨt j), smul_eq_mul] at h
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have h' : (x ⬝ᵥ x) ^ 3 * ((f ⬝ᵥ (Ct *ᵥ x)) * eval (Ct *ᵥ x) (Ψt j)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 3 (dot_self_ne_zero hx0))

/-- **lem_8_2_r1_nonvanish** (lines 128-130): "the form $\varphi(\tilde Cx)=-\ip{\tilde Cf}x$ does not vanish
identically on $f^\perp$, since $\tilde Cf\ne0$ is orthogonal to $f$" (witness `x = C̃f`). -/
theorem lem_8_2_r1_nonvanish_proved (S : Matrix (Fin 16) (Fin 16) ℝ) (hS : Sᵀ = -S) (hSo : Sᵀ * S = 1) (f : Vec 16)
    (hf : f ≠ 0) :
    (∀ x : Vec 16, f ⬝ᵥ (S *ᵥ x) = -((S *ᵥ f) ⬝ᵥ x)) ∧ S *ᵥ f ≠ 0 ∧ (S *ᵥ f) ⬝ᵥ f = 0 ∧
      ∃ x : Vec 16, f ⬝ᵥ x = 0 ∧ f ⬝ᵥ (S *ᵥ x) ≠ 0 := by
  have h1 : ∀ x : Vec 16, f ⬝ᵥ (S *ᵥ x) = -((S *ᵥ f) ⬝ᵥ x) := by
    intro x
    rw [dotProduct_mulVec, ← mulVec_transpose, hS, neg_mulVec, neg_dotProduct]
  have h3 : (S *ᵥ f) ⬝ᵥ f = 0 := by
    have e := h1 f
    rw [dotProduct_comm f] at e
    linarith
  refine ⟨h1, fun h0 => ?_, h3, S *ᵥ f, by rw [dotProduct_comm]; exact h3, ?_⟩
  · apply hf
    have e : (Sᵀ * S) *ᵥ f = f := by rw [hSo, one_mulVec]
    rw [← e, ← mulVec_mulVec, h0, mulVec_zero]
  · rw [mulVec_mulVec, sq_eq_neg_one hS hSo, neg_mulVec, one_mulVec, dotProduct_neg]
    exact neg_ne_zero.mpr (dot_self_ne_zero hf)

/-- On `f^⊥`, every component of `Ψ̃(C̃x)` vanishes: `φ(C̃x)Ψ̃(C̃x) = 0` there, and `φ(C̃x)` vanishes on `f^⊥` only on
a proper hyperplane, so `Ψ̃(C̃x) = 0` on a dense subset of every line of `f^⊥` through `C̃f`, hence everywhere. -/
lemma vanish_on_hyperplane (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (hf : f ≠ 0) (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1)
    (hΨt : ∀ j, (Ψt j).IsHomogeneous 2) (j : Fin 16) (x : Vec 16) (hx : f ⬝ᵥ x = 0) :
    eval (Ct *ᵥ x) (Ψt j) = 0 := by
  have hyp := lem_8_2_r1_hyperplane_proved P hP f Ψt Ct hdec hCt hCo hΨt
  obtain ⟨-, -, -, x0, hx0, hb⟩ := lem_8_2_r1_nonvanish_proved Ct hCt hCo f hf
  have hcont : Continuous fun t : ℝ => eval (Ct *ᵥ (x + t • x0)) (Ψt j) := by
    simp_rw [mulVec_add, mulVec_smul]
    exact (MvPolynomial.continuous_eval (Ψt j)).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : Set.EqOn (fun t : ℝ => eval (Ct *ᵥ (x + t • x0)) (Ψt j)) (fun _ => 0)
      {-((f ⬝ᵥ (Ct *ᵥ x)) / (f ⬝ᵥ (Ct *ᵥ x0)))}ᶜ := by
    intro t ht
    have hne : f ⬝ᵥ (Ct *ᵥ (x + t • x0)) ≠ 0 := by
      rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
      intro h0
      apply ht
      rw [Set.mem_singleton_iff, eq_neg_iff_add_eq_zero, add_div' _ _ _ hb, div_eq_zero_iff]
      left
      linear_combination h0
    have hperp : f ⬝ᵥ (x + t • x0) = 0 := by rw [dotProduct_add, dotProduct_smul, hx, hx0, smul_zero, add_zero]
    exact (mul_eq_zero.mp ((hyp _ hperp).2 j)).resolve_left hne
  have e := congrFun (hcont.ext_on (dense_compl_singleton _) continuous_const hzero) 0
  simpa using e

/-- **lem_8_2_r1_factor** (lines 130-132): "Hence $\varphi$ divides every component of $\tilde \Psi(\tilde Cx)$, and,
as $\tilde C^{-1}=-\tilde C$, we get $\tilde \Psi(x)=\varphi(\tilde Cx)B'x$ with $B'$ linear". -/
theorem lem_8_2_r1_factor_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP : CubicIdentities P) (f : Vec 16)
    (hf : f ≠ 0) (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ)
    (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (hCt : Ctᵀ = -Ct) (hCo : Ctᵀ * Ct = 1)
    (hΨt : ∀ j, (Ψt j).IsHomogeneous 2) :
    (∀ j, formP f ∣ bind₁ (linP Ct) (Ψt j)) ∧
      ∃ B' : Matrix (Fin 16) (Fin 16) ℝ, ∀ j, Ψt j = bind₁ (linP Ct) (formP f) * linP B' j := by
  have hdvd : ∀ j, formP f ∣ bind₁ (linP Ct) (Ψt j) := fun j =>
    dvd_formP_of_vanish hf _ fun x hx => by
      rw [eval_bind₁_linP]
      exact vanish_on_hyperplane P hP f hf Ψt Ct hdec hCt hCo hΨt j x hx
  refine ⟨hdvd, ?_⟩
  have hlin : ∀ j, ∃ c : Vec 16, bind₁ (linP Ct) (Ψt j) = formP f * formP c := by
    intro j
    obtain ⟨g, hg⟩ := hdvd j
    have e := eq_mul_homogeneousComponent (isHomogeneous_formP f) (isHomogeneous_bind₁_linP Ct (hΨt j)) (by norm_num) hg
    obtain ⟨c, hc⟩ := Lem82DivQ.linear_eq_sum (homogeneousComponent_isHomogeneous (2 - 1) g)
    exact ⟨c, by rw [e, ← hc]; rfl⟩
  choose c hc using hlin
  refine ⟨Matrix.of c * Ct, fun j => ?_⟩
  apply MvPolynomial.funext
  intro x
  have hx : Ct *ᵥ (-(Ct *ᵥ x)) = x := by
    rw [mulVec_neg, mulVec_mulVec, sq_eq_neg_one hCt hCo, neg_mulVec, one_mulVec, neg_neg]
  have e := congrArg (eval (-(Ct *ᵥ x))) (hc j)
  rw [eval_bind₁_linP, hx, map_mul, eval_formP, eval_formP, dotProduct_neg, dotProduct_neg, neg_mul_neg] at e
  rw [e, map_mul, eval_bind₁_linP, eval_formP, Lem82DivQ.eval_linP, ← mulVec_mulVec]
  rfl

/-- **lem_8_2_r1_not_div** (lines 133-134): "$\varphi(x)\varphi(\tilde Cx)$ is a quadratic form not divisible by $q$".
A multiple of `q` of degree 2 is `c·q`; it vanishes at `u ⊥ f, u ≠ 0`, so `c = 0`, and the product of two nonzero
linear forms is not `0`. -/
theorem lem_8_2_r1_not_div_proved (S : Matrix (Fin 16) (Fin 16) ℝ) (hSo : Sᵀ * S = 1) (f : Vec 16) (hf : f ≠ 0) :
    ¬ sqP 16 ∣ formP f * bind₁ (linP S) (formP f) := by
  rintro ⟨c, hc⟩
  rw [bind₁_linP_formP] at hc
  have hc0 := eq_mul_homogeneousComponent Poly.sqP_isHomogeneous
    ((isHomogeneous_formP f).mul (isHomogeneous_formP _)) (by norm_num) hc
  rw [show (1 + 1 - 2 : ℕ) = 0 from rfl, homogeneousComponent_zero] at hc0
  obtain ⟨u, hu, hu0⟩ := exists_perp_ne_zero hf
  have hev := congrArg (eval u) hc0
  rw [map_mul, map_mul, eval_formP, hu, zero_mul, Poly.eval_sqP, eval_C] at hev
  have hcoef : c.coeff 0 = 0 := (mul_eq_zero.mp hev.symm).resolve_left (dot_self_ne_zero hu0)
  rw [hcoef, C_0, mul_zero, mul_eq_zero] at hc0
  rcases hc0 with h | h
  · exact formP_ne_zero hf h
  · refine formP_ne_zero (fun h0 => hf ?_) h
    have e : S *ᵥ (Sᵀ *ᵥ f) = f := by rw [mulVec_mulVec, mul_eq_one_comm.mp hSo, one_mulVec]
    rw [← e, h0, mulVec_zero]

/-- **lem_8_2_r1_to_r2** (lines 132-134): "Then $P(x)=\varphi(x)\varphi(\tilde Cx)\,B'x+q\tilde Cx$ ... and the case
$r=2$ applies" (the new decomposition is a lift with `r = 2`). -/
theorem lem_8_2_r1_to_r2_proved (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (hP3 : ∀ j, (P j).IsHomogeneous 3)
    (hP : CubicIdentities P) (f : Vec 16) (hf : f ≠ 0) (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ)
    (Ct B' : Matrix (Fin 16) (Fin 16) ℝ) (hdec : ∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) (_hCt : Ctᵀ = -Ct)
    (hCo : Ctᵀ * Ct = 1) (hB' : ∀ j, Ψt j = bind₁ (linP Ct) (formP f) * linP B' j) :
    Lem82Lift P 2 (formP f * bind₁ (linP Ct) (formP f)) (linP B') Ct := by
  refine ⟨hP3, hP, by norm_num, by norm_num, ?_, lem_8_2_r1_not_div_proved Ct hCo f hf,
    fun j => isHomogeneous_linP B' j, fun j => ?_⟩
  · rw [bind₁_linP_formP]
    exact (isHomogeneous_formP f).mul (isHomogeneous_formP _)
  · rw [hdec j, hB' j, mul_assoc]

/-- **lem_8_2_r1** (lines 134-135): "$B'=0$, so $\tilde \Psi=0$, and $\Psi=-qa$ is divisible by $q$", from the exact
types of the rows lem_8_2_r1_form, lem_8_2_r1_div, lem_8_2_r1_skew, lem_8_2_r1_divides, lem_8_2_r1_orth (first half
of the case `r = 1`) and lem_8_2_r2 (the case `r = 2`), in that order. -/
theorem lem_8_2_r1_given
    (hform : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
      (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P 1 φ Ψ Cm →
      ∃ f : Vec 16, f ≠ 0 ∧ φ = formP f)
    (hdiv : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : Vec 16) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
      (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P 1 (formP f) Ψ Cm →
      ∃ a : Vec 16, quadP Cm = formP f * formP a)
    (hskew : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (f : Vec 16) (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ)
      (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P 1 (formP f) Ψ Cm → ∀ (a : Vec 16),
      quadP Cm = formP f * formP a →
      let Ct := Cm - vecMulVec a f
      let Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ := fun j => Ψ j + sqP 16 * MvPolynomial.C (a j)
      (∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) ∧ Ctᵀ = -Ct ∧ ∀ j, (Ψt j).IsHomogeneous 2)
    (hdivides : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ), CubicIdentities P → ∀ (f : Vec 16)
      (Ψt : Fin 16 → MvPolynomial (Fin 16) ℝ) (Ct : Matrix (Fin 16) (Fin 16) ℝ),
      (∀ j, P j = formP f * Ψt j + sqP 16 * linP Ct j) → Ctᵀ = -Ct →
      formP f ∣ sqP 16 - (∑ j, linP Ct j ^ 2) ∧ sqP 16 - (∑ j, linP Ct j ^ 2) = quadP (1 + Ct * Ct))
    (horth : ∀ (S : Matrix (Fin 16) (Fin 16) ℝ), Sᵀ = -S → ∀ (f : Vec 16), f ≠ 0 →
      formP f ∣ quadP (1 + S * S) → 1 + S * S = 0 ∧ Sᵀ * S = 1)
    (hr2 : ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
      (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P 2 φ Ψ Cm →
      ∀ j, Ψ j = 0) :
    ∀ (P : Fin 16 → MvPolynomial (Fin 16) ℝ) (φ : MvPolynomial (Fin 16) ℝ)
      (Ψ : Fin 16 → MvPolynomial (Fin 16) ℝ) (Cm : Matrix (Fin 16) (Fin 16) ℝ), Lem82Lift P 1 φ Ψ Cm →
      ∀ j, sqP 16 ∣ Ψ j := by
  intro P φ Ψ Cm h j
  obtain ⟨f, hf, rfl⟩ := hform P φ Ψ Cm h
  obtain ⟨a, ha⟩ := hdiv P f Ψ Cm h
  obtain ⟨hdec, hCt, hΨt⟩ : (∀ j, P j = formP f * (Ψ j + sqP 16 * C (a j)) + sqP 16 * linP (Cm - vecMulVec a f) j) ∧
      (Cm - vecMulVec a f)ᵀ = -(Cm - vecMulVec a f) ∧ ∀ j, (Ψ j + sqP 16 * C (a j)).IsHomogeneous 2 :=
    hskew P f Ψ Cm h a ha
  obtain ⟨hd, hdeq⟩ := hdivides P h.2.1 f (fun j => Ψ j + sqP 16 * C (a j)) _ hdec hCt
  rw [hdeq] at hd
  obtain ⟨-, hCo⟩ := horth _ hCt f hf hd
  obtain ⟨-, B', hB'⟩ := lem_8_2_r1_factor_proved P h.2.1 f hf (fun j => Ψ j + sqP 16 * C (a j)) _ hdec hCt hCo hΨt
  have hL := lem_8_2_r1_to_r2_proved P h.1 h.2.1 f hf _ _ B' hdec hCt hCo hB'
  have hj : Ψ j + sqP 16 * C (a j) = bind₁ (linP (Cm - vecMulVec a f)) (formP f) * linP B' j := hB' j
  rw [hr2 P _ _ _ hL j, mul_zero] at hj
  exact ⟨-C (a j), by linear_combination hj⟩

end Osserman.Proofs.Lem82R1
