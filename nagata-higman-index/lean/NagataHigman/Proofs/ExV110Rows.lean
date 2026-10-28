/-
NagataHigman/Proofs/ExV110Rows.lean — three claims of short paper v1.10 of project 011 (Nagata–Higman index; FINAL tex
md5 23b0bd3e) that had no Lean statement yet:
§1 outline (i), "an element of the block I_(n^n) is determined by its coefficients on S_{N-1}" (v1.10 l. 189);
Lemma 4.1, proof, "These Z are the operators Q₊Z₁Q₊ + Q₋Z₂Q₋" (v1.10 l. 535-536); (F1), "L is the multilinear
component of (y_1+…+y_n)^n" (v1.10 l. 245); and three reasons new in rc3: step (3) "π₀⁻¹E_K = sgn(π₀)E_K" (l. 331),
step (7) "ℓ(λ) = λ'_1" (l. 388), the display of Lemma 4.2(d) (l. 571-573). Proofs in `NagataHigman.Proofs.ExV110Rows`,
statements in `NagataHigman.Paper`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import NagataHigman.Proofs.ExV110

universe u

noncomputable section

namespace NagataHigman.Proofs.ExV110Rows

open NagataHigman Equiv Finset Matrix

variable {F : Type*} [Field F] [CharZero F]

/-! ## N4-R1: an element of the block of the square is determined by its coefficients on `S_{N-1}` -/

/-- For `f, g` in the block `I_λ` of the square `λ = (n^n)`: if `f` and `g` agree on every permutation fixing the last
point, then `f = g` (Fourier inversion on the block, then `ρ_λ(S_{N-1})` spans all matrices, `lem_3_1_span`). -/
theorem square_determined_proved (n : ℕ) (hn : 1 ≤ n) (Y : YoungSystem F (n ^ 2)) (lam : Shape (n ^ 2))
    (hlam : lam.InBox n) (last : Fin (n ^ 2)) (hlast : (last : ℕ) + 1 = n ^ 2) (f g : GrpAlg F (n ^ 2))
    (hf : f ∈ Y.block lam) (hg : g ∈ Y.block lam)
    (hfg : ∀ σ : Perm (Fin (n ^ 2)), σ last = last → f.coeff σ = g.coeff σ) : f = g := by
  have hc : ((Y.dim lam : F) / ((n ^ 2).factorial : F)) ≠ 0 :=
    div_ne_zero (NagataHigman.Proofs.dim_ne_zero Y lam) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  have htr : ∀ σ : Perm (Fin (n ^ 2)), σ last = last →
      trace (Y.rho lam σ * (Y.rhoAlg lam f - Y.rhoAlg lam g)) = 0 := by
    intro σ hσ
    have hσ' : σ⁻¹ last = last := by
      rw [Perm.inv_eq_iff_eq]
      exact hσ.symm
    have h := hfg σ⁻¹ hσ'
    rw [NagataHigman.Proofs.YoungSystem.coeff_of_mem_block Y hf,
      NagataHigman.Proofs.YoungSystem.coeff_of_mem_block Y hg, inv_inv] at h
    rw [Matrix.mul_sub, Matrix.trace_sub, mul_left_cancel₀ hc h, sub_self]
  have hspan := NagataHigman.Proofs.lem_3_1_span_proved n hn Y lam hlam last hlast
  have hM : Y.rhoAlg lam f - Y.rhoAlg lam g = 0 := by
    apply NagataHigman.Proofs.YoungSystem.eq_zero_of_trace_mul
    intro E
    have hE : E ∈ Submodule.span F
        (Set.range fun σ : {σ : Perm (Fin (n ^ 2)) // σ last = last} => Y.rho lam σ.1) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Matrix.trace_mul_comm]
    induction hE using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨σ, rfl⟩ := hx
      exact htr σ.1 σ.2
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul r x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  apply NagataHigman.Proofs.YoungSystem.ext_of_rhoAlg Y
  intro mu
  by_cases hmu : mu = lam
  · subst hmu
    exact sub_eq_zero.1 hM
  · rw [(NagataHigman.Proofs.YoungSystem.mem_block_iff Y).1 hf mu hmu,
      (NagataHigman.Proofs.YoungSystem.mem_block_iff Y).1 hg mu hmu]

/-! ## N12-R1: the operators that commute with `Y_N` are the `Q₊Z₁Q₊ + Q₋Z₂Q₋` -/

section MatrixCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For an involution `Y`: `X` commutes with `Y` iff `X = Q₊Z₁Q₊ + Q₋Z₂Q₋` for some `Z₁, Z₂`. -/
theorem commutes_iff_blocks (Yt X : Matrix ι ι F) (hY : Yt * Yt = 1) :
    X * Yt = Yt * X ↔ ∃ Z₁ Z₂ : Matrix ι ι F, X = qP Yt * Z₁ * qP Yt + qM Yt * Z₂ * qM Yt := by
  constructor
  · intro hX
    refine ⟨X, X, ?_⟩
    have hXP : X * qP Yt = qP Yt * X := by
      rw [qP, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, hX]
    have hXM : X * qM Yt = qM Yt * X := by
      rw [qM, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, mul_one, one_mul, hX]
    have c1 : qP Yt * X * qM Yt = 0 := by rw [← hXP, mul_assoc, qP_mul_qM Yt hY, mul_zero]
    have c2 : qM Yt * X * qP Yt = 0 := by rw [← hXM, mul_assoc, qM_mul_qP Yt hY, mul_zero]
    calc X = (qP Yt + qM Yt) * X * (qP Yt + qM Yt) := by rw [qP_add_qM, one_mul, mul_one]
      _ = qP Yt * X * qP Yt + qP Yt * X * qM Yt + (qM Yt * X * qP Yt + qM Yt * X * qM Yt) := by
        simp only [add_mul, mul_add]
        abel
      _ = qP Yt * X * qP Yt + qM Yt * X * qM Yt := by rw [c1, c2, add_zero, zero_add]
  · rintro ⟨Z₁, Z₂, rfl⟩
    have hP1 : qP Yt * Yt = qP Yt := by rw [qP, smul_mul_assoc, add_mul, one_mul, hY, add_comm]
    have hM1 : qM Yt * Yt = -qM Yt := by rw [qM, smul_mul_assoc, sub_mul, one_mul, hY, ← smul_neg, neg_sub]
    have hP2 : Yt * qP Yt = qP Yt := Y_mul_qP Yt hY
    have hM2 : Yt * qM Yt = -qM Yt := Y_mul_qM Yt hY
    calc (qP Yt * Z₁ * qP Yt + qM Yt * Z₂ * qM Yt) * Yt
        = qP Yt * Z₁ * (qP Yt * Yt) + qM Yt * Z₂ * (qM Yt * Yt) := by simp only [add_mul, mul_assoc]
      _ = Yt * qP Yt * Z₁ * qP Yt + Yt * qM Yt * Z₂ * qM Yt := by
        rw [hP1, hM1, hP2, hM2]
        simp only [Matrix.mul_neg, Matrix.neg_mul]
      _ = Yt * (qP Yt * Z₁ * qP Yt + qM Yt * Z₂ * qM Yt) := by simp only [mul_add, mul_assoc]

end MatrixCore

/-- On `ν`: the span of the `ρ(σ)`, `σ ∈ Stab(N)`, is the set of the `Q₊Z₁Q₊ + Q₋Z₂Q₋` (`lem_4_1_span` and
`Y_N² = 1`). -/
theorem Z_form_proved (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (top : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1)
    (Z : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) :
    Z ∈ Submodule.span F
        ((Y.rho lam : Perm (Fin (n ^ 2 - 1)) → Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) '' stab top) ↔
      ∃ Z₁ Z₂ : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F,
        Z = projPlus Y lam top * Z₁ * projPlus Y lam top + projMinus Y lam top * Z₂ * projMinus Y lam top := by
  have hJ := NagataHigman.Proofs.starElem_top F top htop
  have hYs : Y.rhoAlg lam (starElem F top) * Y.rhoAlg lam (starElem F top) = 1 := by
    rw [hJ]
    exact NagataHigman.Proofs.jucysMurphy_top_sq_nu n hn Y lam hlam top htop
  rw [NagataHigman.Proofs.restriction_of_young Y lam top htop Z, ← hJ]
  exact commutes_iff_blocks _ Z hYs

/-! ## N5-R1: `L` is the multilinear part of `(x_1 + … + x_n)^n` -/

omit [CharZero F] in
/-- `(x_0 + … + x_{n-1})^n = L + (the words in which some letter repeats)`. -/
theorem L_multilinear_part_proved (n : ℕ) :
    nuPow (∑ i : Fin n, letter F i) n =
      symSum n (fun i => letter F i) +
        ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin n => ¬ Function.Bijective w),
          tupleProd n (fun k => letter F (w k)) := by
  classical
  have hexp := NagataHigman.Proofs.nuPow_finset_sum_eq n (fun i : Fin n => letter F i) Finset.univ
  simp only [Finset.mem_univ, implies_true, ↓reduceIte] at hexp
  rw [hexp, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : Fin n → Fin n => Function.Bijective w)]
  congr 1
  rw [Finset.sum_filter]
  have hbs : ∀ w : Fin n → Fin n, Function.Bijective w ↔ Function.Surjective w := fun w =>
    ⟨fun h => h.2, fun h => ⟨Finite.injective_iff_surjective.2 h, h⟩⟩
  refine (Finset.sum_congr rfl fun w _ => if_congr (hbs w) rfl rfl).trans ?_
  exact NagataHigman.Proofs.sum_surjective_eq_sum_perm n (fun w => tupleProd n (fun k => letter F (w k)))

/-! ## c5: the display of Lemma 4.2(d) -/

/-- On `ν`: `c_T(N-1) + 1/(c_T(N) - c_T(N-1)) = c_T(N-1) - c_T(N-1)/2 = ½ c_T(N-1)`, from the content relation
`c_T(N-1)² - c_T(N-1) c_T(N) = 2` (`nu_content_rel`, tableau combinatorics only). -/
theorem d_display_proved (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n)
    (top k : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) (hk : (k : ℕ) + 2 = n ^ 2 - 1) (T : SYT lam) :
    ((T.content k : ℤ) : F) + 1 / (((T.content top : ℤ) : F) - ((T.content k : ℤ) : F)) =
        ((T.content k : ℤ) : F) - ((T.content k : ℤ) : F) / 2 ∧
      ((T.content k : ℤ) : F) - ((T.content k : ℤ) : F) / 2 = (1 / 2 : F) * ((T.content k : ℤ) : F) := by
  have hrel := NagataHigman.Proofs.nu_content_rel n hn lam (NagataHigman.Proofs.sec_4_1_nu_proved n hn lam hlam) T
    top k htop hk
  have hrelF : ((T.content k : ℤ) : F) ^ 2 - ((T.content k : ℤ) : F) * ((T.content top : ℤ) : F) = 2 := by
    exact_mod_cast hrel
  generalize ((T.content k : ℤ) : F) = c at hrelF ⊢
  generalize ((T.content top : ℤ) : F) = c' at hrelF ⊢
  have hne : c' - c ≠ 0 := by
    intro h
    rw [sub_eq_zero.1 h] at hrelF
    have h0 : (2 : F) = 0 := by
      rw [← hrelF]
      ring
    exact two_ne_zero h0
  have h1 : 1 / (c' - c) = -(c / 2) := by
    rw [div_eq_iff hne]
    linear_combination (-1 / 2 : F) * hrelF
  refine ⟨?_, by ring⟩
  rw [h1]
  ring

end NagataHigman.Proofs.ExV110Rows

end
