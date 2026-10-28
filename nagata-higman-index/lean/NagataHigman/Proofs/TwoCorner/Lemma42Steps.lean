/-
NagataHigman/Proofs/TwoCorner/Lemma42Steps.lean — the paper's own steps (a)-(d) of Lemma 4.2 (v1.02 tex 418-437), on `ν`,
for an arbitrary Young system: the projections `Q± = (1 ± Y_top)/2`, the operator `D = Q₊Y_kQ₊ + Q₋Y_kQ₋` with
`D v_T = g(c_T(k), c_T(top)) v_T`, `g(x, y) = x + 1/(y - x)`, the table of the four pairs, and `ρ(J_k), ρ(s) ∈ 𝒴`.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Indices: `k = N-2`, `top = N-1` (paper: `N-1`, `N`), `s = (k top)`, `Y_j = ρ(X^{(j)})`, `𝒴 = Algebra.adjoin F {Y_j}`.
Every operator here is diagonal in a Young basis except `ρ(s)`, so each step is a scalar identity on the four content
pairs `(c_T(k), c_T(top)) ∈ {(-1,1), (2,1), (1,-1), (-2,-1)}` (Tableaux.nu_contents). The general lemmas take the two
content facts `c_T(top)² = 1`, `c_T(k)² - c_T(k) c_T(top) = 2` as hypotheses (as Lemma42.eq_scalar_of_commute_stars);
the `ν` versions discharge them.
Step (d), as in short v1.03 (tex l. 484-490): on `ν`, `c_T(k)(c_T(top) - c_T(k)) = -2` for every `T` (the hypothesis
`hrel`), so `1/(c_T(top) - c_T(k)) = -c_T(k)/2` and `D v_T = ½ c_T(k) v_T`: `ρ(J_k) = 2 • D`
(`rhoAlg_jucysMurphy_eq_two_smul_stepD`). (`lem42g_table`, `lem42_values_nodup`: the old v1.02 table, no longer a claim.)
-/
import NagataHigman.Defs.TwoCornerSteps
import NagataHigman.Proofs.TwoCorner.Lemma42

noncomputable section

namespace NagataHigman.Proofs

open Equiv Finset Matrix NagataHigman

variable {F : Type*} [Field F] {N : ℕ}

section Steps

variable (Y : YoungSystem F N)

variable {lam : Shape N} (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F))

/-- A product of two matrices diagonal in `b` is diagonal, with the product eigenvalues. -/
theorem eigen_mul {A B : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F} {a c : SYT lam → F}
    (hA : ∀ T, A *ᵥ b T = a T • b T) (hB : ∀ T, B *ᵥ b T = c T • b T) (T : SYT lam) :
    (A * B) *ᵥ b T = (a T * c T) • b T := by
  rw [← Matrix.mulVec_mulVec, hB, Matrix.mulVec_smul, hA, smul_smul, mul_comm]

theorem Ytop_mulVec (hb : IsYoungBasis Y b) (top : Fin N) (htop : (top : ℕ) + 1 = N) (T : SYT lam) :
    Y.rhoAlg lam (starElem F top) *ᵥ b T = ((T.content top : ℤ) : F) • b T := by
  rw [starElem_top F top htop]
  exact hb T top

theorem projPlus_mulVec (hb : IsYoungBasis Y b) (top : Fin N) (htop : (top : ℕ) + 1 = N) (T : SYT lam) :
    projPlus Y lam top *ᵥ b T = ((1 + ((T.content top : ℤ) : F)) / 2) • b T := by
  rw [projPlus, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Ytop_mulVec Y b hb top htop]
  module

theorem projMinus_mulVec (hb : IsYoungBasis Y b) (top : Fin N) (htop : (top : ℕ) + 1 = N) (T : SYT lam) :
    projMinus Y lam top *ᵥ b T = ((1 - ((T.content top : ℤ) : F)) / 2) • b T := by
  rw [projMinus, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Ytop_mulVec Y b hb top htop]
  module

/-- **Lemma 4.2 (a)**: `Q₊, Q₋` are complementary idempotents (the projections onto the `±1`-eigenspaces of
`Y_top = ρ(J_top)`, i.e. onto the two blocks of the restriction to `S_{N-1}`). -/
theorem projPlus_projMinus [CharZero F] (hb : IsYoungBasis Y b) (top : Fin N) (htop : (top : ℕ) + 1 = N)
    (hy : ∀ T : SYT lam, T.content top ^ 2 = 1) :
    projPlus Y lam top * projPlus Y lam top = projPlus Y lam top ∧
      projMinus Y lam top * projMinus Y lam top = projMinus Y lam top ∧
      projPlus Y lam top * projMinus Y lam top = 0 ∧ projPlus Y lam top + projMinus Y lam top = 1 := by
  have hP := projPlus_mulVec Y b hb top htop
  have hM := projMinus_mulVec Y b hb top htop
  have hyF : ∀ T : SYT lam, ((T.content top : ℤ) : F) ^ 2 = 1 := fun T => by exact_mod_cast hy T
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply matrix_eq_of_basis Y b <;> intro T
  · rw [eigen_mul Y b hP hP, hP]
    congr 1
    linear_combination hyF T / 4
  · rw [eigen_mul Y b hM hM, hM]
    congr 1
    linear_combination hyF T / 4
  · rw [eigen_mul Y b hP hM, Matrix.zero_mulVec, ← zero_smul F (b T)]
    congr 1
    linear_combination -hyF T / 4
  · rw [Matrix.add_mulVec, hP, hM, Matrix.one_mulVec, ← add_smul]
    convert one_smul F (b T) using 2
    ring

/-- The `(T', T)` coordinate of `P Y_k P v_T` for `P` diagonal in `b`. -/
theorem repr_sandwich (P : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) (p : SYT lam → F)
    (hP : ∀ U, P *ᵥ b U = p U • b U) (A : Matrix (Fin (Y.dim lam)) (Fin (Y.dim lam)) F) (T T' : SYT lam) :
    b.repr ((P * A * P) *ᵥ b T) T' = p T' * p T * b.repr (A *ᵥ b T) T' := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP T, Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul,
    Finsupp.smul_apply, repr_mulVec_of_eigen Y b P p hP, smul_eq_mul]
  ring

/-- **Lemma 4.2 (c)**: `D v_T = g(c_T(k), c_T(top)) v_T`. -/
theorem stepD_mulVec [CharZero F] (hb : IsYoungBasis Y b) (k top : Fin N) (hk : (k : ℕ) + 1 = top)
    (htop : (top : ℕ) + 1 = N) (hy : ∀ T : SYT lam, T.content top ^ 2 = 1)
    (hrel : ∀ T : SYT lam, T.content k ^ 2 - T.content k * T.content top = 2) (T : SYT lam) :
    stepD Y lam k top *ᵥ b T = lem42g ((T.content k : ℤ) : F) ((T.content top : ℤ) : F) • b T := by
  apply b.repr.injective
  ext T'
  have hYk : Y.rhoAlg lam (starElem F k) = Y.rhoAlg lam (jucysMurphy F k) + Y.rho lam (swap k top) := by
    rw [starElem_eq_jucysMurphy_add k top hk htop, map_add, rhoAlg_perm]
  rw [stepD, Matrix.add_mulVec, map_add, Finsupp.add_apply,
    repr_sandwich Y b _ _ (projPlus_mulVec Y b hb top htop),
    repr_sandwich Y b _ _ (projMinus_mulVec Y b hb top htop), hYk, Matrix.add_mulVec, hb T k, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, Module.Basis.repr_self, map_smul, Finsupp.smul_apply,
    Module.Basis.repr_self, smul_eq_mul, smul_eq_mul]
  have hyF : ∀ U : SYT lam, ((U.content top : ℤ) : F) ^ 2 = 1 := fun U => by exact_mod_cast hy U
  rcases eq_or_ne T' T with rfl | hne
  · rw [Finsupp.single_eq_same]
    obtain ⟨-, hdiag⟩ := R_diag_general Y b hb T' k top hk.symm
    rw [hdiag, lem42g]
    push_cast
    linear_combination (((T'.content k : ℤ) : F) * 1 + 1 / (((T'.content top : ℤ) : F) -
      ((T'.content k : ℤ) : F))) * hyF T' / 2
  · rw [Finsupp.single_eq_of_ne hne, mul_zero, mul_zero, zero_add]
    by_cases hw0 : b.repr (Y.rho lam (swap k top) *ᵥ b T) T' = 0
    · rw [hw0]
      ring
    obtain ⟨hother, hpair⟩ := R_support_contents Y b hb T T' k top hk.symm hw0
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (syt_eq_of_content_eq fun i => by
        by_cases hik : i = k
        · rw [hik, h1]
        by_cases hit : i = top
        · rw [hit, h2]
        exact hother i hik hit) hne
    · have hxy : T.content k * T.content top = -1 := by
        have := hy T'
        rw [h2] at this
        linear_combination this - hrel T
      have hxyF : ((T.content k : ℤ) : F) * ((T.content top : ℤ) : F) = -1 := by exact_mod_cast hxy
      rw [h2]
      linear_combination b.repr (Y.rho lam (swap k top) *ᵥ b T) T' * hxyF / 2

/-- **Lemma 4.2 (d)** (l. 488-489): `c_T(k)(c_T(top) - c_T(k)) = -2` gives `D v_T = ½ c_T(k) v_T`, so `ρ(J_k) = 2 • D`. -/
theorem rhoAlg_jucysMurphy_eq_two_smul_stepD [CharZero F] (hb : IsYoungBasis Y b) (k top : Fin N)
    (hk : (k : ℕ) + 1 = top) (htop : (top : ℕ) + 1 = N) (hy : ∀ T : SYT lam, T.content top ^ 2 = 1)
    (hrel : ∀ T : SYT lam, T.content k ^ 2 - T.content k * T.content top = 2) :
    Y.rhoAlg lam (jucysMurphy F k) = (2 : F) • stepD Y lam k top := by
  apply matrix_eq_of_basis Y b
  intro T
  rw [hb T k, Matrix.smul_mulVec, stepD_mulVec Y b hb k top hk htop hy hrel T, smul_smul]
  congr 1
  obtain ⟨hne0, -⟩ := R_diag_general Y b hb T k top hk.symm
  have hrelF : ((T.content k : ℤ) : F) ^ 2 - ((T.content k : ℤ) : F) * ((T.content top : ℤ) : F) = 2 := by
    exact_mod_cast hrel T
  push_cast at hne0
  rw [lem42g]
  field_simp
  linear_combination hrelF

/-- **Lemma 4.2 (a)-(d)**, membership in `𝒴 = Algebra.adjoin F {Y_j}`: `Q±`, `D`, `ρ(J_k)` and `ρ(s)` lie in `𝒴`. -/
theorem steps_mem_adjoin [CharZero F] (hb : IsYoungBasis Y b) (k top : Fin N) (hk : (k : ℕ) + 1 = top)
    (htop : (top : ℕ) + 1 = N) (hy : ∀ T : SYT lam, T.content top ^ 2 = 1)
    (hrel : ∀ T : SYT lam, T.content k ^ 2 - T.content k * T.content top = 2) :
    let 𝒜 := Algebra.adjoin F (Set.range fun j : Fin N => Y.rhoAlg lam (starElem F j))
    projPlus Y lam top ∈ 𝒜 ∧ projMinus Y lam top ∈ 𝒜 ∧ stepD Y lam k top ∈ 𝒜 ∧
      Y.rhoAlg lam (jucysMurphy F k) ∈ 𝒜 ∧ Y.rho lam (swap k top) ∈ 𝒜 := by
  intro 𝒜
  have hY : ∀ j, Y.rhoAlg lam (starElem F j) ∈ 𝒜 := fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hP : projPlus Y lam top ∈ 𝒜 := Subalgebra.smul_mem _ (add_mem (one_mem _) (hY top)) _
  have hM : projMinus Y lam top ∈ 𝒜 := Subalgebra.smul_mem _ (sub_mem (one_mem _) (hY top)) _
  have hD : stepD Y lam k top ∈ 𝒜 :=
    add_mem (mul_mem (mul_mem hP (hY k)) hP) (mul_mem (mul_mem hM (hY k)) hM)
  have hJ : Y.rhoAlg lam (jucysMurphy F k) ∈ 𝒜 := by
    rw [rhoAlg_jucysMurphy_eq_two_smul_stepD Y b hb k top hk htop hy hrel]
    exact Subalgebra.smul_mem _ hD _
  refine ⟨hP, hM, hD, hJ, ?_⟩
  have hs : Y.rho lam (swap k top) = Y.rhoAlg lam (starElem F k) - Y.rhoAlg lam (jucysMurphy F k) := by
    rw [starElem_eq_jucysMurphy_add k top hk htop, map_add, rhoAlg_perm, add_sub_cancel_left]
  rw [hs]
  exact sub_mem (hY k) hJ

end Steps

/-- **Lemma 4.2 (d)**, the table (v1.02 tex 433-434): `g(-1,1) = -1/2`, `g(2,1) = 1`, `g(1,-1) = 1/2`, `g(-2,-1) = -1`. -/
theorem lem42g_table [CharZero F] :
    lem42g (-1 : F) 1 = -1 / 2 ∧ lem42g (2 : F) 1 = 1 ∧ lem42g (1 : F) (-1) = 1 / 2 ∧ lem42g (-2 : F) (-1) = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [lem42g] <;> norm_num

/-- **Lemma 4.2 (d)**: the four values `(c_T(top), g)` are pairwise distinct (v1.02 tex 435). -/
theorem lem42_values_nodup [CharZero F] :
    ([(1, -1 / 2), (1, 1), (-1, 1 / 2), (-1, -1)] : List (F × F)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false,
    not_false_eq_true, List.nodup_nil, and_true]
  norm_num

/-! ### The steps on `ν` (`n ≥ 2`, `N = n² - 1`, `k = N-2`, `top = N-1`) -/

section Nu

variable [CharZero F]

/-- The content facts of step (d) on `ν`, and `k + 1 = top`. -/
theorem nu_step_facts (n : ℕ) (hn : 2 ≤ n) (lam : Shape (n ^ 2 - 1)) (hlam : lam.InBox n)
    (top k : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) (hk : (k : ℕ) + 2 = n ^ 2 - 1) :
    (k : ℕ) + 1 = top ∧ (∀ T : SYT lam, T.content top ^ 2 = 1) ∧
      ∀ T : SYT lam, T.content k ^ 2 - T.content k * T.content top = 2 := by
  have hparts := sec_4_1_nu_proved n hn lam hlam
  refine ⟨by omega, fun T => ?_, fun T => nu_content_rel n hn lam hparts T top k htop hk⟩
  rcases nu_content_top n hn lam hparts T top htop with h | h <;> rw [h] <;> norm_num

/-- **Lemma 4.2 (a)** on `ν`: `Q± = (1 ± Y_top)/2` are complementary idempotents in `𝒴`. -/
theorem lem_4_2_a_nu (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (top k : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1)
    (hk : (k : ℕ) + 2 = n ^ 2 - 1) :
    projPlus Y lam top * projPlus Y lam top = projPlus Y lam top ∧
      projMinus Y lam top * projMinus Y lam top = projMinus Y lam top ∧
      projPlus Y lam top * projMinus Y lam top = 0 ∧ projPlus Y lam top + projMinus Y lam top = 1 ∧
      projPlus Y lam top ∈ Algebra.adjoin F (Set.range fun j => Y.rhoAlg lam (starElem F j)) ∧
      projMinus Y lam top ∈ Algebra.adjoin F (Set.range fun j => Y.rhoAlg lam (starElem F j)) := by
  obtain ⟨hk1, hy, hrel⟩ := nu_step_facts n hn lam hlam top k htop hk
  obtain ⟨b, hb⟩ := Y.youngBasis lam
  obtain ⟨h1, h2, h3, h4⟩ := projPlus_projMinus Y b hb top htop hy
  obtain ⟨h5, h6, -⟩ := steps_mem_adjoin Y b hb k top hk1 htop hy hrel
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- **Lemma 4.2 (a)** on `ν`, eigenspaces: in a Young basis, `Q₊` keeps `v_T` and `Q₋` kills it when
`c_T(top) = 1`, and the other way round when `c_T(top) = -1`. -/
theorem lem_4_2_a_nu_eigen (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F)) (hb : IsYoungBasis Y b)
    (top : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) (T : SYT lam) :
    (T.content top = 1 ∧ projPlus Y lam top *ᵥ b T = b T ∧ projMinus Y lam top *ᵥ b T = 0) ∨
      (T.content top = -1 ∧ projPlus Y lam top *ᵥ b T = 0 ∧ projMinus Y lam top *ᵥ b T = b T) := by
  rw [projPlus_mulVec Y b hb top htop, projMinus_mulVec Y b hb top htop]
  rcases nu_content_top n hn lam (sec_4_1_nu_proved n hn lam hlam) T top htop with h | h
  · left
    refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> norm_num
  · right
    refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> norm_num

/-- **Lemma 4.2 (c)** on `ν`: `D v_T = g(c_T(k), c_T(top)) v_T`, `g(x, y) = x + 1/(y - x)`. -/
theorem lem_4_2_c_nu (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (b : Module.Basis (SYT lam) F (Fin (Y.dim lam) → F)) (hb : IsYoungBasis Y b)
    (top k : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1) (hk : (k : ℕ) + 2 = n ^ 2 - 1) (T : SYT lam) :
    stepD Y lam k top *ᵥ b T = lem42g ((T.content k : ℤ) : F) ((T.content top : ℤ) : F) • b T := by
  obtain ⟨hk1, hy, hrel⟩ := nu_step_facts n hn lam hlam top k htop hk
  exact stepD_mulVec Y b hb k top hk1 htop hy hrel T

/-- **Lemma 4.2 (d)** on `ν`: the four content pairs, their values `(c_T(top), g)` (pairwise distinct:
`lem42_values_nodup`), the Lagrange step `ρ(J_k) = 2 • D`, and `ρ(J_k), ρ(s) ∈ 𝒴` with `s = (k top)`. -/
theorem lem_4_2_d_nu (n : ℕ) (hn : 2 ≤ n) (Y : YoungSystem F (n ^ 2 - 1)) (lam : Shape (n ^ 2 - 1))
    (hlam : lam.InBox n) (top k : Fin (n ^ 2 - 1)) (htop : (top : ℕ) + 1 = n ^ 2 - 1)
    (hk : (k : ℕ) + 2 = n ^ 2 - 1) :
    (∀ T : SYT lam, (T.content k, T.content top) ∈ ({(-1, 1), (2, 1), (1, -1), (-2, -1)} : Set (ℤ × ℤ))) ∧
      (∀ T : SYT lam, (((T.content top : ℤ) : F), lem42g ((T.content k : ℤ) : F) ((T.content top : ℤ) : F)) ∈
        ({(1, -1 / 2), (1, 1), (-1, 1 / 2), (-1, -1)} : Set (F × F))) ∧
      Y.rhoAlg lam (jucysMurphy F k) = (2 : F) • stepD Y lam k top ∧
      Y.rhoAlg lam (jucysMurphy F k) ∈ Algebra.adjoin F (Set.range fun j => Y.rhoAlg lam (starElem F j)) ∧
      Y.rho lam (swap k top) ∈ Algebra.adjoin F (Set.range fun j => Y.rhoAlg lam (starElem F j)) := by
  obtain ⟨hk1, hy, hrel⟩ := nu_step_facts n hn lam hlam top k htop hk
  have hparts := sec_4_1_nu_proved n hn lam hlam
  obtain ⟨b, hb⟩ := Y.youngBasis lam
  obtain ⟨-, -, -, h4, h5⟩ := steps_mem_adjoin Y b hb k top hk1 htop hy hrel
  refine ⟨fun T => nu_contents_mem n hn lam hparts T top k htop hk, fun T => ?_,
    rhoAlg_jucysMurphy_eq_two_smul_stepD Y b hb k top hk1 htop hy hrel, h4, h5⟩
  obtain ⟨ht1, ht2, ht3, ht4⟩ := lem42g_table (F := F)
  rcases nu_contents n hn lam hparts T top k htop hk with h | h | h | h <;> rw [h.1, h.2] <;> push_cast
  · rw [ht1]; simp
  · rw [ht2]; simp
  · rw [ht3]; simp
  · rw [ht4]; simp

end Nu

end NagataHigman.Proofs

end
