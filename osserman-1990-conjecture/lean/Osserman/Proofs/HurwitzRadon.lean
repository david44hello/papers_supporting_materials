/-
Osserman/Proofs/HurwitzRadon.lean — Remark 7.2 of paper 013, the count "at most eight squares" (Hurwitz–Radon for
ℝ^16): a `Cl(ν)`-structure on `ℝ^16` has `ν ≤ 8` (row rem_7_2_nu_le_8, statement copied verbatim from
Osserman/Paper/Statements7.lean).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Proof. Suppose `ν ≥ 9` and take `J_0, …, J_8`. For a set `S` of indices let `J_S` be the product of the `J_k`, `k ∈ S`,
in increasing order. Conjugation `c_i(X) = -J_iXJ_i` is multiplicative, commutes with the transpose, keeps the trace,
fixes `J_i` and negates `J_k` (`k ≠ i`); so `c_i(J_S) = σ_i(S) J_S` with `σ_i(S) = ±1`. If `σ_i(S)σ_i(T) = -1` for some
`i`, then `c_i(J_SᵀJ_T) = -J_SᵀJ_T` and `tr(J_SᵀJ_T) = 0`. Writing `σ_i(S) = (-1)^{|S|}·(-1)^{[i ∈ S]}`, such an `i`
exists for all `S ≠ T` except complementary pairs. The 256 sets without `0`, and the full set, contain only one
complementary pair (full, empty), and `tr J_full = 0` since `J_full` is skew (`J_Sᵀ = ε_{|S|} J_S`, `ε_9 = -1`).
With `tr(J_SᵀJ_S) = 16` these 257 matrices are linearly independent in the 256-dimensional space of `16 × 16` matrices.
-/
import Osserman.Defs.Basic

namespace Osserman.Proofs.HurwitzRadon

open Osserman Matrix

abbrev M16 := Matrix (Fin 16) (Fin 16) ℝ

variable {J : Fin 9 → M16}

/-! ### The relations -/

lemma sq_neg_one (hJ : IsCliffordStr J) (i : Fin 9) : J i * J i = -1 := by
  have h := hJ.2 i i
  rw [ite_eq_left rfl] at h
  have h2 : (2 : ℝ) • (J i * J i) = (2 : ℝ) • (-1 : M16) := by
    rw [two_smul, h, smul_neg, two_smul, one_add_one_eq_two]
  exact smul_right_injective _ two_ne_zero h2

lemma anticomm (hJ : IsCliffordStr J) {i k : Fin 9} (hik : k ≠ i) : J i * J k = -(J k * J i) := by
  have h := hJ.2 i k
  rw [ite_eq_right (Ne.symm hik)] at h
  exact eq_neg_of_add_eq_zero_left h

lemma orth (hJ : IsCliffordStr J) (i : Fin 9) : (J i)ᵀ * J i = 1 := by
  rw [hJ.1 i, Matrix.neg_mul, sq_neg_one hJ, neg_neg]

/-! ### Conjugation by `J_i` -/

/-- `c_i(X) = -J_iXJ_i = J_i X J_i⁻¹`. -/
def cj (J : Fin 9 → M16) (i : Fin 9) (X : M16) : M16 := -(J i * X * J i)

lemma cj_mul (hJ : IsCliffordStr J) (i : Fin 9) (X Y : M16) : cj J i (X * Y) = cj J i X * cj J i Y := by
  have e : J i * X * J i * (J i * Y * J i) = J i * X * (J i * J i) * Y * J i := by
    simp only [Matrix.mul_assoc]
  simp only [cj, neg_mul_neg]
  rw [e, sq_neg_one hJ]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.mul_assoc]

lemma cj_one (hJ : IsCliffordStr J) (i : Fin 9) : cj J i 1 = 1 := by
  rw [cj, Matrix.mul_one, sq_neg_one hJ, neg_neg]

lemma cj_transpose (hJ : IsCliffordStr J) (i : Fin 9) (X : M16) : cj J i Xᵀ = (cj J i X)ᵀ := by
  simp only [cj, transpose_neg, transpose_mul, hJ.1 i, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

lemma trace_cj (hJ : IsCliffordStr J) (i : Fin 9) (X : M16) : (cj J i X).trace = X.trace := by
  rw [cj, trace_neg, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, sq_neg_one hJ, Matrix.mul_neg,
    Matrix.mul_one, trace_neg, neg_neg]

lemma cj_J (hJ : IsCliffordStr J) (i k : Fin 9) : cj J i (J k) = (if k = i then (1 : ℝ) else -1) • J k := by
  by_cases hk : k = i
  · subst hk
    rw [cj, sq_neg_one hJ, ite_eq_left rfl, one_smul, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  · rw [cj, anticomm hJ hk, Matrix.neg_mul, Matrix.mul_assoc, sq_neg_one hJ, Matrix.mul_neg, Matrix.mul_one,
      neg_neg, ite_eq_right hk, neg_one_smul]

/-! ### Products `J_l = ∏_{k ∈ l} J_k` -/

/-- The product of the `J_k` along the list `l`. -/
def P (J : Fin 9 → M16) (l : List (Fin 9)) : M16 := (l.map J).prod

/-- The sign of `c_i` on `J_l`. -/
def sg (i : Fin 9) (l : List (Fin 9)) : ℝ := (l.map fun k => if k = i then (1 : ℝ) else -1).prod

lemma cj_P (hJ : IsCliffordStr J) (i : Fin 9) (l : List (Fin 9)) : cj J i (P J l) = sg i l • P J l := by
  induction l with
  | nil => simp [P, sg, cj_one hJ]
  | cons k l ih =>
    simp only [P, sg, List.map_cons, List.prod_cons] at ih ⊢
    rw [cj_mul hJ, cj_J hJ, ih, smul_mul_smul_comm]

lemma P_orth (hJ : IsCliffordStr J) (l : List (Fin 9)) : (P J l)ᵀ * P J l = 1 := by
  induction l with
  | nil => simp [P]
  | cons k l ih =>
    simp only [P, List.map_cons, List.prod_cons] at ih ⊢
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (J k)ᵀ, orth hJ, Matrix.one_mul, ih]

/-- `σ_i(l) = (-1)^{|l|} · (-1)^{[i ∈ l]}` for a list without repetition. -/
lemma sg_eq (i : Fin 9) {l : List (Fin 9)} (hl : l.Nodup) :
    sg i l = (-1) ^ l.length * (if i ∈ l then -1 else 1) := by
  induction l with
  | nil => simp [sg]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2
    simp only [sg, List.map_cons, List.prod_cons] at ih' ⊢
    rw [ih', List.length_cons, pow_succ]
    by_cases hk : k = i
    · subst hk
      simp [hl.1]
    · have hmem : (i ∈ k :: l) ↔ i ∈ l := by
        simp [Ne.symm hk]
      simp only [hk, ite_false, hmem]
      ring

/-- The sign of the transpose: `ε_0 = 1`, `ε_{m+1} = -(-1)^m ε_m`. -/
def eps : ℕ → ℝ
  | 0 => 1
  | m + 1 => -((-1) ^ m * eps m)

lemma P_transpose (hJ : IsCliffordStr J) {l : List (Fin 9)} (hl : l.Nodup) : (P J l)ᵀ = eps l.length • P J l := by
  induction l with
  | nil => simp [P, eps]
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    have hsg : sg k l = (-1) ^ l.length := by rw [sg_eq k hl.2, ite_eq_right hl.1, mul_one]
    -- `-J_k J_l J_k = (-1)^{|l|} J_l`, so `J_l J_k = (-1)^{|l|} J_k J_l`
    have hc := cj_P hJ k l
    rw [hsg, cj] at hc
    have hswap : P J l * J k = ((-1 : ℝ) ^ l.length) • (J k * P J l) := by
      have e := congrArg (fun X => J k * X) hc
      simp only [Matrix.mul_neg, ← Matrix.mul_assoc, sq_neg_one hJ, Matrix.neg_mul, Matrix.one_mul, neg_neg,
        Matrix.mul_smul] at e
      exact e
    have hcons : P J (k :: l) = J k * P J l := by simp [P]
    rw [hcons, transpose_mul, ih hl.2, hJ.1 k, Matrix.smul_mul, Matrix.mul_neg, smul_neg, hswap, smul_smul,
      ← neg_smul, List.length_cons, eps, mul_comm]

/-! ### The 257 matrices -/

/-- The indices `k` with `f k`, in increasing order. -/
def lst (f : Fin 9 → Bool) : List (Fin 9) := (List.finRange 9).filter f

lemma lst_nodup (f : Fin 9 → Bool) : (lst f).Nodup := (List.nodup_finRange 9).filter f

lemma mem_lst (f : Fin 9 → Bool) (k : Fin 9) : k ∈ lst f ↔ f k = true := by
  simp [lst]

/-- `J_f = ∏_{f k} J_k`. -/
def V (J : Fin 9 → M16) (f : Fin 9 → Bool) : M16 := P J (lst f)

lemma trace_diag (hJ : IsCliffordStr J) (f : Fin 9 → Bool) : ((V J f)ᵀ * V J f).trace = 16 := by
  rw [V, P_orth hJ, trace_one, Fintype.card_fin]
  norm_num

/-- `tr(J_fᵀJ_g) = 0` when `c_i` has opposite signs on `J_f` and `J_g`. -/
lemma trace_off_of_sign (hJ : IsCliffordStr J) (f g : Fin 9 → Bool) (i : Fin 9)
    (hi : sg i (lst f) * sg i (lst g) = -1) : ((V J f)ᵀ * V J g).trace = 0 := by
  have e : cj J i ((V J f)ᵀ * V J g) = -((V J f)ᵀ * V J g) := by
    rw [cj_mul hJ, cj_transpose hJ, V, V, cj_P hJ, cj_P hJ, transpose_smul, smul_mul_smul_comm, hi, neg_one_smul]
  have t := trace_cj hJ i ((V J f)ᵀ * V J g)
  rw [e, trace_neg] at t
  linarith

/-- For `f ≠ g` that are not complementary, some `c_i` has opposite signs on `J_f` and `J_g`. -/
lemma exists_sign (f g : Fin 9 → Bool) (hfg : f ≠ g) (hc : ¬ ∀ k, g k = !f k) :
    ∃ i, sg i (lst f) * sg i (lst g) = -1 := by
  have hs : ∀ i, sg i (lst f) * sg i (lst g) =
      ((-1) ^ (lst f).length * (-1) ^ (lst g).length) * ((if f i then -1 else 1) * (if g i then -1 else 1)) := by
    intro i
    rw [sg_eq i (lst_nodup f), sg_eq i (lst_nodup g)]
    simp only [mem_lst]
    ring
  rcases neg_one_pow_eq_or ℝ ((lst f).length + (lst g).length) with h | h
  · obtain ⟨i, hi⟩ : ∃ i, ¬ f i = g i := not_forall.mp fun h => hfg (funext h)
    refine ⟨i, ?_⟩
    rw [hs, ← pow_add, h, one_mul]
    cases hf : f i <;> cases hg : g i <;> simp_all
  · obtain ⟨i, hi⟩ := not_forall.mp hc
    refine ⟨i, ?_⟩
    rw [hs, ← pow_add, h]
    cases hf : f i <;> cases hg : g i <;> simp_all

/-- `J_full` is skew, so its trace is zero. -/
lemma trace_full (hJ : IsCliffordStr J) : (V J fun _ => true).trace = 0 := by
  have hlen : (lst fun _ => true).length = 9 := by simp [lst]
  have hT := P_transpose hJ (lst_nodup fun _ => true)
  rw [hlen] at hT
  have he : eps 9 = -1 := by norm_num [eps]
  rw [he, neg_one_smul] at hT
  have t := trace_transpose (V J fun _ => true)
  rw [V, hT, trace_neg] at t
  rw [V]
  linarith

lemma V_empty (f : Fin 9 → Bool) (hf : ∀ k, f k = false) : V J f = 1 := by
  have h : lst f = [] := by
    rw [lst, List.filter_eq_nil_iff]
    intro k _
    simp [hf k]
  rw [V, h, P, List.map_nil, List.prod_nil]

/-- The index set: the 256 sets without `0` (`some h`), and the full set (`none`). -/
def emb : Option (Fin 8 → Bool) → (Fin 9 → Bool)
  | none => fun _ => true
  | some h => Fin.cons false h

lemma emb_zero_or (a : Option (Fin 8 → Bool)) : emb a 0 = false ∨ a = none := by
  cases a with
  | none => exact Or.inr rfl
  | some h => exact Or.inl rfl

lemma emb_injective : Function.Injective emb := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some h => exact absurd (congrFun hab 0) (by simp [emb])
  | some h =>
    cases b with
    | none => exact absurd (congrFun hab 0) (by simp [emb])
    | some h' => exact congrArg some (Fin.cons_right_injective (α := fun _ => Bool) false hab)

lemma trace_off (hJ : IsCliffordStr J) {a b : Option (Fin 8 → Bool)} (hab : a ≠ b) :
    ((V J (emb a))ᵀ * V J (emb b)).trace = 0 := by
  by_cases hc : ∀ k, emb b k = !emb a k
  · -- complementary: one of them is the full set, the other the empty set
    have h0 := hc 0
    rcases emb_zero_or a with ha | ha <;> rcases emb_zero_or b with hb | hb
    · rw [ha, hb] at h0
      exact absurd h0 (by decide)
    · subst hb
      have hfa : ∀ k, emb a k = false := fun k => by simpa [emb] using (hc k).symm
      rw [V_empty _ hfa, transpose_one, Matrix.one_mul, emb]
      exact trace_full hJ
    · subst ha
      have hfb : ∀ k, emb b k = false := fun k => by simpa [emb] using hc k
      rw [V_empty _ hfb, Matrix.mul_one, trace_transpose, emb]
      exact trace_full hJ
    · exact absurd (ha.trans hb.symm) hab
  · obtain ⟨i, hi⟩ := exists_sign (emb a) (emb b) (fun h => hab (emb_injective h)) hc
    exact trace_off_of_sign hJ _ _ i hi

lemma linIndep (hJ : IsCliffordStr J) : LinearIndependent ℝ fun a => V J (emb a) := by
  rw [linearIndependent_iff']
  intro s c hsum a ha
  have key := congrArg (fun X => ((V J (emb a))ᵀ * X).trace) hsum
  simp only [Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, Matrix.mul_zero,
    trace_zero] at key
  rw [Finset.sum_eq_single a (fun b _ hba => by rw [trace_off hJ (Ne.symm hba), mul_zero])
    (fun h => absurd ha h), trace_diag hJ] at key
  linarith

theorem rem_7_2_nu_le_8_proved {ν : ℕ} (Jα : Fin ν → Matrix (Fin 16) (Fin 16) ℝ) (hJ : IsCliffordStr Jα) :
    ν ≤ 8 := by
  by_contra hν
  have h9 : 9 ≤ ν := by omega
  let J : Fin 9 → M16 := fun k => Jα (Fin.castLE h9 k)
  have hJ9 : IsCliffordStr J := ⟨fun i => hJ.1 _, fun i j => by simpa [J] using hJ.2 (Fin.castLE h9 i) (Fin.castLE h9 j)⟩
  have hcard := (linIndep hJ9).fintype_card_le_finrank
  rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_option, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_fin] at hcard
  norm_num at hcard

end Osserman.Proofs.HurwitzRadon
