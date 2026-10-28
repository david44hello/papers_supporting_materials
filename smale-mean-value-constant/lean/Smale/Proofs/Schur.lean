/-
Smale/Proofs/Schur.lean — the reversed polynomial `f*` and Lemma 4.2 (Schur–Cohn) of paper 009 (tex l.252-271):
`|f*| = |f|` on the circle; `Tf` has formal degree `n - 1` and constant term `|e₀|² - |e_n|²`; if `|e₀| > |e_n|`, `f`
and `Tf` have the same zeros on the circle and the same number in `𝔻` (by Rouché for polynomials,
`Smale/Proofs/ArgPrinciple.lean`); if all `δ_j > 0`, `f` has no zero in `𝔻̄`.
-/
import Smale.Proofs.ArgPrinciple

namespace Smale

open Polynomial Complex Metric ComplexConjugate

theorem coeff_conjRev (f : ℂ[X]) (n m : ℕ) :
    (conjRev f n).coeff m = if m < n + 1 then conj (f.coeff (n - m)) else 0 := by
  simp only [conjRev, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]

/-- The value of `f*` at `w`, reindexed: `Σ_j ē_j w^{n-j}`. -/
theorem eval_conjRev (f : ℂ[X]) (n : ℕ) (w : ℂ) :
    (conjRev f n).eval w = ∑ j ∈ Finset.range (n + 1), conj (f.coeff j) * w ^ (n - j) := by
  simp only [conjRev, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [show n + 1 - 1 - j = n - j by omega, Nat.sub_sub_self hj']

theorem pow_mul_conj_pow {w : ℂ} (hw : conj w * w = 1) (j k : ℕ) : w ^ (j + k) * conj w ^ k = w ^ j := by
  rw [pow_add, mul_assoc, ← mul_pow, mul_comm w, hw, one_pow, mul_one]

theorem conj_mul_self_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : conj w * w = 1 := by
  rw [Complex.conj_mul', hw]
  simp

/-- On the circle, `f*(w) = wⁿ · conj(f(w))` (tex l.254-255). -/
theorem conjRev_eval_circle (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) {w : ℂ} (hw : conj w * w = 1) :
    (conjRev f n).eval w = w ^ n * conj (f.eval w) := by
  rw [eval_conjRev, eval_eq_sum_range' (Nat.lt_succ_of_le hn), map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hpow : w ^ n * conj w ^ j = w ^ (n - j) := by
    have h := pow_mul_conj_pow hw (n - j) j
    rwa [Nat.sub_add_cancel hj'] at h
  rw [map_mul, map_pow, ← hpow]
  ring

/-- tex l.255, exactly the Statements type: on the circle `|f*| = |f|`. -/
theorem sec4_conjRev_circle_proved (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖(conjRev f n).eval w‖ = ‖f.eval w‖ := by
  rw [conjRev_eval_circle f n hn (conj_mul_self_of_norm_eq_one hw), norm_mul, norm_pow, hw, one_pow, one_mul,
    Complex.norm_conj]

theorem coeff_schurT (f : ℂ[X]) (n m : ℕ) :
    (schurT f n).coeff m = conj (f.coeff 0) * f.coeff m - f.coeff n * (conjRev f n).coeff m := by
  rw [schurT, coeff_sub, coeff_C_mul, coeff_C_mul]

/-- Lemma 4.2 (tex l.258-259), exactly the Statements type: `Tf` has formal degree `n - 1` and constant term
`|e₀|² - |e_n|²`. -/
theorem lem_4_2_T_proved (f : ℂ[X]) (n : ℕ) (_hn1 : 1 ≤ n) (hn : f.natDegree ≤ n) :
    (schurT f n).natDegree ≤ n - 1 ∧ (schurT f n).coeff 0 = ((‖f.coeff 0‖ ^ 2 - ‖f.coeff n‖ ^ 2 : ℝ) : ℂ) := by
  constructor
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_schurT, coeff_conjRev]
    rcases Nat.lt_or_ge n N with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hn h)]
      simp [show ¬ N < n + 1 by omega]
    · obtain rfl : N = n := by omega
      rw [ite_eq_left (Nat.lt_succ_self _), Nat.sub_self]
      ring
  · rw [coeff_schurT, coeff_conjRev, ite_eq_left (Nat.succ_pos _), Nat.sub_zero, Complex.conj_mul', Complex.mul_conj']
    push_cast
    ring

/-- Lemma 4.2, first claim (tex l.259-260), exactly the Statements type: if `|e₀| > |e_n|`, `f` and `Tf` have the
same zeros on the circle and, if `f` has none there, the same number of zeros in `𝔻` (Rouché for polynomials). -/
theorem lem_4_2_a_proved (f : ℂ[X]) (n : ℕ) (_hn1 : 1 ≤ n) (hn : f.natDegree ≤ n)
    (hlt : ‖f.coeff n‖ < ‖f.coeff 0‖) :
    (∀ w : ℂ, ‖w‖ = 1 → (f.eval w = 0 ↔ (schurT f n).eval w = 0)) ∧
      ((∀ w : ℂ, ‖w‖ = 1 → f.eval w ≠ 0) → zerosInDisk (schurT f n) = zerosInDisk f) := by
  have hT : ∀ w : ℂ, ‖w‖ = 1 →
      (schurT f n).eval w = conj (f.coeff 0) * f.eval w - f.coeff n * (w ^ n * conj (f.eval w)) := by
    intro w hw
    rw [schurT, eval_sub, eval_mul, eval_mul, eval_C, eval_C,
      conjRev_eval_circle f n hn (conj_mul_self_of_norm_eq_one hw)]
  refine ⟨fun w hw => ⟨fun h0 => ?_, fun h0 => ?_⟩, fun hc => ?_⟩
  · rw [hT w hw, h0]
    simp
  · by_contra hne
    have h1 : conj (f.coeff 0) * f.eval w = f.coeff n * (w ^ n * conj (f.eval w)) := by
      rw [hT w hw] at h0
      exact sub_eq_zero.1 h0
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hw, one_pow, one_mul, Complex.norm_conj, Complex.norm_conj] at h2
    have hpos : 0 < ‖f.eval w‖ := norm_pos_iff.2 hne
    nlinarith
  · have he0' : f.coeff 0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hlt
      exact (norm_nonneg _).not_gt hlt
    have he0 : conj (f.coeff 0) ≠ 0 := by simpa using he0'
    have hsplit : schurT f n = C (conj (f.coeff 0)) * f + -(C (f.coeff n) * conjRev f n) := by
      rw [schurT, sub_eq_add_neg]
    rw [hsplit, zerosInDisk_add_of_norm_lt]
    · simp only [zerosInDisk_eq, roots_C_mul _ he0]
    · intro w hw
      simp only [eval_neg, norm_neg, eval_mul, eval_C]
      rw [norm_mul, sec4_conjRev_circle_proved f n hn w hw, norm_mul, Complex.norm_conj]
      exact mul_lt_mul_of_pos_right hlt (norm_pos_iff.2 (hc w hw))

/-- `f_j` has formal degree `n - j`. -/
theorem natDegree_schurSeq_le (f : ℂ[X]) (n : ℕ) (hn : f.natDegree ≤ n) :
    ∀ j, j ≤ n → (schurSeq f n j).natDegree ≤ n - j := by
  intro j
  induction j with
  | zero =>
    intro _
    show f.natDegree ≤ n - 0
    omega
  | succ j ih =>
    intro hj
    have h := (lem_4_2_T_proved (schurSeq f n j) (n - j) (by omega) (ih (by omega))).1
    show (schurT (schurSeq f n j) (n - j)).natDegree ≤ n - (j + 1)
    omega

/-- The step `j ↦ j - 1` of the proof (tex l.266-270): `f_j = T f_{j-1}`, here with `j = n - i`. -/
theorem schurSeq_succ_eq (f : ℂ[X]) (n i : ℕ) (hi : i + 1 ≤ n) :
    schurSeq f n (n - i) = schurT (schurSeq f n (n - (i + 1))) (i + 1) := by
  rw [show n - i = n - (i + 1) + 1 by omega]
  show schurT (schurSeq f n (n - (i + 1))) (n - (n - (i + 1))) = _
  rw [show n - (n - (i + 1)) = i + 1 by omega]

/-- Lemma 4.2, "Consequently" (tex l.260-261, proof l.264-270), exactly the Statements type: if `δ₁, …, δ_n` are all
positive, `f` has no zero in `𝔻̄`. -/
theorem lem_4_2_b_proved (f : ℂ[X]) (n : ℕ) (hn1 : 1 ≤ n) (hn : f.natDegree ≤ n)
    (hδ : ∀ j, 1 ≤ j → j ≤ n → (schurDelta f n j).im = 0 ∧ 0 < (schurDelta f n j).re) :
    ∀ w ∈ closedDisk, f.eval w ≠ 0 := by
  have hdeg := natDegree_schurSeq_le f n hn
  have key : ∀ i, i ≤ n → (∀ w : ℂ, ‖w‖ = 1 → (schurSeq f n (n - i)).eval w ≠ 0) ∧
      zerosInDisk (schurSeq f n (n - i)) = 0 := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      have h0 := hdeg n le_rfl
      rw [Nat.sub_self] at h0
      have hc : schurSeq f n n = C (schurDelta f n n) := eq_C_of_natDegree_le_zero h0
      have hδn := (hδ n hn1 le_rfl).2
      have hne : schurDelta f n n ≠ 0 := fun h => by
        rw [h, zero_re] at hδn
        exact lt_irrefl _ hδn
      rw [hc]
      exact ⟨fun w _ => by rw [eval_C]; exact hne, by simp [zerosInDisk_eq]⟩
    | succ i ih =>
      intro hi
      obtain ⟨hc, hz⟩ := ih (by omega)
      have hdeg' := hdeg (n - (i + 1)) (by omega)
      rw [show n - (n - (i + 1)) = i + 1 by omega] at hdeg'
      have hT := schurSeq_succ_eq f n i hi
      have hTd := lem_4_2_T_proved (schurSeq f n (n - (i + 1))) (i + 1) (by omega) hdeg'
      have hδi := (hδ (n - i) (by omega) (by omega)).2
      rw [schurDelta, hT, hTd.2, ofReal_re] at hδi
      have hlt : ‖(schurSeq f n (n - (i + 1))).coeff (i + 1)‖ < ‖(schurSeq f n (n - (i + 1))).coeff 0‖ :=
        (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (sub_pos.1 hδi)
      have ha := lem_4_2_a_proved _ (i + 1) (by omega) hdeg' hlt
      rw [hT] at hc hz
      have hgc : ∀ w : ℂ, ‖w‖ = 1 → (schurSeq f n (n - (i + 1))).eval w ≠ 0 := fun w hw h0 =>
        hc w hw ((ha.1 w hw).1 h0)
      exact ⟨hgc, by rw [← ha.2 hgc]; exact hz⟩
  obtain ⟨hc, hz⟩ := key n le_rfl
  rw [Nat.sub_self] at hc hz
  change ∀ w : ℂ, ‖w‖ = 1 → f.eval w ≠ 0 at hc
  change zerosInDisk f = 0 at hz
  intro w hw h0
  rcases (mem_closedBall_zero_iff.1 hw).lt_or_eq with hlt | heq
  · have hmem : w ∈ f.roots.filter fun w => ‖w‖ < 1 :=
      Multiset.mem_filter.2 ⟨(mem_roots (ne_zero_of_circle hc)).2 h0, hlt⟩
    rw [zerosInDisk_eq, Multiset.card_eq_zero] at hz
    rw [hz] at hmem
    exact Multiset.notMem_zero _ hmem
  · exact hc w heq h0

end Smale
