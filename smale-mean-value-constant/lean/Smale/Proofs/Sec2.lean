/-
Smale/Proofs/Sec2.lean — Section 2 of paper 009 (tex v1.90 l.134-175): Theorem 2.2 "Hence" and "Moreover", and
Remark 2.3 (the pair from a polynomial, the polynomial q = p(w)/w, the trivial pair W(w) = w, B = 1, and K* ≤ sup_k 𝓑_k).
The two outside results are the cited [JN, Prop. 4.2] and [JN, Prop. 3.1] (Smale/Cited/Basic.lean).
-/
import Smale.Cited.Basic

namespace Smale

open Polynomial

/-! ### Theorem 2.2, "Hence" (tex l.146-148) -/

/-- `m(p) ≤ K*` for every `p ∈ 𝓟_d`, `d ≥ 2` (the definitions of `K(d)` and `K*`, tex l.55). -/
theorem sec2_mval_le_Kstar {d : ℕ} (hd : 2 ≤ d) {p : ℂ[X]} (hp : IsPd d p) : ((mval p : ℝ) : EReal) ≤ Kstar :=
  (le_iSup (fun q : {q : ℂ[X] // IsPd d q} => ((mval q.1 : ℝ) : EReal)) ⟨p, hp⟩).trans
    (le_iSup (fun e : {e : ℕ // 2 ≤ e} => Kd e.1) ⟨d, hd⟩)

/-- Below a positive real `a`, every `c < a` lies below some real `A` with `0 < A < a`. -/
theorem sec2_exists_pos_real_btwn {c : EReal} {a : ℝ} (ha : 0 < a) (hc : c < (a : EReal)) :
    ∃ A : ℝ, c ≤ (A : EReal) ∧ 0 < A ∧ A < a := by
  obtain ⟨x, hcx, hxa⟩ := EReal.lt_iff_exists_real_btwn.mp hc
  refine ⟨max x (a / 2), hcx.le.trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)),
    lt_max_of_lt_right (half_pos ha), max_lt (EReal.coe_lt_coe_iff.mp hxa) (half_lt_self ha)⟩

/-- Theorem 2.2, "Hence" (tex l.148): `K* ≥ 1/B(0)` for every admissible pair (from [JN, Prop. 4.2]). -/
theorem thm_2_2_hence_proved (W B : ℂ → ℂ) (k : ℕ) (hWB : IsAdmissible W B k) :
    ((1 / (B 0).re : ℝ) : EReal) ≤ Kstar := by
  have hpos : 0 < 1 / (B 0).re := one_div_pos.mpr hWB.2.2.1.2
  refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
  obtain ⟨A, hcA, hA0, hAa⟩ := sec2_exists_pos_real_btwn hpos hc
  obtain ⟨d, hd, p, hp, hm⟩ := Cited.jatarNg_prop_4_2 W B k hWB A hA0 hAa
  exact hcA.trans ((EReal.coe_le_coe_iff.mpr hm.le).trans (sec2_mval_le_Kstar hd hp))

/-! ### Remark 2.3 (tex l.163-175) -/

/-- Remark 2.3 (tex l.163-171): for `p ∈ 𝓟_d` with `m(p) > 1` and `1 < R < m(p)` there is an admissible pair with
`1/B(0) = R` (the cited [JN, Prop. 3.1], without its degree bound). -/
theorem rem_2_3_pair_proved (d : ℕ) (hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) (hm : 1 < mval p) (R : ℝ) (hR1 : 1 < R)
    (hRm : R < mval p) : ∃ (W B : ℂ → ℂ) (k : ℕ), IsAdmissible W B k ∧ 1 / (B 0).re = R := by
  obtain ⟨W, B, k, -, -, hWB, hR⟩ := Cited.jatarNg_prop_3_1 d hd p hp hm R hR1 hRm
  exact ⟨W, B, k, hWB, hR⟩

/-- Remark 2.3 (tex l.164-165, l.169-170): `q = p(w)/w` is a polynomial (`p = X q`) with `q(0) = 1`, and every
critical point `β` of `p` has `|q(β)| ≥ m(p)`. -/
theorem rem_2_3_q_proved (d : ℕ) (_hd : 2 ≤ d) (p : ℂ[X]) (hp : IsPd d p) :
    p = X * (p /ₘ X) ∧ (p /ₘ X).eval 0 = 1 ∧ ∀ β : ℂ, p.derivative.eval β = 0 → mval p ≤ ‖(p /ₘ X).eval β‖ := by
  obtain ⟨-, h0, h1⟩ := hp
  have hX : X * (p /ₘ X) = p := by
    simpa using (mul_divByMonic_eq_iff_isRoot (p := p) (a := 0)).2 h0
  have hq0 : (p /ₘ X).eval 0 = 1 := by
    have h := congrArg (fun r => r.derivative.eval 0) hX
    simp only [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X, zero_mul, add_zero] at h
    rw [h, h1]
  refine ⟨hX.symm, hq0, fun β hβ => ?_⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [h1] at hβ
    exact one_ne_zero hβ
  have hpβ : p.eval β = β * (p /ₘ X).eval β := by
    conv_lhs => rw [← hX]
    rw [eval_mul, eval_X]
  have hmem : ‖p.eval β‖ / ‖β‖ ∈ critRatios p := ⟨β, hβ, rfl⟩
  have hbdd : BddBelow (critRatios p) := ⟨0, by rintro r ⟨γ, -, rfl⟩; positivity⟩
  have hle : sInf (critRatios p) ≤ ‖p.eval β‖ / ‖β‖ := csInf_le hbdd hmem
  rw [hpβ, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.2 hβ0)] at hle
  exact hle

/-- Remark 2.3 (tex l.171-172): `W(w) = w`, `B = 1` is an admissible pair with `deg B = 0`. -/
theorem sec2_trivial_admissible : IsAdmissible (fun w => w) (fun _ => 1) 0 := by
  refine ⟨⟨⟨differentiableOn_id, Set.injOn_id _⟩, rfl, by simp⟩, ⟨1, [], by simp, rfl, by simp, ?_⟩,
    ⟨by simp, by simp⟩, ?_⟩
  · intro w _
    simp [blaschkeProd]
  · intro w _
    simp

/-- `1/B(0) ≤ 𝓑_d` for an admissible pair with `deg B ≤ d`. -/
theorem sec2_le_Bcal {W B : ℂ → ℂ} {k d : ℕ} (hkd : k ≤ d) (hWB : IsAdmissible W B k) :
    ((1 / (B 0).re : ℝ) : EReal) ≤ Bcal d :=
  le_sSup ⟨W, B, k, hkd, hWB, rfl⟩

/-- Remark 2.3 (tex l.171-172): the pair `W(w) = w`, `B = 1` is admissible, so `𝓑_k ≥ 1` for every `k`. -/
theorem rem_2_3_trivial_proved : IsAdmissible (fun w => w) (fun _ => 1) 0 ∧ ∀ k : ℕ, (1 : EReal) ≤ Bcal k := by
  refine ⟨sec2_trivial_admissible, fun k => ?_⟩
  have h := sec2_le_Bcal (Nat.zero_le k) sec2_trivial_admissible
  simpa using h

/-- Remark 2.3 (tex l.169-172): `m(p) ≤ sup_k 𝓑_k` for every `p ∈ 𝓟_d` (by the pair from `p` with `R → m(p)` when
`m(p) > 1`, by the trivial pair when `m(p) ≤ 1`); hence `K* ≤ sup_k 𝓑_k`. -/
theorem rem_2_3_Kstar_le_proved :
    (∀ d : ℕ, 2 ≤ d → ∀ p : ℂ[X], IsPd d p → ((mval p : ℝ) : EReal) ≤ ⨆ k : ℕ, Bcal k) ∧
      Kstar ≤ ⨆ k : ℕ, Bcal k := by
  have h1 : (1 : EReal) ≤ ⨆ k : ℕ, Bcal k := (rem_2_3_trivial_proved.2 0).trans (le_iSup Bcal 0)
  have hm : ∀ d : ℕ, 2 ≤ d → ∀ p : ℂ[X], IsPd d p → ((mval p : ℝ) : EReal) ≤ ⨆ k : ℕ, Bcal k := by
    intro d hd p hp
    rcases le_or_gt (mval p) 1 with hle | hgt
    · exact (EReal.coe_le_coe_iff.mpr hle).trans h1
    · refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
      obtain ⟨x, hcx, hxm⟩ := EReal.lt_iff_exists_real_btwn.mp hc
      have hxm' : x < mval p := EReal.coe_lt_coe_iff.mp hxm
      obtain ⟨R, hR1, hRm⟩ : ∃ R : ℝ, max x 1 < R ∧ R < mval p := exists_between (max_lt hxm' hgt)
      obtain ⟨W, B, k, hWB, hR⟩ := rem_2_3_pair_proved d hd p hp hgt R ((le_max_right _ _).trans_lt hR1) hRm
      have hk : (R : EReal) ≤ Bcal k := by
        rw [← hR]
        exact sec2_le_Bcal le_rfl hWB
      calc c ≤ (x : EReal) := hcx.le
        _ ≤ (R : EReal) := EReal.coe_le_coe_iff.mpr ((le_max_left _ _).trans hR1.le)
        _ ≤ Bcal k := hk
        _ ≤ ⨆ k : ℕ, Bcal k := le_iSup Bcal k
  refine ⟨hm, ?_⟩
  unfold Kstar Kd
  exact iSup_le fun d => iSup_le fun p => hm d.1 d.2 p.1 p.2

/-! ### Theorem 2.2, "Moreover" (tex l.148) -/

/-- Theorem 2.2, "Moreover" (tex l.148; [JN, Thm. 1.2]): `K* = sup_d 𝓑_d`, from "Hence" and Remark 2.3. -/
theorem thm_2_2_moreover_proved : Kstar = ⨆ d : ℕ, Bcal d := by
  refine le_antisymm rem_2_3_Kstar_le_proved.2 (iSup_le fun d => ?_)
  unfold Bcal
  refine sSup_le ?_
  rintro x ⟨W, B, k, -, hWB, rfl⟩
  exact thm_2_2_hence_proved W B k hWB

end Smale
