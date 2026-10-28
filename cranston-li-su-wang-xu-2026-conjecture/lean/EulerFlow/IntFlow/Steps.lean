/-
EulerFlow/IntFlow/Steps.lean — paper 002, Lemmas 8.5 and 8.6 (tex l.635-669): lifting a step with the value `1`
or `2`, and the remark after Lemma 8.6 (tex l.652).
The paper chooses reference directions along `Q`; here every edge keeps its own reference direction and `Q`
passes it with the sign `χ_Q(e) = ±1`. For Lemma 8.6 the rounded map is `x = (r_f + χ_Q)/k` (the paper's
`(r + χ_Q)/k`, now valid in any reference directions): it is `1` exactly on the forward edges with `r = k-1` and
`0` exactly on the backward edges with `r = 1`, which forces the lift there.
-/
import EulerFlow.IntFlow.Lift

namespace EulerFlow

namespace Sec8

open Finset MGraph

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- Membership in `Ik k` without absolute values. -/
lemma mem_Ik_iff (k y : ℤ) : y ∈ Ik k ↔ (1 ≤ y ∧ y ≤ k - 1) ∨ (1 - k ≤ y ∧ y ≤ -1) := by
  simp only [Ik, Set.mem_ofPred_eq]
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- If `a + j ≠ 0` in `ℤ_k`, then the representative of `a` is not `k - j`. -/
lemma val_ne_of_add_ne_zero {k : ℕ} {a : ZMod k} {j : ℕ} (hj : j ≤ k) (h : a + (j : ZMod k) ≠ 0)
    [NeZero k] : a.val ≠ k - j := by
  intro hv
  apply h
  rw [← ZMod.natCast_zmod_val a, hv, ← Nat.cast_add, Nat.sub_add_cancel hj, ZMod.natCast_self]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- If `a - j ≠ 0` in `ℤ_k`, then the representative of `a` is not `j`. -/
lemma val_ne_of_sub_ne_zero {k : ℕ} {a : ZMod k} {j : ℕ} (h : a - (j : ZMod k) ≠ 0) [NeZero k] :
    a.val ≠ j := by
  intro hv
  apply h
  rw [← ZMod.natCast_zmod_val a, hv, sub_self]

omit [Fintype E] [DecidableEq V] in
/-- On an edge of `Q`, `χ_Q` is `1` or `-1`, by the direction of the dart. -/
lemma chi_on_cycle (Q : G.DirCycle) {e : E} (he : e ∈ Q.darts.map Prod.fst) : Q.chi e = 1 ∨ Q.chi e = -1 := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
  rw [Q.chi_of_mem hd]
  cases d.2 <;> simp [dartSign]

/-- The lifted step map `F + j χ_Q` is an integer flow with the residues of `f + j χ_Q`. -/
lemma step_flow_res {k : ℕ} (Q : G.DirCycle) (f : E → ZMod k) (F : E → ℤ) (hF : G.IsIntLift k f F) (j : ℤ) :
    G.IsFlow (F + fun e => Q.chi e • j) ∧
      ∀ e, (((F + fun e => Q.chi e • j) e : ℤ) : ZMod k) = (f + fun e => Q.chi e • (j : ZMod k)) e := by
  refine ⟨IsFlow.add hF.1.1 (IsFlow.zsmul_const Q.isFlow_chi j), fun e => ?_⟩
  simp [hF.2 e]

/-- `lem_8_5` (Lemma 8.5, a step with the value `1`, tex l.635-646): for every integer lift `F` of `f`, the map
`F + χ_Q` is an integer lift of `f + χ_Q`. -/
theorem lem_8_5_proved [Fintype V] (k : ℕ) (hk : 2 ≤ k) (G : MGraph V E) (Q : G.DirCycle) (f : E → ZMod k)
    (hf : G.IsNZFlow f) (hf1 : G.IsNZFlow (f + fun e => Q.chi e • (1 : ZMod k))) (F : E → ℤ)
    (hF : G.IsIntLift k f F) :
    G.IsIntLift k (f + fun e => Q.chi e • (1 : ZMod k)) (F + fun e => Q.chi e • (1 : ℤ)) := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨hfl, hres⟩ := step_flow_res Q f F hF 1
  refine ⟨⟨hfl, fun e => ?_⟩, fun e => by simp [hF.2 e]⟩
  have hb := val_bounds hk (hf.2 e)
  have hFe := eq_val_or_val_sub hk (hf.2 e) (hF.1.2 e) (hF.2 e)
  have hne := hf1.2 e
  simp only [Pi.add_apply, smul_eq_mul, mul_one] at hne ⊢
  by_cases he : e ∈ Q.darts.map Prod.fst
  · rcases chi_on_cycle Q he with hc | hc <;> rw [hc] at hne ⊢
    · -- forward: `r ≠ k - 1`
      have hr : (f e).val ≠ k - 1 := val_ne_of_add_ne_zero (j := 1) (by omega) (by simpa using hne)
      rw [mem_Ik_iff]; omega
    · -- backward: `r ≠ 1`
      have hr : (f e).val ≠ 1 := val_ne_of_sub_ne_zero (j := 1) (by simpa [sub_eq_add_neg] using hne)
      rw [mem_Ik_iff]; omega
  · rw [Q.chi_of_not_mem he, add_zero]; exact hF.1.2 e

/-- `lem_8_6` (Lemma 8.6, a step with the value `2`, tex l.648-669): some integer lift `F` of `f` has
`F + 2χ_Q` an integer lift of `f + 2χ_Q`. Route: round `(r_f + χ_Q)/k` (Lemma 8.2) and take `F = r_f - k z`. -/
theorem lem_8_6_proved [Fintype V] (k : ℕ) (hk : 3 ≤ k) (G : MGraph V E) (Q : G.DirCycle) (f : E → ZMod k)
    (hf : G.IsNZFlow f) (hf2 : G.IsNZFlow (f + fun e => Q.chi e • (2 : ZMod k))) :
    ∃ F : E → ℤ, G.IsIntLift k f F ∧
      G.IsIntLift k (f + fun e => Q.chi e • (2 : ZMod k)) (F + fun e => Q.chi e • (2 : ℤ)) := by
  have hk2 : 2 ≤ k := by omega
  have : NeZero k := ⟨by omega⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set r : E → ℤ := fun e => ((f e).val : ℤ) with hr
  set x : E → ℝ := fun e => ((r e + Q.chi e : ℤ) : ℝ) / k with hx
  -- the facts per edge: `r ∈ [1, k-1]`, and on `Q` the forbidden representatives
  have hrb : ∀ e, 1 ≤ r e ∧ r e ≤ (k : ℤ) - 1 := by
    intro e; have := val_bounds hk2 (hf.2 e); simp only [hr]; omega
  have hfwd : ∀ e, Q.chi e = 1 → r e ≠ (k : ℤ) - 2 := by
    intro e hc
    have hne := hf2.2 e
    simp only [Pi.add_apply, hc, one_smul] at hne
    have := val_ne_of_add_ne_zero (j := 2) (by omega) (by simpa using hne)
    simp only [hr]; omega
  have hbwd : ∀ e, Q.chi e = -1 → r e ≠ 2 := by
    intro e hc
    have hne := hf2.2 e
    simp only [Pi.add_apply, hc, neg_smul, one_smul] at hne
    have := val_ne_of_sub_ne_zero (j := 2) (by simpa [sub_eq_add_neg] using hne)
    simp only [hr]; omega
  have hchi : ∀ e, Q.chi e = -1 ∨ Q.chi e = 0 ∨ Q.chi e = 1 := Q.chi_mem
  have hx01 : ∀ e, 0 ≤ x e ∧ x e ≤ 1 := by
    intro e
    have h1 : (0 : ℤ) ≤ r e + Q.chi e := by have := hrb e; rcases hchi e with h | h | h <;> omega
    have h2 : r e + Q.chi e ≤ (k : ℤ) := by have := hrb e; rcases hchi e with h | h | h <;> omega
    refine ⟨div_nonneg (by exact_mod_cast h1) hkpos.le, (div_le_one hkpos).2 (by exact_mod_cast h2)⟩
  have hbx : ∀ v, G.boundary x v = ((G.boundary r v : ℤ) : ℝ) / k := by
    intro v
    have hQ := Q.isFlow_chi v
    have hQr : (∑ e ∈ univ.filter (fun e => G.src e = v), (Q.chi e : ℝ)) =
        ∑ e ∈ univ.filter (fun e => G.tgt e = v), (Q.chi e : ℝ) := by exact_mod_cast hQ
    simp only [hx, boundary, ← Finset.sum_div, Int.cast_add, Finset.sum_add_distrib, Int.cast_sub,
      Int.cast_sum, hQr]
    ring
  have hint : ∀ v, ∃ n : ℤ, G.boundary x v = n := by
    intro v
    obtain ⟨c, hc⟩ := (sec8_rf_proved k hk2 G f hf).1 v
    refine ⟨c, ?_⟩
    rw [hbx, show G.boundary r v = G.boundary (fun e => ((f e).val : ℤ)) v from rfl, hc]
    push_cast
    field_simp
  obtain ⟨z, hz01, hzb, hzx⟩ := MGraph.rounding x hx01 hint
  have hkb : ∀ v, (k : ℤ) * G.boundary z v = G.boundary (fun e => ((f e).val : ℤ)) v := by
    intro v
    have := congr_fun hzb v
    rw [boundary_intCast, hbx] at this
    have h' : (((k : ℤ) * G.boundary z v : ℤ) : ℝ) = ((G.boundary r v : ℤ) : ℝ) := by
      push_cast; rw [this]; field_simp
    exact_mod_cast h'
  have hlift := isIntLift_of_round hk2 f hf z hz01 hkb
  refine ⟨_, hlift, ?_⟩
  obtain ⟨hfl, hres⟩ := step_flow_res Q f _ hlift 2
  refine ⟨⟨hfl, fun e => ?_⟩, fun e => by simp⟩
  simp only [Pi.add_apply, smul_eq_mul]
  have hb := hrb e
  rw [mem_Ik_iff]
  -- the forced values of `z`
  have hx1 : r e + Q.chi e = k → z e = 1 := by
    intro h
    apply (hzx e).2
    simp only [hx, h, Int.cast_natCast]; field_simp
  have hx0 : r e + Q.chi e = 0 → z e = 0 := by
    intro h
    apply (hzx e).1
    simp only [hx, h]; simp
  rcases hchi e with hc | hc | hc
  · have h2 := hbwd e hc
    rw [hc]
    rcases hz01 e with hz | hz
    · simp only [hr] at hb h2 hx1 hx0 ⊢; rw [hz]; omega
    · have hr1 : r e ≠ 1 := fun h => by have := hx0 (by rw [h, hc]; norm_num); omega
      simp only [hr] at hb h2 hr1 ⊢; rw [hz]; omega
  · rw [hc]
    have := (mem_Ik_iff _ _).1 (hlift.1.2 e)
    simpa using this
  · have h2 := hfwd e hc
    rw [hc]
    rcases hz01 e with hz | hz
    · have hrk : r e ≠ (k : ℤ) - 1 := fun h => by have := hx1 (by rw [h, hc]; ring); omega
      simp only [hr] at hb h2 hrk ⊢; rw [hz]; omega
    · simp only [hr] at hb h2 ⊢; rw [hz]; omega

end Sec8

end EulerFlow
