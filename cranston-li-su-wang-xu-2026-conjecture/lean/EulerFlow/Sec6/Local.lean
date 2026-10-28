/-
EulerFlow/Sec6/Local.lean — Section 6 of paper 002: Lemma 6.2 and Proposition 6.3 as the case q = 1 of Lemma 9.5
and Proposition 9.6 (the same argument with 1 in the place of q), and the small claims of tex l.524-527.
-/
import EulerFlow.Sec9.Prop96
import EulerFlow.Concrete.Small
import EulerFlow.Concrete.Dipole

namespace EulerFlow.MGraph.Sec6

open Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}

set_option linter.unusedSectionVars false

theorem cast_one_pm {m : ℕ} (x : ZMod m) : (x = ((1 : ℕ) : ZMod m) ∨ x = -((1 : ℕ) : ZMod m)) ↔ (x = 1 ∨ x = -1) := by
  simp

theorem lem_6_2_a_main (m : ℕ) (hm : 4 ≤ m) (f : E → ZMod m) (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = 1 ∨ f d.1 = -1) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) :
    dirVal f d = dirVal f (d'.1, !d'.2) ∧ (dirVal f d = 1 ∨ dirVal f d = -1) := by
  have h := Sec9.lem_9_5_a_main m 1 le_rfl (by omega) f hnb Q (fun d hd => (cast_one_pm _).mpr (hQ d hd))
    v d d' hd hd' hdv hd'v
  exact ⟨h.1, (cast_one_pm _).mp h.2⟩

/-- A residue other than `0, 1, -1` is in `J(m, 1)` = the residues of `2, …, m-2`. -/
theorem mem_Jpq_one {m : ℕ} (hm : 4 ≤ m) (x : ZMod m) (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ -1) :
    x ∈ Jpq m 1 := by
  haveI : NeZero m := ⟨by omega⟩
  have hlt := ZMod.val_lt x
  refine ⟨x.val, ?_, ?_, ZMod.natCast_zmod_val x⟩
  · by_contra hc
    push Not at hc
    rcases (show x.val = 0 ∨ x.val = 1 by omega) with hv | hv
    · exact h0 ((ZMod.val_eq_zero x).mp hv)
    · apply h1; rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_one]
  · by_contra hc
    push Not at hc
    have hv : x.val = m - 1 := by omega
    apply h2
    rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]

theorem lem_6_2_b_main (m : ℕ) (hm : 4 ≤ m) (f : E → ZMod m) (hf : G.IsNZFlow f)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle)
    (hQ : ∀ d ∈ Q.darts, f d.1 = 1 ∨ f d.1 = -1) (v : V) (d d' : E × Bool) (hd : d ∈ Q.darts)
    (hd' : d' ∈ Q.darts) (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (i : E × Bool)
    (hiv : G.endVertex i = v) (hid : i ≠ d) (hid' : i ≠ (d'.1, !d'.2))
    (hc : dirVal f i ≠ -(2 • dirVal f d)) :
    ∃ ts : List (ZMod m), G.StepsAlong {x | x ≠ 0} (Tcyc m) Q f ts ∧
      G.HasBalancedPairAt (f + fun e => Q.chi e • ts.sum) v := by
  obtain ⟨hI, hT⟩ := sec9_I_one_proved m (by omega)
  have hbal : dirVal f d + dirVal f i ≠ 0 := fun h0 => hnb ⟨v, d, i, Ne.symm hid, hdv, hiv, h0⟩
  have hc0 : dirVal f i ≠ 0 := by rw [Ne, dirVal_eq_zero_iff]; exact hf.2 _
  rw [two_nsmul] at hc
  have hJ : dirVal f d + dirVal f i ∈ Jpq m 1 := by
    apply mem_Jpq_one hm _ hbal
    · rcases Sec4.pm_dirVal f d (hQ d hd) with h | h <;> rw [h] at hc ⊢ <;> intro h'
      · exact hc0 (by linear_combination h')
      · exact hc (by linear_combination h')
    · rcases Sec4.pm_dirVal f d (hQ d hd) with h | h <;> rw [h] at hc ⊢ <;> intro h'
      · exact hc (by linear_combination h')
      · exact hc0 (by linear_combination h')
  have hf' : G.IsIFlow (Ipq m 1) f := by rw [hI]; exact hf
  obtain ⟨ts, hsteps, hb⟩ := Sec9.lem_9_5_b_main m 1 le_rfl (by omega) f hf' hnb Q
    (fun d hd => (cast_one_pm _).mpr (hQ d hd)) v d d' hd hd' hdv hd'v i hiv hid hid' hJ
  rw [hI, hT] at hsteps
  exact ⟨ts, hsteps, hb⟩

theorem prop_6_3_main (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (hE : Nonempty E) (hG : G.Loopless)
    (hdeg : ∀ v, G.degree v = 0 ∨ 4 ≤ G.degree v) (f : {f : E → ZMod m // G.IsNZFlow f}) :
    ∃ f' : {f : E → ZMod m // G.IsNZFlow f}, G.HasBalancedPair f'.1 ∧
      (G.tStepGraph (Tcyc m)).Reachable f f' :=
  Sec9.prop_9_6_gen m 1 le_rfl (by omega) {x | x ≠ 0} (Tcyc m) (sec9_I_one_proved m (by omega)).1.symm
    (sec9_I_one_proved m (by omega)).2.symm G hE hG hdeg f

/-- tex l.524-526: the value `-2a` (`a = ±1`) is not small in `ℤ_m`, `m ≥ 4`. -/
theorem neg_two_not_small (m : ℕ) (hm : 4 ≤ m) (a : ZMod m) (ha : a = 1 ∨ a = -1) :
    -(2 • a) ≠ 1 ∧ -(2 • a) ≠ -1 := by
  have h3 : (3 : ZMod m) ≠ 0 := by
    have : ((3 : ℕ) : ZMod m) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]; intro h; exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    simpa using this
  have h1 : (1 : ZMod m) ≠ 0 := by
    haveI : Fact (1 < m) := ⟨by omega⟩; exact one_ne_zero
  rw [two_nsmul]
  rcases ha with rfl | rfl <;> constructor <;> intro h
  · exact h3 (by linear_combination -h)
  · exact h1 (by linear_combination -h)
  · exact h1 (by linear_combination h)
  · exact h3 (by linear_combination h)

/-- Remark after Theorem 2.4 (tex l.525-527), with the flow having no balanced pair. -/
theorem remark_Z3Z3 (D : CyclicDecomp (ZMod 3 × ZMod 3)) (a : ZMod 3 × ZMod 3) (ha : a ∈ D.S) :
    -(2 • a) = a ∧ ∃ f : Fin 6 → ZMod 3 × ZMod 3, (dipole 6).IsNZFlow f ∧ ¬ (dipole 6).HasBalancedPair f ∧
      ∀ i : Fin 6 × Bool, (dipole 6).endVertex i = 0 → dirVal f i = a := by
  have ha0 : a ≠ 0 := by
    obtain ⟨k, hk | hk⟩ := ha
    · rw [hk]; exact D.s_ne k
    · rw [hk, neg_ne_zero]; exact D.s_ne k
  have h2a : a + a ≠ 0 := by
    intro h
    have : -(2 • a) = a := z3z3_neg_two a
    rw [two_nsmul, h, neg_zero] at this
    exact ha0 this.symm
  refine ⟨z3z3_neg_two a, fun _ => a, ⟨dipole_isFlow_const 6 a (z3z3_six a), fun _ => ha0⟩, ?_, ?_⟩
  · rintro ⟨v, i, j, -, hi, hj, hsum⟩
    obtain ⟨ei, bi⟩ := i
    obtain ⟨ej, bj⟩ := j
    fin_cases v <;> cases bi <;> cases bj <;> simp_all [dipole, endVertex, dirVal]
    all_goals first
      | exact h2a hsum
      | exact h2a (neg_eq_zero.mp (by rw [neg_add]; exact hsum))
  · rintro ⟨e, b⟩ hv
    cases b <;> simp_all [dipole, endVertex, dirVal]

end EulerFlow.MGraph.Sec6
