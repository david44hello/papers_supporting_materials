/-
EulerFlow/Sec4/Local.lean — the local step for every group on graphs with all degrees 0 or 4 (paper 002, Section 4):
Lemma 4.3 (Case 1 / Case 2 and the step (∗)), with the algebraic facts on parts taken as hypotheses (proved in
Sec4/Decomp.lean).
-/
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow.MGraph.Sec4

open Finset

variable {V E : Type} [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}

set_option linter.unusedSectionVars false

/-! ### Flows: linearity, Kirchhoff (eq. 2.1) -/

theorem isFlow_add {A : Type} [AddCommGroup A] {x y : E → A} (hx : G.IsFlow x) (hy : G.IsFlow y) :
    G.IsFlow (x + y) := by
  intro v; simp only [Pi.add_apply, Finset.sum_add_distrib, hx v, hy v]

theorem isFlow_chi_smul {A : Type} [AddCommGroup A] (Q : G.DirCycle) (t : A) :
    G.IsFlow (fun e => Q.chi e • t) := by
  intro v
  have h := Q.isFlow_chi v
  simp only [← Finset.sum_smul, h]

theorem isFlow_step {A : Type} [AddCommGroup A] {f : E → A} (hf : G.IsFlow f) (Q : G.DirCycle) (t : A) :
    G.IsFlow (f + fun e => Q.chi e • t) := isFlow_add hf (isFlow_chi_smul Q t)

/-- A step from a nowhere-zero flow is a nowhere-zero flow iff every dart value along `Q`, plus `t`, is non-zero. -/
theorem isNZFlow_step_iff {A : Type} [AddCommGroup A] {f : E → A} (hf : G.IsNZFlow f) (Q : G.DirCycle) (t : A) :
    G.IsNZFlow (f + fun e => Q.chi e • t) ↔ ∀ d ∈ Q.darts, dirVal f d + t ≠ 0 := by
  constructor
  · intro h
    exact ((Q.ne_zero_step_iff f t).mp h.2).2
  · intro h
    exact ⟨isFlow_step hf.1 Q t, (Q.ne_zero_step_iff f t).mpr ⟨fun e _ => hf.2 e, h⟩⟩

/-- Kirchhoff in outward values (eq. 2.1, tex l.157-159): the outward values at a vertex sum to `0`. -/
theorem kirchhoff [Fintype V] {A : Type} [AddCommGroup A] {f : E → A} (hf : G.IsFlow f) (v : V) :
    ∑ i ∈ univ.filter (fun i : E × Bool => G.endVertex i = v), dirVal f i = 0 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, endVertex, dirVal]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  have h := hf v
  rw [Finset.sum_filter, Finset.sum_filter] at h
  rw [Finset.sum_add_distrib]
  have : ∑ x : E, (if G.tgt x = v then -f x else 0) = -∑ x : E, (if G.tgt x = v then f x else 0) := by
    rw [← Finset.sum_neg_distrib]; congr 1; ext x; split_ifs <;> simp
  rw [this, h]; abel

/-! ### The four ends at a vertex of degree 4 -/

/-- At a vertex of degree `4`, two given different ends `i₁, i₂` are completed by two more ends `i₃, i₄`, all four
different, and `y₁ + y₂ + y₃ + y₄ = 0`. -/
theorem four_ends [Fintype V] {A : Type} [AddCommGroup A] {f : E → A} (hf : G.IsFlow f) {v : V}
    (hdeg : G.degree v = 4) {i₁ i₂ : E × Bool} (h₁ : G.endVertex i₁ = v) (h₂ : G.endVertex i₂ = v)
    (h₁₂ : i₁ ≠ i₂) :
    ∃ i₃ i₄ : E × Bool, G.endVertex i₃ = v ∧ G.endVertex i₄ = v ∧ i₃ ≠ i₁ ∧ i₃ ≠ i₂ ∧ i₄ ≠ i₁ ∧ i₄ ≠ i₂ ∧
      i₃ ≠ i₄ ∧ dirVal f i₁ + dirVal f i₂ + dirVal f i₃ + dirVal f i₄ = 0 := by
  set F := univ.filter (fun i : E × Bool => G.endVertex i = v) with hF
  have hcard : F.card = 4 := hdeg
  have m₁ : i₁ ∈ F := by simp [hF, h₁]
  have m₂ : i₂ ∈ (F.erase i₁) := by simp [hF, h₂, Ne.symm h₁₂]
  have hc2 : ((F.erase i₁).erase i₂).card = 2 := by
    rw [Finset.card_erase_of_mem m₂, Finset.card_erase_of_mem m₁, hcard]
  obtain ⟨i₃, i₄, h34, hset⟩ := Finset.card_eq_two.mp hc2
  have m₃ : i₃ ∈ (F.erase i₁).erase i₂ := by rw [hset]; simp
  have m₄ : i₄ ∈ (F.erase i₁).erase i₂ := by rw [hset]; simp
  simp only [Finset.mem_erase, hF, Finset.mem_filter, Finset.mem_univ, true_and] at m₃ m₄
  refine ⟨i₃, i₄, m₃.2.2, m₄.2.2, m₃.2.1, m₃.1, m₄.2.1, m₄.1, h34, ?_⟩
  have hFeq : F = insert i₁ (insert i₂ {i₃, i₄}) := by
    rw [← hset, Finset.insert_erase m₂, Finset.insert_erase m₁]
  have hk := kirchhoff hf v
  rw [← hF, hFeq, Finset.sum_insert (by simp [h₁₂, m₃.2.1.symm, m₄.2.1.symm]),
    Finset.sum_insert (by simp [m₃.1.symm, m₄.1.symm]), Finset.sum_pair h34] at hk
  rw [← hk]; abel

/-! ### The step (∗) of Lemma 4.3 (tex l.363-372) -/

/-- (∗): `Q` leaves `v` by the dart `d` (end 2) and enters `v` by the dart `d'` (end 1 = `(d'.1, !d'.2)`); `i, j`
are the other two ends at `v`, with `y₁ + y₂ + y_i + y_j = 0`; `f` has no balanced pair. If `-(y₁ + y_i)` is not the
value along `Q` of a dart of `Q` other than `d, d'`, then `f + (y₁ + y_i) χ_Q` is a flow with a balanced pair. -/
theorem star {A : Type} [AddCommGroup A] {f : E → A} (hf : G.IsNZFlow f) (hnb : ¬ G.HasBalancedPair f)
    (Q : G.DirCycle) {v : V} {d d' i j : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts)
    (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (hiv : G.endVertex i = v)
    (hid : i ≠ d) (hid' : i ≠ (d'.1, !d'.2))
    (hsum : dirVal f (d'.1, !d'.2) + dirVal f d + dirVal f i + dirVal f j = 0)
    (hfree : ∀ d'' ∈ Q.darts, d'' ≠ d → d'' ≠ d' → dirVal f d'' ≠ -(dirVal f (d'.1, !d'.2) + dirVal f i)) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧
      G.HasBalancedPair (f + fun e => Q.chi e • t) := by
  set y₁ := dirVal f (d'.1, !d'.2) with hy₁
  set t := y₁ + dirVal f i with ht
  have he1v : G.endVertex (d'.1, !d'.2) = v := by rw [endVertex_flip]; exact hd'v
  -- t ≠ 0: the ends 1 and i are not a balanced pair
  have ht0 : t ≠ 0 := by
    intro h0
    exact hnb ⟨v, (d'.1, !d'.2), i, Ne.symm hid', he1v, hiv, h0⟩
  have hnz : ∀ k, dirVal f k ≠ 0 := fun k => by rw [Ne, dirVal_eq_zero_iff]; exact hf.2 k.1
  refine ⟨t, ht0, ?_, ?_⟩
  · rw [isNZFlow_step_iff hf]
    intro d'' hd''
    by_cases h1 : d'' = d
    · rw [h1]
      -- y₂ + t = -y_j
      have : dirVal f d + t = -dirVal f j := by
        rw [ht, eq_neg_iff_add_eq_zero, ← hsum]; abel
      rw [this, neg_ne_zero]; exact hnz j
    · by_cases h2 : d'' = d'
      · rw [h2]
        -- the value along d' is -y₁, so the new value is y_i
        have : dirVal f d' + t = dirVal f i := by
          rw [ht, hy₁, dirVal_flip]; abel
        rw [this]; exact hnz i
      · intro h0
        exact hfree d'' hd'' h1 h2 (eq_neg_of_add_eq_zero_left h0)
  · -- the ends 1 and i are a balanced pair of the new flow
    have hoff := Q.other_end_not_mem hd hd' hdv hd'v hiv hid hid'
    refine ⟨v, (d'.1, !d'.2), i, Ne.symm hid', he1v, hiv, ?_⟩
    rw [Q.dirVal_step_flip f t hd', Q.dirVal_step_off f t hoff.1 hoff.2, ht]
    abel

end EulerFlow.MGraph.Sec4
