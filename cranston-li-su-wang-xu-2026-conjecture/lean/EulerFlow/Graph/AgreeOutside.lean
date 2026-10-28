/-
EulerFlow/Graph/AgreeOutside.lean — paper 002, Section 2 (tex l.138-139, again l.709-711): two flows that agree
outside a cycle differ by a flow on that cycle, which is constant along the cycle: `f' = f + t χ_Q`; and
conversely. Route: `g = f' - f` is a flow that vanishes off `Q`; at each vertex of `Q` the flow condition, written
over the ends (eq. (2.1)), has only the entering and the leaving end of `Q`, so `g` has the same value along
consecutive darts of `Q`.
-/
import EulerFlow.Graph.DirCycleBasic
import EulerFlow.Graph.MultiStep

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

omit [DecidableEq E] in
/-- The flow condition over the ends at `v` (eq. (2.1)): the outward values at `v` sum to zero. -/
lemma sum_dirVal_ends {A : Type} [AddCommGroup A] {g : E → A} (hg : G.IsFlow g) (v : V) :
    ∑ i ∈ univ.filter (fun i : E × Bool => G.endVertex i = v), dirVal g i = 0 := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have h := hg v
  rw [Finset.sum_filter, Finset.sum_filter] at h
  have hterm : ∀ e, ∑ b : Bool, (if G.endVertex (e, b) = v then dirVal g (e, b) else 0) =
      (if G.src e = v then g e else 0) - (if G.tgt e = v then g e else 0) := by
    intro e
    rw [Fintype.sum_bool]
    simp only [endVertex, dirVal, ↓reduceIte, Bool.false_eq_true]
    split_ifs <;> abel
  rw [Finset.sum_congr rfl (fun e _ => hterm e), Finset.sum_sub_distrib, h, sub_self]

omit [DecidableEq E] in
lemma isFlow_sub_gen {A : Type} [AddCommGroup A] {f f' : E → A} (hf : G.IsFlow f) (hf' : G.IsFlow f') :
    G.IsFlow (f' - f) := by
  intro v
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, hf v, hf' v]

/-- At a vertex of `Q`, a flow vanishing off `Q` has the same value on the entering and the leaving dart. -/
lemma dirVal_consecutive {A : Type} [AddCommGroup A] (Q : G.DirCycle) {g : E → A} (hg : G.IsFlow g)
    (hoff : ∀ e, Q.chi e = 0 → g e = 0) {d d' : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts)
    (hdd' : G.dartHead d = G.dartTail d') : dirVal g d' = dirVal g d := by
  set v := G.dartTail d' with hv
  have hsum := sum_dirVal_ends hg v
  have hne : d' ≠ (d.1, !d.2) := by
    intro h
    have h1 : d'.1 = d.1 := by rw [h]
    have := Q.eq_of_fst_eq hd' hd h1
    rw [this] at h
    rcases d with ⟨e, b⟩
    cases b <;> simp at h
  rw [Finset.sum_eq_add d' (d.1, !d.2) hne] at hsum
  · rw [dirVal_flip, ← sub_eq_add_neg, sub_eq_zero] at hsum
    exact hsum
  · intro i hi hid
    have hiv : G.endVertex i = v := (mem_filter.1 hi).2
    have := Q.other_end_not_mem hd' hd rfl (hv ▸ hdd') hiv hid.1 hid.2
    rw [dirVal_eq_zero_iff]
    apply hoff
    apply Q.chi_of_not_mem
    intro hmem
    obtain ⟨d2, hd2, h2⟩ := List.mem_map.1 hmem
    rcases i with ⟨e, b⟩
    rcases d2 with ⟨e2, b2⟩
    simp only at h2
    subst h2
    cases b <;> cases b2 <;> simp_all
  · intro h; exact absurd (mem_filter.2 ⟨mem_univ d', by rw [hv]; rfl⟩) h
  · intro h; exact absurd (mem_filter.2 ⟨mem_univ _, by rw [endVertex_flip, hdd']⟩) h

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- In a chain where consecutive elements have equal `φ`, every element has the `φ` of the head. -/
lemma eq_head_of_isChain {α β : Type} (φ : α → β) (R : α → α → Prop) (l : List α) (hl : l ≠ [])
    (hc : l.IsChain R) (hR : ∀ a ∈ l, ∀ b ∈ l, R a b → φ b = φ a) : ∀ a ∈ l, φ a = φ (l.head hl) := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    intro x hx
    rcases l with _ | ⟨b, l⟩
    · simp at hx; simp [hx]
    · rw [List.isChain_cons_cons] at hc
      have hR' : ∀ a ∈ b :: l, ∀ c ∈ b :: l, R a c → φ c = φ a :=
        fun a ha c hc' h => hR a (List.mem_cons_of_mem _ ha) c (List.mem_cons_of_mem _ hc') h
      rcases List.mem_cons.1 hx with rfl | hx'
      · rfl
      · rw [ih (by simp) hc.2 hR' x hx']
        simpa using hR _ (by simp) _ (by simp) hc.1

/-- `sec2_agree_outside_cycle` (tex l.138-139, l.709-711): two flows agree outside `Q` iff they differ by
`t χ_Q` for some `t`. -/
theorem sec2_agree_outside_cycle_proved [Fintype V] {A : Type} [AddCommGroup A] (G : MGraph V E)
    (Q : G.DirCycle) (f f' : E → A) (hf : G.IsFlow f) (hf' : G.IsFlow f') :
    (∀ e, Q.chi e = 0 → f e = f' e) ↔ ∃ t : A, f' = f + fun e => Q.chi e • t := by
  constructor
  · intro hout
    set g := f' - f with hgdef
    have hg : G.IsFlow g := isFlow_sub_gen hf hf'
    have hoff : ∀ e, Q.chi e = 0 → g e = 0 := by
      intro e he; simp [hgdef, hout e he]
    have hconst := eq_head_of_isChain (dirVal g) _ Q.darts Q.ne_nil Q.chain
      (fun d hd d' hd' h => dirVal_consecutive Q hg hoff hd hd' h)
    refine ⟨dirVal g (Q.darts.head Q.ne_nil), funext fun e => ?_⟩
    by_cases he : e ∈ Q.darts.map Prod.fst
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
      rw [Pi.add_apply, Q.chi_of_mem hd, ← hconst d hd]
      have hgd : g d.1 = f' d.1 - f d.1 := rfl
      rcases d with ⟨e, _ | _⟩ <;> simp [dartSign, dirVal, hgd]
    · rw [Pi.add_apply, Q.chi_of_not_mem he, zero_smul, add_zero]
      exact (hout e (Q.chi_of_not_mem he)).symm
  · rintro ⟨t, rfl⟩ e he
    simp [he]

end MGraph

end EulerFlow
