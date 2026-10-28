/-
EulerFlow/Graph/DirCycleBasic.lean — dart-level facts on directed cycles: χ on the darts of Q, the outward values
of a step at the ends of Q (the paper's equation (2.2), tex l.160-164), heads = tails rotated.
-/
import EulerFlow.Defs.Constructions
import EulerFlow.Graph.Chi

namespace EulerFlow.MGraph

variable {V E : Type} {G : MGraph V E}

/-! ### `dirVal` is additive, and is zero exactly when the edge value is zero -/

theorem dirVal_add {M : Type} [AddCommGroup M] (x y : E → M) (d : E × Bool) :
    dirVal (x + y) d = dirVal x d + dirVal y d := by
  unfold dirVal; split_ifs <;> simp [add_comm]

theorem dirVal_eq_zero_iff {M : Type} [AddCommGroup M] (x : E → M) (d : E × Bool) :
    dirVal x d = 0 ↔ x d.1 = 0 := by
  unfold dirVal; split_ifs <;> simp

theorem dirVal_flip {M : Type} [AddCommGroup M] (x : E → M) (d : E × Bool) :
    dirVal x (d.1, !d.2) = -dirVal x d := by
  obtain ⟨e, b⟩ := d; cases b <;> simp [dirVal]

theorem endVertex_flip (d : E × Bool) : G.endVertex (d.1, !d.2) = G.dartHead d := rfl

namespace DirCycle

variable (Q : G.DirCycle)

/-- Two darts of `Q` that leave the same vertex are equal. -/
theorem eq_of_tail_eq {d d' : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts)
    (h : G.dartTail d = G.dartTail d') : d = d' :=
  List.inj_on_of_nodup_map Q.tails_nodup hd hd' h

/-- `Q` does not pass an edge in both directions. -/
theorem flip_not_mem {d : E × Bool} (hd : d ∈ Q.darts) : (d.1, !d.2) ∉ Q.darts := by
  intro h
  have h2 := congrArg Prod.snd (Q.eq_of_fst_eq hd h rfl)
  obtain ⟨e, b⟩ := d
  cases b <;> simp at h2

/-- The heads of the darts of `Q`, in order, are its tails rotated by one. -/
theorem heads_eq_rotate : Q.darts.map G.dartHead = (Q.darts.map G.dartTail).rotate 1 := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  rw [List.getElem_rotate]
  simp only [List.getElem_map, List.length_map]
  have hk : k < Q.darts.length := by simpa using h1
  by_cases hlt : k + 1 < Q.darts.length
  · have hm : (k + 1) % Q.darts.length = k + 1 := Nat.mod_eq_of_lt hlt
    simp only [hm]
    exact Q.chain.getElem k hlt
  · have hm : (k + 1) % Q.darts.length = 0 := by
      rw [show k + 1 = Q.darts.length by omega, Nat.mod_self]
    simp only [hm]
    have hc := Q.closes
    rw [List.getLast_eq_getElem, List.head_eq_getElem] at hc
    have hk' : Q.darts.length - 1 = k := by omega
    simp only [hk'] at hc
    exact hc

theorem heads_nodup : (Q.darts.map G.dartHead).Nodup := by
  rw [Q.heads_eq_rotate]; exact List.nodup_rotate.mpr Q.tails_nodup

/-- Two darts of `Q` that enter the same vertex are equal. -/
theorem eq_of_head_eq {d d' : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts)
    (h : G.dartHead d = G.dartHead d') : d = d' :=
  List.inj_on_of_nodup_map Q.heads_nodup hd hd' h

/-- Every vertex that `Q` leaves, `Q` also enters. -/
theorem exists_enter {d : E × Bool} (hd : d ∈ Q.darts) : ∃ d' ∈ Q.darts, G.dartHead d' = G.dartTail d := by
  have h : G.dartTail d ∈ Q.darts.map G.dartHead := by
    rw [Q.heads_eq_rotate, List.mem_rotate]; exact List.mem_map_of_mem hd
  simpa using h

/-- Every vertex that `Q` enters, `Q` also leaves. -/
theorem exists_leave {d : E × Bool} (hd : d ∈ Q.darts) : ∃ d' ∈ Q.darts, G.dartTail d' = G.dartHead d := by
  have h : G.dartHead d ∈ (Q.darts.map G.dartTail).rotate 1 := by
    rw [← Q.heads_eq_rotate]; exact List.mem_map_of_mem hd
  rw [List.mem_rotate] at h
  simpa using h

/-- At a vertex `v` of `Q`, the ends other than the leaving end `d` and the entering end `(d'.1, !d'.2)` are not
on `Q` (in either direction). -/
theorem other_end_not_mem {v : V} {d d' i : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts)
    (hdv : G.dartTail d = v) (hd'v : G.dartHead d' = v) (hiv : G.endVertex i = v) (hid : i ≠ d)
    (hid' : i ≠ (d'.1, !d'.2)) : i ∉ Q.darts ∧ (i.1, !i.2) ∉ Q.darts := by
  constructor
  · intro hi
    exact hid (Q.eq_of_tail_eq hi hd (by rw [hdv]; exact hiv))
  · intro hi
    have hh : G.dartHead (i.1, !i.2) = G.dartHead d' := by
      rw [hd'v]; simpa [dartHead] using hiv
    have := Q.eq_of_head_eq hi hd' hh
    apply hid'
    rw [← this]; simp

section Chi

variable [DecidableEq E]

/-- `χ_Q` vanishes off `Q`. -/
theorem chi_eq_zero {e : E} (he : ∀ d ∈ Q.darts, d.1 ≠ e) : Q.chi e = 0 := by
  have h1 : (e, false) ∉ Q.darts := fun h => he _ h rfl
  have h2 : (e, true) ∉ Q.darts := fun h => he _ h rfl
  simp [DirCycle.chi, h1, h2]

/-- The value of `t χ_Q` in the direction of an end/dart `i` (tex l.160-164): `t` if `Q` passes `i`, `-t` if `Q`
passes the opposite dart, and `0` if `Q` does not use the edge. -/
theorem dirVal_chi_smul {A : Type} [AddCommGroup A] (t : A) (i : E × Bool) :
    dirVal (fun e => Q.chi e • t) i =
      if i ∈ Q.darts then t else if (i.1, !i.2) ∈ Q.darts then -t else 0 := by
  by_cases hi : i ∈ Q.darts
  · have := Q.chi_of_mem hi
    obtain ⟨e, b⟩ := i
    cases b <;> simp_all [dirVal, dartSign]
  · by_cases hj : (i.1, !i.2) ∈ Q.darts
    · have := Q.chi_of_mem hj
      obtain ⟨e, b⟩ := i
      cases b <;> simp_all [dirVal, dartSign]
    · have h0 : Q.chi i.1 = 0 := Q.chi_eq_zero (by
        intro d hd hde
        obtain ⟨e, b⟩ := i
        obtain ⟨e', b'⟩ := d
        simp only at hde
        subst hde
        cases b <;> cases b' <;> simp_all)
      simp [dirVal, h0, hi, hj]

/-- Equation (2.2) at the leaving end: `y_j(f + tχ_Q) = y_j(f) + t`. -/
theorem dirVal_step_mem {A : Type} [AddCommGroup A] (f : E → A) (t : A) {d : E × Bool} (hd : d ∈ Q.darts) :
    dirVal (f + fun e => Q.chi e • t) d = dirVal f d + t := by
  rw [dirVal_add, Q.dirVal_chi_smul]
  simp [hd]

/-- Equation (2.2) at the entering end: `y_i(f + tχ_Q) = y_i(f) - t`. -/
theorem dirVal_step_flip {A : Type} [AddCommGroup A] (f : E → A) (t : A) {d : E × Bool}
    (hd : d ∈ Q.darts) : dirVal (f + fun e => Q.chi e • t) (d.1, !d.2) = dirVal f (d.1, !d.2) - t := by
  rw [dirVal_add, Q.dirVal_chi_smul]
  simp [hd, Q.flip_not_mem hd, sub_eq_add_neg]

/-- Equation (2.2), last clause: the other ends keep their outward values. -/
theorem dirVal_step_off {A : Type} [AddCommGroup A] (f : E → A) (t : A) {i : E × Bool}
    (hi : i ∉ Q.darts) (hi' : (i.1, !i.2) ∉ Q.darts) :
    dirVal (f + fun e => Q.chi e • t) i = dirVal f i := by
  rw [dirVal_add, Q.dirVal_chi_smul]
  simp [hi, hi']

/-- `f + tχ_Q` is nowhere zero iff `f` is non-zero on the edges off `Q` and every dart value of `f` along `Q`,
plus `t`, is non-zero. -/
theorem ne_zero_step_iff {A : Type} [AddCommGroup A] (f : E → A) (t : A) :
    (∀ e, (f + fun e => Q.chi e • t) e ≠ 0) ↔
      (∀ e, (∀ d ∈ Q.darts, d.1 ≠ e) → f e ≠ 0) ∧ ∀ d ∈ Q.darts, dirVal f d + t ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun e he => ?_, fun d hd => ?_⟩
    · have := h e
      simpa [Q.chi_eq_zero he] using this
    · rw [← Q.dirVal_step_mem f t hd]
      rw [Ne, dirVal_eq_zero_iff]
      exact h d.1
  · rintro ⟨hoff, hon⟩ e
    by_cases he : ∃ d ∈ Q.darts, d.1 = e
    · obtain ⟨d, hd, rfl⟩ := he
      have := hon d hd
      rw [← Q.dirVal_step_mem f t hd, Ne, dirVal_eq_zero_iff] at this
      exact this
    · push Not at he
      have h0 := Q.chi_eq_zero he
      simpa [h0] using hoff e he

end Chi

end DirCycle

end EulerFlow.MGraph
