/-
EulerFlow/Sec6/Acyc.lean — Lemma 6.1 (tex l.465-474) and Lemma 9.4 (tex l.776-786): push a cycle `Q` with no
small edge down by steps `-1` until an edge of `Q` becomes small. Lemma 6.1 is the case `q = 1` of Lemma 9.4.
-/
import EulerFlow.Defs.Constructions
import EulerFlow.Graph.DirCycleBasic

namespace EulerFlow

open MGraph

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-! ### `I(p, q)` in terms of integers -/

/-- `I(p, q)` is closed under negation: `-n ≡ p - n`. -/
theorem neg_mem_Ipq {p q : ℕ} (hpq : 2 * q < p) {y : ZMod p} (hy : y ∈ Ipq p q) : -y ∈ Ipq p q := by
  obtain ⟨n, h1, h2, rfl⟩ := hy
  refine ⟨p - n, by omega, by omega, ?_⟩
  rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]

/-- A value of `I(p, q)` other than `q, -q` is the residue of an integer in `{q+1, …, p-q-1}`. -/
theorem val_bounds_of_mem_Ipq {p q : ℕ} (hq : 1 ≤ q) (hpq : 2 * q < p) {y : ZMod p} (hy : y ∈ Ipq p q)
    (hyq : y ≠ q) (hyq' : y ≠ -(q : ZMod p)) : q + 1 ≤ y.val ∧ y.val + q + 1 ≤ p := by
  obtain ⟨n, h1, h2, rfl⟩ := hy
  rw [ZMod.val_natCast_of_lt (by omega)]
  have hnq : n ≠ q := fun h => hyq (by rw [h])
  have hnpq : n ≠ p - q := fun h => hyq' (by
    rw [h, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub])
  omega

/-- For `m ≥ 2`, `I(m, 1)` is the set of the non-zero residues. -/
theorem Ipq_one {m : ℕ} (hm : 2 ≤ m) : Ipq m 1 = {x : ZMod m | x ≠ 0} := by
  have : NeZero m := ⟨by omega⟩
  ext x
  constructor
  · rintro ⟨n, h1, h2, rfl⟩ h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd (by omega) h0) (by omega)
  · intro hx
    refine ⟨x.val, ?_, ?_, ZMod.natCast_zmod_val x⟩
    · rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]; exact hx
    · have := ZMod.val_lt x; omega

/-! ### Darts and edges -/

omit [Fintype E] [DecidableEq E] in
/-- The value on the edge from the value along a dart: an edge value is in a negation-closed set iff the
value along a dart of that edge is. -/
theorem mem_of_dirVal_mem {A : Type} [AddCommGroup A] {I : Set A} (hI : ∀ y ∈ I, -y ∈ I) (x : E → A)
    (d : E × Bool) (h : dirVal x d ∈ I) : x d.1 ∈ I := by
  obtain ⟨e, b⟩ := d
  cases b
  · simpa [dirVal] using h
  · simpa [dirVal] using hI _ h

omit [Fintype E] [DecidableEq E] in
theorem dirVal_mem_of_mem {A : Type} [AddCommGroup A] {I : Set A} (hI : ∀ y ∈ I, -y ∈ I) (x : E → A)
    (d : E × Bool) (h : x d.1 ∈ I) : dirVal x d ∈ I := by
  obtain ⟨e, b⟩ := d
  cases b
  · simpa [dirVal] using h
  · simpa [dirVal] using hI _ h

omit [Fintype E] [DecidableEq E] in
/-- An edge value is `±q` iff the value along a dart of that edge is. -/
theorem dirVal_ne_pm {A : Type} [AddCommGroup A] (x : E → A) (d : E × Bool) (a : A)
    (h : x d.1 ≠ a ∧ x d.1 ≠ -a) : dirVal x d ≠ a ∧ dirVal x d ≠ -a := by
  obtain ⟨e, b⟩ := d
  cases b
  · simpa [dirVal] using h
  · simp only [dirVal, ite_true]
    constructor
    · intro h'; exact h.2 (by rw [← h', neg_neg])
    · intro h'; exact h.1 (neg_injective h')

omit [Fintype E] [DecidableEq E] in
/-- If the value along a dart is `a`, the edge value is `a` or `-a`. -/
theorem eq_pm_of_dirVal_eq {A : Type} [AddCommGroup A] (x : E → A) (d : E × Bool) (a : A)
    (h : dirVal x d = a) : x d.1 = a ∨ x d.1 = -a := by
  obtain ⟨e, b⟩ := d
  cases b
  · left; simpa [dirVal] using h
  · right; simp only [dirVal, ite_true] at h; rw [← h, neg_neg]

/-! ### The flow condition is linear -/

omit [Fintype V] in
/-- `f + χ_Q • c` satisfies the flow condition if `f` does. -/
theorem isFlow_add_chi_smul {A : Type} [AddCommGroup A] {G : MGraph V E} {f : E → A} (hf : G.IsFlow f)
    (Q : G.DirCycle) (c : A) : G.IsFlow (f + fun e => Q.chi e • c) := by
  intro v
  have h2 : ∑ e ∈ Finset.univ.filter (fun e => G.src e = v), Q.chi e • c =
      ∑ e ∈ Finset.univ.filter (fun e => G.tgt e = v), Q.chi e • c := by
    rw [← Finset.sum_smul, ← Finset.sum_smul, Q.isFlow_chi v]
  simp only [Pi.add_apply, Finset.sum_add_distrib, hf v, h2]

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- Off `Q`, a step along `Q` changes nothing. -/
theorem step_off {A : Type} [AddCommGroup A] {G : MGraph V E} (Q : G.DirCycle) (f : E → A) (c : A) {e : E}
    (he : ∀ d ∈ Q.darts, d.1 ≠ e) : (f + fun e => Q.chi e • c) e = f e := by
  simp [Q.chi_eq_zero he]

/-! ### The core of Lemma 9.4 -/

/-- The sum of the first `j` steps of `n` steps `-1`. -/
theorem sum_take_replicate_neg_one {p : ℕ} (n j : ℕ) (hj : j ≤ n) :
    ((List.replicate n (-1 : ZMod p)).take j).sum = -(j : ZMod p) := by
  rw [List.take_replicate, List.sum_replicate, Nat.min_eq_left hj]
  simp

/-- Lemma 9.4, core: there is `n` such that every `f - jχ_Q`, `j ≤ n`, is a `(p,q)`-flow, and `f - nχ_Q` has
fewer non-small edges. `n = x - q`, where `x ∈ {q+1, …, p-q-1}` is the least value along `Q`. -/
theorem lem_9_4_core (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (f : E → ZMod p)
    (hf : G.IsIFlow (Ipq p q) f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ≠ q ∧ f d.1 ≠ -(q : ZMod p)) :
    ∃ n : ℕ, (∀ j ≤ n, G.IsIFlow (Ipq p q) (f + fun e => Q.chi e • (-(j : ZMod p)))) ∧
      rhoPQ q (f + fun e => Q.chi e • (-(n : ZMod p))) + 1 ≤ rhoPQ q f := by
  classical
  have : NeZero p := ⟨by omega⟩
  have hI : ∀ y ∈ Ipq p q, -y ∈ Ipq p q := fun y hy => neg_mem_Ipq hpq hy
  -- the integer value `x_d` along each dart of `Q`, in `{q+1, …, p-q-1}`
  have hbd : ∀ d ∈ Q.darts, q + 1 ≤ (dirVal f d).val ∧ (dirVal f d).val + q + 1 ≤ p := by
    intro d hd
    have hne := dirVal_ne_pm f d (q : ZMod p) (hQ d hd)
    exact val_bounds_of_mem_Ipq hq hpq (dirVal_mem_of_mem hI f d (hf.2 d.1)) hne.1 hne.2
  -- the dart `d₀` with the least `x_d`
  obtain ⟨d₀, hd₀, hmin⟩ := Finset.exists_min_image Q.darts.toFinset (fun d => (dirVal f d).val)
    ⟨Q.darts.head Q.ne_nil, List.mem_toFinset.2 (List.head_mem Q.ne_nil)⟩
  rw [List.mem_toFinset] at hd₀
  set x := (dirVal f d₀).val with hx
  have hx_bd := hbd d₀ hd₀
  -- along a dart `d` of `Q`, `f - jχ_Q` has the value `x_d - j`
  have hstep : ∀ j : ℕ, ∀ d ∈ Q.darts, j ≤ (dirVal f d).val →
      dirVal (f + fun e => Q.chi e • (-(j : ZMod p))) d = (((dirVal f d).val - j : ℕ) : ZMod p) := by
    intro j d hd hj
    rw [Q.dirVal_step_mem f _ hd, Nat.cast_sub hj, ZMod.natCast_zmod_val, sub_eq_add_neg]
  refine ⟨x - q, fun j hj => ⟨isFlow_add_chi_smul hf.1 Q _, fun e => ?_⟩, ?_⟩
  · -- the values of `f - jχ_Q`
    by_cases he : ∃ d ∈ Q.darts, d.1 = e
    · obtain ⟨d, hd, rfl⟩ := he
      have hxd := hmin d (List.mem_toFinset.2 hd)
      have hbdd := hbd d hd
      apply mem_of_dirVal_mem hI
      rw [hstep j d hd (by omega)]
      exact ⟨_, by omega, by omega, rfl⟩
    · push Not at he
      rw [step_off Q f _ he]
      exact hf.2 e
  · -- `ρ` decreases: the edge of `d₀` became small, and no edge became non-small
    set g := f + fun e => Q.chi e • (-((x - q : ℕ) : ZMod p)) with hg
    have hgd₀ : dirVal g d₀ = (q : ZMod p) := by
      rw [hg, hstep _ d₀ hd₀ (by omega)]
      congr 1
      omega
    have hsub : {e | g e ≠ (q : ZMod p) ∧ g e ≠ -(q : ZMod p)} ⊆
        {e | f e ≠ (q : ZMod p) ∧ f e ≠ -(q : ZMod p)} \ {d₀.1} := by
      intro e ⟨he1, he2⟩
      refine ⟨?_, ?_⟩
      · by_cases he : ∃ d ∈ Q.darts, d.1 = e
        · obtain ⟨d, hd, rfl⟩ := he
          exact hQ d hd
        · push Not at he
          rw [hg, step_off Q f _ he] at he1 he2
          exact ⟨he1, he2⟩
      · rintro rfl
        rcases eq_pm_of_dirVal_eq g d₀ _ hgd₀ with h | h
        · exact he1 h
        · exact he2 h
    have hmem : d₀.1 ∈ {e | f e ≠ (q : ZMod p) ∧ f e ≠ -(q : ZMod p)} := hQ d₀ hd₀
    unfold rhoPQ
    calc Set.ncard {e | g e ≠ (q : ZMod p) ∧ g e ≠ -(q : ZMod p)} + 1
        ≤ Set.ncard ({e | f e ≠ (q : ZMod p) ∧ f e ≠ -(q : ZMod p)} \ {d₀.1}) + 1 :=
          Nat.add_le_add_right (Set.ncard_le_ncard hsub) 1
      _ = Set.ncard {e | f e ≠ (q : ZMod p) ∧ f e ≠ -(q : ZMod p)} :=
          Set.ncard_sdiff_singleton_add_one hmem

omit [Fintype V] in
/-- The chain of Lemma 9.4 as `StepsAlong`, for any `I` that is `I(p, q)` and any `T ∋ -1`. -/
theorem stepsAlong_of_core {p : ℕ} (hp : 2 < p) (G : MGraph V E) (I T : Set (ZMod p)) (hT : (-1 : ZMod p) ∈ T)
    (f : E → ZMod p) (Q : G.DirCycle) (n : ℕ)
    (hflow : ∀ j ≤ n, G.IsIFlow I (f + fun e => Q.chi e • (-(j : ZMod p)))) :
    G.StepsAlong I T Q f (List.replicate n (-1)) := by
  have : Fact (1 < p) := ⟨by omega⟩
  refine ⟨fun t ht => ?_, fun j hj => ?_⟩
  · rw [List.eq_of_mem_replicate ht]
    exact ⟨hT, neg_ne_zero.2 one_ne_zero⟩
  · rw [List.length_replicate] at hj
    rw [sum_take_replicate_neg_one n j hj]
    exact hflow j hj

/-! ### The two lemmas, with the exact types of `Paper/Statements.lean` -/

/-- Lemma 9.4 (tex l.776-786). -/
theorem lem_9_4_proved (p q : ℕ) (hq : 1 ≤ q) (hpq : 2 * q < p) (G : MGraph V E) (f : E → ZMod p)
    (hf : G.IsIFlow (Ipq p q) f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ≠ q ∧ f d.1 ≠ -(q : ZMod p)) :
    ∃ ts : List (ZMod p), (∀ t ∈ ts, t = -1) ∧ G.StepsAlong (Ipq p q) (Tpq p q) Q f ts ∧
      rhoPQ q (f + fun e => Q.chi e • ts.sum) + 1 ≤ rhoPQ q f := by
  obtain ⟨n, hflow, hrho⟩ := lem_9_4_core p q hq hpq G f hf Q hQ
  refine ⟨List.replicate n (-1), fun t ht => List.eq_of_mem_replicate ht,
    stepsAlong_of_core (by omega) G _ _ (by simp [Tpq]) f Q n hflow, ?_⟩
  rw [← List.take_length (l := List.replicate n (-1 : ZMod p)), List.length_replicate,
    sum_take_replicate_neg_one n n le_rfl]
  exact hrho

omit [Fintype E] [DecidableEq E] in
/-- `ρ` of Section 6 is `ρ` of Section 9 with `q = 1`. -/
theorem rhoPQ_one {m : ℕ} (f : E → ZMod m) : rhoPQ 1 f = rhoCyc f := by
  simp [rhoPQ, rhoCyc]

/-- Lemma 6.1 (tex l.465-474). -/
theorem lem_6_1_proved (m : ℕ) (hm : 4 ≤ m) (G : MGraph V E) (f : E → ZMod m) (hf : G.IsNZFlow f)
    (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ≠ 1 ∧ f d.1 ≠ -1) :
    ∃ ts : List (ZMod m), (∀ t ∈ ts, t = -1) ∧ G.StepsAlong {x | x ≠ 0} (Tcyc m) Q f ts ∧
      rhoCyc (f + fun e => Q.chi e • ts.sum) + 1 ≤ rhoCyc f := by
  have hI := Ipq_one (show 2 ≤ m by omega)
  have hf' : G.IsIFlow (Ipq m 1) f := by rw [hI]; exact hf
  have hQ' : ∀ d ∈ Q.darts, f d.1 ≠ ((1 : ℕ) : ZMod m) ∧ f d.1 ≠ -((1 : ℕ) : ZMod m) := by
    simpa using hQ
  obtain ⟨n, hflow, hrho⟩ := lem_9_4_core m 1 le_rfl (by omega) G f hf' Q hQ'
  rw [hI] at hflow
  refine ⟨List.replicate n (-1), fun t ht => List.eq_of_mem_replicate ht,
    stepsAlong_of_core (by omega) G _ _ (by simp [Tcyc]) f Q n hflow, ?_⟩
  rw [← List.take_length (l := List.replicate n (-1 : ZMod m)), List.length_replicate,
    sum_take_replicate_neg_one n n le_rfl, ← rhoPQ_one, ← rhoPQ_one]
  exact hrho

end EulerFlow
