/-
EulerFlow/Sec4/Bstar.lean — Lemma 4.3 (tex l.357-389): Case 1 (two neighbouring edges of Q of different colours) and
Case 2 (all edges of Q of one colour), each finished by the step (∗) of Sec4/Local.lean. The two facts on parts
of a cyclic decomposition are hypotheses here (`ColourUnique`, `SmallSumEq`; proved in Sec4/Decomp.lean).
-/
import EulerFlow.Sec4.Local

namespace EulerFlow.MGraph.Sec4

open Finset

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V] {G : MGraph V E}
variable {A : Type} [AddCommGroup A]

set_option linter.unusedSectionVars false

/-- The colour of a small element is unique. -/
def ColourUnique (D : CyclicDecomp A) : Prop :=
  ∀ (x : A) (k j : Fin D.r), (x = D.s k ∨ x = -D.s k) → (x = D.s j ∨ x = -D.s j) → k = j

/-- Lemma 4.3 Case 1, algebra (tex l.377-381). -/
def SmallSumEq (D : CyclicDecomp A) : Prop :=
  ∀ (t₃ t₄ a b : A) (i j : Fin D.r), t₃ ∈ D.S → t₄ ∈ D.S → (a = D.s i ∨ a = -D.s i) →
    (b = D.s j ∨ b = -D.s j) → i ≠ j → t₃ + t₄ = a - b → t₃ = a ∨ t₄ = a

theorem S_neg (D : CyclicDecomp A) {x : A} (hx : x ∈ D.S) : -x ∈ D.S := by
  obtain ⟨k, hk | hk⟩ := hx
  · exact ⟨k, Or.inr (by rw [hk])⟩
  · exact ⟨k, Or.inl (by rw [hk, neg_neg])⟩

theorem pm_dirVal {s : A} (f : E → A) (d : E × Bool) (h : f d.1 = s ∨ f d.1 = -s) :
    dirVal f d = s ∨ dirVal f d = -s := by
  unfold dirVal; split_ifs
  · rcases h with h | h <;> simp [h]
  · exact h

theorem dirVal_mem_S (D : CyclicDecomp A) (f : E → A) (d : E × Bool) (h : f d.1 ∈ D.S) : dirVal f d ∈ D.S := by
  unfold dirVal; split_ifs
  · exact S_neg D h
  · exact h

/-- The set-up at a vertex `v = tail d` of `Q` entered by `d'`: two more ends `i₃, i₄` and Kirchhoff. -/
theorem setup (hG : G.Loopless) (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) {f : E → A}
    (hf : G.IsNZFlow f) (Q : G.DirCycle) {d d' : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts)
    (hcons : G.dartHead d' = G.dartTail d) :
    ∃ i₃ i₄ : E × Bool, G.endVertex i₃ = G.dartTail d ∧ G.endVertex i₄ = G.dartTail d ∧
      i₃ ≠ d ∧ i₃ ≠ (d'.1, !d'.2) ∧ i₄ ≠ d ∧ i₄ ≠ (d'.1, !d'.2) ∧
      dirVal f (d'.1, !d'.2) + dirVal f d + dirVal f i₃ + dirVal f i₄ = 0 := by
  have h1 : G.endVertex (d'.1, !d'.2) = G.dartTail d := by rw [endVertex_flip]; exact hcons
  have h2 : G.endVertex d = G.dartTail d := rfl
  have h12 : (d'.1, !d'.2) ≠ d := by
    intro h; exact Q.flip_not_mem hd' (h ▸ hd)
  have hdeg4 : G.degree (G.dartTail d) = 4 := by
    rcases hdeg (G.dartTail d) with h0 | h4
    · exfalso
      have : d ∈ univ.filter (fun i : E × Bool => G.endVertex i = G.dartTail d) := by simp [h2]
      have hpos := Finset.card_pos.mpr ⟨d, this⟩
      unfold degree at h0; omega
    · exact h4
  obtain ⟨i₃, i₄, h3, h4, h31, h32, h41, h42, -, hsum⟩ := four_ends hf.1 hdeg4 h1 h2 h12
  exact ⟨i₃, i₄, h3, h4, h32, h31, h42, h41, hsum⟩

/-- Lemma 4.3, Case 1 (tex l.376-382): at a vertex where two neighbouring edges of `Q` have different colours. -/
theorem case1 (D : CyclicDecomp A) (hss : SmallSumEq D) (hG : G.Loopless)
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) {f : E → A} (hf : G.IsNZFlow f)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle) (hQ : ∀ d ∈ Q.darts, f d.1 ∈ D.S)
    {d d' : E × Bool} (hd : d ∈ Q.darts) (hd' : d' ∈ Q.darts) (hcons : G.dartHead d' = G.dartTail d)
    {i j : Fin D.r} (hi : f d'.1 = D.s i ∨ f d'.1 = -D.s i) (hj : f d.1 = D.s j ∨ f d.1 = -D.s j) (hij : i ≠ j) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧ G.HasBalancedPair (f + fun e => Q.chi e • t) := by
  obtain ⟨i₃, i₄, h3, h4, h3d, h3d', h4d, h4d', hsum⟩ := setup hG hdeg hf Q hd hd' hcons
  have hai : dirVal f (d'.1, !d'.2) = D.s i ∨ dirVal f (d'.1, !d'.2) = -D.s i := by
    rw [dirVal_flip]
    rcases pm_dirVal f d' hi with h | h <;> simp [h]
  have hbj := pm_dirVal f d hj
  have hnz : ∀ k, dirVal f k ≠ 0 := fun k => by rw [Ne, dirVal_eq_zero_iff]; exact hf.2 k.1
  have h4eq : dirVal f i₄ = -(dirVal f (d'.1, !d'.2) + dirVal f d + dirVal f i₃) :=
    eq_neg_of_add_eq_zero_right hsum
  -- t₃ or t₄ is not small
  have hnot : dirVal f (d'.1, !d'.2) + dirVal f i₃ ∉ D.S ∨ dirVal f (d'.1, !d'.2) + dirVal f i₄ ∉ D.S := by
    by_contra hc
    push Not at hc
    have hs : (dirVal f (d'.1, !d'.2) + dirVal f i₃) + (dirVal f (d'.1, !d'.2) + dirVal f i₄) =
        dirVal f (d'.1, !d'.2) - dirVal f d := by
      rw [h4eq]; abel
    rcases hss _ _ _ _ i j hc.1 hc.2 hai hbj hij hs with h | h
    · exact hnz i₃ (by simpa using h)
    · exact hnz i₄ (by simpa using h)
  rcases hnot with h | h
  · refine star hf hnb Q hd hd' rfl hcons h3 h3d h3d' hsum ?_
    intro d'' hd'' _ _ heq
    exact h (by have := S_neg D (dirVal_mem_S D f d'' (hQ d'' hd'')); rw [heq, neg_neg] at this; exact this)
  · refine star (j := i₃) hf hnb Q hd hd' rfl hcons h4 h4d h4d' (by rw [h4eq]; abel) ?_
    intro d'' hd'' _ _ heq
    exact h (by have := S_neg D (dirVal_mem_S D f d'' (hQ d'' hd'')); rw [heq, neg_neg] at this; exact this)

/-- Lemma 4.3, Case 2 (tex l.384-388): all edges of `Q` have one colour `k`. -/
theorem case2 (D : CyclicDecomp A) (hG : G.Loopless)
    (hdeg : ∀ v, G.degree v = 0 ∨ G.degree v = 4) {f : E → A} (hf : G.IsNZFlow f)
    (hnb : ¬ G.HasBalancedPair f) (Q : G.DirCycle) {k : Fin D.r}
    (hk : ∀ d ∈ Q.darts, f d.1 = D.s k ∨ f d.1 = -D.s k) :
    ∃ t : A, t ≠ 0 ∧ G.IsNZFlow (f + fun e => Q.chi e • t) ∧ G.HasBalancedPair (f + fun e => Q.chi e • t) := by
  have hd : Q.darts.head Q.ne_nil ∈ Q.darts := List.head_mem _
  obtain ⟨d', hd', hcons⟩ := Q.exists_enter hd
  obtain ⟨i₃, i₄, h3, h4, h3d, h3d', h4d, h4d', hsum⟩ := setup hG hdeg hf Q hd hd' hcons
  have hnz : ∀ k, dirVal f k ≠ 0 := fun k => by rw [Ne, dirVal_eq_zero_iff]; exact hf.2 k.1
  have hak : dirVal f (d'.1, !d'.2) = D.s k ∨ dirVal f (d'.1, !d'.2) = -D.s k := by
    rw [dirVal_flip]
    rcases pm_dirVal f d' (hk d' hd') with h | h <;> simp [h]
  have hbk := pm_dirVal f _ (hk _ hd)
  -- the ends 1 and 2 are not a balanced pair, so y₁ = y₂
  have hab0 : dirVal f (d'.1, !d'.2) + dirVal f (Q.darts.head Q.ne_nil) ≠ 0 := by
    intro h0
    have h1 : G.endVertex (d'.1, !d'.2) = G.dartTail (Q.darts.head Q.ne_nil) := by
      rw [endVertex_flip]; exact hcons
    have h12 : (d'.1, !d'.2) ≠ Q.darts.head Q.ne_nil := by intro h; exact Q.flip_not_mem hd' (h ▸ hd)
    exact hnb ⟨_, _, _, h12, h1, rfl, h0⟩
  have hab : dirVal f (Q.darts.head Q.ne_nil) = dirVal f (d'.1, !d'.2) := by
    rcases hak with h1 | h1 <;> rcases hbk with h2 | h2
    · rw [h1, h2]
    · exact absurd (by rw [h1, h2, add_neg_cancel]) hab0
    · exact absurd (by rw [h1, h2, neg_add_cancel]) hab0
    · rw [h1, h2]
  have h4eq : dirVal f i₄ = -(dirVal f (d'.1, !d'.2) + dirVal f (Q.darts.head Q.ne_nil) + dirVal f i₃) :=
    eq_neg_of_add_eq_zero_right hsum
  refine star hf hnb Q hd hd' rfl hcons h3 h3d h3d' hsum ?_
  intro d'' hd'' _ _ heq
  -- the value along d'' is ±s_k = ±y₁, and -(y₁ + y₃) is neither y₁ nor -y₁
  have hd''k := pm_dirVal f d'' (hk d'' hd'')
  have hpm : dirVal f d'' = dirVal f (d'.1, !d'.2) ∨ dirVal f d'' = -dirVal f (d'.1, !d'.2) := by
    rcases hak with h1 | h1 <;> rcases hd''k with h2 | h2 <;> simp [h1, h2]
  rcases hpm with h | h
  · -- -(y₁ + y₃) = y₁: then y₄ = 0
    apply hnz i₄
    have e : -(dirVal f (d'.1, !d'.2) + dirVal f i₃) = dirVal f (d'.1, !d'.2) := heq.symm.trans h
    have e' := eq_neg_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mp e)
    rw [h4eq, hab]
    rw [← neg_zero, ← e']; abel
  · -- -(y₁ + y₃) = -y₁: then y₃ = 0
    apply hnz i₃
    have := heq.symm.trans h
    rw [neg_inj] at this
    simpa using this

end EulerFlow.MGraph.Sec4
