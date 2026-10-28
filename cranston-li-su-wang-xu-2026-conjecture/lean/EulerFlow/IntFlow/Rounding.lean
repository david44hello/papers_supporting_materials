/-
EulerFlow/IntFlow/Rounding.lean — paper 002, Lemma 8.2 (rounding, tex l.593-606): a map `x : E → [0,1]` with
integer boundary has a `{0,1}`-valued rounding `z` with the same boundary that keeps the values `0` and `1`.
Route = the paper's: while some edge is fractional, the fractional edges contain a cycle (no vertex meets exactly
one fractional end, because the boundary is an integer); push `x` along it by the least `δ` that makes an edge `0`
or `1`; the number of fractional edges drops.
-/
import EulerFlow.Graph.Cycles

namespace EulerFlow

namespace MGraph

open Finset

variable {V E : Type} {G : MGraph V E} [Fintype E] [DecidableEq E] [DecidableEq V]

omit [DecidableEq E] in
/-- The boundary as one sum over all edges. -/
lemma boundary_eq_sum {M : Type} [AddCommGroup M] (x : E → M) (v : V) :
    G.boundary x v = ∑ e, ((if G.tgt e = v then x e else 0) - (if G.src e = v then x e else 0)) := by
  unfold boundary
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]

/-- Pushing a real map along a directed cycle keeps its boundary. -/
lemma boundary_add_smul_chi (x : E → ℝ) (δ : ℝ) (Q : G.DirCycle) (v : V) :
    G.boundary (fun e => x e + δ * (Q.chi e : ℝ)) v = G.boundary x v := by
  have hQ := Q.isFlow_chi v
  have hQr : (∑ e ∈ univ.filter (fun e => G.src e = v), (Q.chi e : ℝ)) =
      ∑ e ∈ univ.filter (fun e => G.tgt e = v), (Q.chi e : ℝ) := by exact_mod_cast hQ
  unfold boundary
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hQr]
  ring

/-- The fractional edges of `x`. -/
noncomputable def fracEdges (x : E → ℝ) : Finset E := univ.filter fun e => 0 < x e ∧ x e < 1

omit [DecidableEq E] in
lemma mem_fracEdges {x : E → ℝ} {e : E} : e ∈ fracEdges x ↔ 0 < x e ∧ x e < 1 := by simp [fracEdges]

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- A value in `[0,1]` that is not fractional is `0` or `1`. -/
lemma eq_zero_or_one_of_not_frac {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) (hf : ¬ (0 < r ∧ r < 1)) : r = 0 ∨ r = 1 := by
  by_contra h
  push Not at h
  exact hf ⟨lt_of_le_of_ne h0 (Ne.symm h.1), lt_of_le_of_ne h1 h.2⟩

omit [Fintype E] [DecidableEq E] [DecidableEq V] in
/-- No integer lies strictly between `0` and `1`. -/
lemma not_int_of_frac {r : ℝ} (h : 0 < r ∧ r < 1) (n : ℤ) : r ≠ n := by
  rintro rfl
  have h0 : (0 : ℤ) < n := by exact_mod_cast h.1
  have h1 : n < 1 := by exact_mod_cast h.2
  omega

/-- **No vertex meets exactly one fractional end** when the boundary is an integer (tex l.600-602). -/
lemma sdeg_frac_ne_one (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hint : ∀ v, ∃ n : ℤ, G.boundary x v = n)
    (v : V) : G.sdeg (fracEdges x) v ≠ 1 := by
  intro h1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
  have huniq : ∀ i : E × Bool, i.1 ∈ fracEdges x → G.endVertex i = v → i = a := by
    intro i hi hv
    have : i ∈ univ.filter (fun i : E × Bool => i.1 ∈ fracEdges x ∧ G.endVertex i = v) := by simp [hi, hv]
    rw [ha] at this
    exact mem_singleton.1 this
  have haF : a.1 ∈ fracEdges x ∧ G.endVertex a = v := by
    have : a ∈ univ.filter (fun i : E × Bool => i.1 ∈ fracEdges x ∧ G.endVertex i = v) := by
      rw [ha]; exact mem_singleton_self a
    simpa using this
  -- the integer value of a non-fractional edge
  set c : E → ℤ := fun e => (if G.tgt e = v then ⌊x e⌋ else 0) - (if G.src e = v then ⌊x e⌋ else 0) with hc
  have hterm : ∀ e ∈ univ.erase a.1,
      ((if G.tgt e = v then x e else 0) - (if G.src e = v then x e else 0)) = (c e : ℝ) := by
    intro e he
    have hne : e ≠ a.1 := (mem_erase.1 he).1
    have hfl : (G.tgt e = v ∨ G.src e = v) → x e = ⌊x e⌋ := by
      intro hv
      have hnf : e ∉ fracEdges x := by
        intro hf
        rcases hv with hv | hv
        · exact hne (congr_arg Prod.fst (huniq (e, true) hf (by simp [endVertex, hv])))
        · exact hne (congr_arg Prod.fst (huniq (e, false) hf (by simp [endVertex, hv])))
      rcases eq_zero_or_one_of_not_frac (hx e).1 (hx e).2 (fun h => hnf (mem_fracEdges.2 h)) with h | h <;>
        simp [h]
    simp only [hc, Int.cast_sub]
    by_cases ht : G.tgt e = v
    · have h := hfl (Or.inl ht)
      by_cases hs : G.src e = v
      · simp [ht, hs]
      · simp [ht, hs, ← h]
    · by_cases hs : G.src e = v
      · have h := hfl (Or.inr hs)
        simp [ht, hs, ← h]
      · simp [ht, hs]
  obtain ⟨n, hn⟩ := hint v
  rw [boundary_eq_sum, ← Finset.add_sum_erase _ _ (mem_univ a.1), Finset.sum_congr rfl hterm,
    ← Int.cast_sum] at hn
  -- exactly one end of `a.1` is at `v`
  have hrev : G.endVertex (dartRev a) ≠ v := by
    intro h
    have := huniq (dartRev a) haF.1 h
    rcases a with ⟨e, b⟩
    cases b <;> simp [dartRev] at this
  have hfrac := mem_fracEdges.1 haF.1
  rcases a with ⟨e, b⟩
  cases b
  · -- the end `(e, false)` is at `src e = v`, and `tgt e ≠ v`
    have hs : G.src e = v := by simpa [endVertex] using haF.2
    have ht : G.tgt e ≠ v := by simpa [dartRev, endVertex] using hrev
    dsimp only at hn
    simp only [hs, ht, ↓reduceIte, zero_sub] at hn
    have : x e = ((∑ e' ∈ univ.erase e, c e') - n : ℤ) := by push_cast at hn ⊢; linarith
    exact not_int_of_frac hfrac _ this
  · -- the end `(e, true)` is at `tgt e = v`, and `src e ≠ v`
    have ht : G.tgt e = v := by simpa [endVertex] using haF.2
    have hs : G.src e ≠ v := by simpa [dartRev, endVertex] using hrev
    dsimp only at hn
    simp only [hs, ht, ↓reduceIte, sub_zero] at hn
    have : x e = (n - ∑ e' ∈ univ.erase e, c e' : ℤ) := by push_cast at hn ⊢; linarith
    exact not_int_of_frac hfrac _ this

/-- **Rounding** (Lemma 8.2, tex l.593-606), by induction on the number of fractional edges. -/
theorem rounding (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1) (hint : ∀ v, ∃ n : ℤ, G.boundary x v = n) :
    ∃ z : E → ℤ, (∀ e, z e = 0 ∨ z e = 1) ∧ G.boundary (fun e => (z e : ℝ)) = G.boundary x ∧
      ∀ e, (x e = 0 → z e = 0) ∧ (x e = 1 → z e = 1) := by
  suffices key : ∀ n : ℕ, ∀ x : E → ℝ, (fracEdges x).card ≤ n → (∀ e, 0 ≤ x e ∧ x e ≤ 1) →
      (∀ v, ∃ n : ℤ, G.boundary x v = n) →
      ∃ z : E → ℤ, (∀ e, z e = 0 ∨ z e = 1) ∧ G.boundary (fun e => (z e : ℝ)) = G.boundary x ∧
        ∀ e, (x e = 0 → z e = 0) ∧ (x e = 1 → z e = 1) from key _ x le_rfl hx hint
  intro n
  induction n with
  | zero =>
    intro x hcard hx _
    have h01 : ∀ e, x e = 0 ∨ x e = 1 := by
      intro e
      refine eq_zero_or_one_of_not_frac (hx e).1 (hx e).2 (fun hf => ?_)
      have : e ∈ fracEdges x := mem_fracEdges.2 hf
      have := Finset.card_pos.2 ⟨e, this⟩
      omega
    refine ⟨fun e => if x e = 1 then 1 else 0, fun e => by by_cases h : x e = 1 <;> simp [h], ?_, ?_⟩
    · congr 1
      funext e
      rcases h01 e with h | h <;> simp [h]
    · intro e
      rcases h01 e with h | h <;> simp [h]
  | succ n ih =>
    intro x hcard hx hint
    rcases (fracEdges x).eq_empty_or_nonempty with hemp | hne
    · exact ih x (by rw [hemp]; simp) hx hint
    obtain ⟨Q, hQ⟩ := G.exists_dirCycle_of_sdeg_ne_one (fracEdges x) hne (sdeg_frac_ne_one x hx hint)
    -- the distance to `0` or `1` in the direction of a dart
    set g : E × Bool → ℝ := fun d => if d.2 then x d.1 else 1 - x d.1 with hg
    have hdne : Q.darts.toFinset.Nonempty := by
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ Q.ne_nil
      exact ⟨d, List.mem_toFinset.2 hd⟩
    obtain ⟨dm, hdm, hmin⟩ := Finset.exists_min_image Q.darts.toFinset g hdne
    rw [List.mem_toFinset] at hdm
    set δ := g dm with hδ
    have hgpos : ∀ d ∈ Q.darts, 0 < g d := by
      intro d hd
      have := mem_fracEdges.1 (hQ d hd)
      simp only [hg]
      split_ifs <;> linarith
    have hδpos : 0 < δ := hgpos dm hdm
    set x' : E → ℝ := fun e => x e + δ * (Q.chi e : ℝ) with hx'
    -- on the edges of `Q`, `x'` moves by `±δ`; elsewhere it is `x`
    have hon : ∀ d ∈ Q.darts, x' d.1 = if d.2 then x d.1 - δ else x d.1 + δ := by
      intro d hd
      simp only [hx', Q.chi_of_mem hd, dartSign]
      split_ifs <;> push_cast <;> ring
    have hoff : ∀ e, e ∉ Q.darts.map Prod.fst → x' e = x e := by
      intro e he
      simp [hx', Q.chi_of_not_mem he]
    have hx'01 : ∀ e, 0 ≤ x' e ∧ x' e ≤ 1 := by
      intro e
      by_cases he : e ∈ Q.darts.map Prod.fst
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
        have hle : δ ≤ g d := hmin d (List.mem_toFinset.2 hd)
        have hfr := mem_fracEdges.1 (hQ d hd)
        rw [hon d hd]
        simp only [hg] at hle
        split_ifs at hle ⊢ <;> constructor <;> linarith
      · rw [hoff e he]; exact hx e
    have hint' : ∀ v, ∃ n : ℤ, G.boundary x' v = n := by
      intro v; rw [hx', boundary_add_smul_chi]; exact hint v
    have hsub : fracEdges x' ⊂ fracEdges x := by
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨dm.1, hQ dm hdm, fun hf => ?_⟩
        have hf' := mem_fracEdges.1 hf
        rw [hon dm hdm] at hf'
        simp only [hδ, hg] at hf'
        split_ifs at hf' <;> linarith [hf'.1, hf'.2]
      · intro e he
        by_cases hq : e ∈ Q.darts.map Prod.fst
        · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hq
          exact hQ d hd
        · rw [mem_fracEdges, ← hoff e hq]; exact mem_fracEdges.1 he
    have hlt := Finset.card_lt_card hsub
    obtain ⟨z, hz01, hzb, hzx⟩ := ih x' (by omega) hx'01 hint'
    refine ⟨z, hz01, ?_, fun e => ?_⟩
    · rw [hzb]; funext v; rw [hx', boundary_add_smul_chi]
    · -- an edge with value `0` or `1` is not fractional, so it is not on `Q`
      have hkeep : (x e = 0 ∨ x e = 1) → x' e = x e := by
        intro h01
        apply hoff
        intro hq
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hq
        have := mem_fracEdges.1 (hQ d hd)
        rcases h01 with h | h <;> linarith [this.1, this.2]
      constructor
      · intro h0; exact (hzx e).1 (by rw [hkeep (Or.inl h0)]; exact h0)
      · intro h1; exact (hzx e).2 (by rw [hkeep (Or.inr h1)]; exact h1)

/-- `lem_8_2` (Lemma 8.2, rounding, tex l.593-597), in the exact Statements form. -/
theorem lem_8_2_proved [Fintype V] (G : MGraph V E) (x : E → ℝ) (hx : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hint : ∀ v, ∃ n : ℤ, G.boundary x v = n) :
    ∃ z : E → ℤ, (∀ e, z e = 0 ∨ z e = 1) ∧ G.boundary (fun e => (z e : ℝ)) = G.boundary x ∧
      ∀ e, (x e = 0 → z e = 0) ∧ (x e = 1 → z e = 1) :=
  rounding x hx hint

end MGraph

end EulerFlow
