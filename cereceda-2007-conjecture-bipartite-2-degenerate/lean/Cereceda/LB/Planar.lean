import Cereceda.Defs.LowerBound

/-!
Cereceda/LB/Planar.lean — `H_n` has a straight-line planar drawing (paper Section 4).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
## version 0.21 - 20261027_0910 — installed; namespace Cereceda.PlanarAux (no clash with team names).
## version 0.11 - 20261027 — first version.

The drawing: the path vertex `Sum.inl i` at `(i, 0)`; the apex `a = Sum.inr 0` at `(0, 1)`; the apex `b = Sum.inr 1`
at `(0, -1)`. A path edge lies on the `x`-axis; an apex edge meets the `x`-axis only at its path end.
-/

namespace Cereceda.PlanarAux

open Set

/-- The height of an apex: `Sum.inr 0` at `y = 1`, `Sum.inr 1` at `y = -1`. -/
noncomputable def apexY (c : Fin 2) : ℝ := 1 - 2 * (c.val : ℝ)

lemma apexY_cases (c : Fin 2) : apexY c = 1 ∨ apexY c = -1 := by
  rcases c with ⟨_ | _ | k, hk⟩
  · left; norm_num [apexY]
  · right; norm_num [apexY]
  · omega

lemma apexY_ne_zero (c : Fin 2) : apexY c ≠ 0 := by
  rcases apexY_cases c with h | h <;> rw [h] <;> norm_num

lemma apexY_inj {c d : Fin 2} (h : apexY c = apexY d) : c = d := by
  apply Fin.ext
  have : (c.val : ℝ) = d.val := by unfold apexY at h; linarith
  exact_mod_cast this

/-- The straight-line drawing of `H_n`. -/
noncomputable def drawH (n : ℕ) : Fin n ⊕ Fin 2 → ℝ × ℝ
  | .inl i => ((i.val : ℝ), 0)
  | .inr c => (0, apexY c)

/-- A point of a segment in the plane, in coordinates. -/
lemma seg_coords {x y z : ℝ × ℝ} (hz : z ∈ segment ℝ x y) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z.1 = x.1 + t * (y.1 - x.1) ∧ z.2 = x.2 + t * (y.2 - x.2) := by
  rw [segment_eq_image'] at hz
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hz
  exact ⟨t, ht0, ht1, by simp, by simp⟩

/-- A point of a path edge lies on the `x`-axis, between the lower end `a` and `a + 1`. -/
lemma path_seg_bounds {i j : ℕ} (h : i + 1 = j ∨ j + 1 = i) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ ((i : ℝ), (0 : ℝ)) ((j : ℝ), (0 : ℝ))) :
    z.2 = 0 ∧ ∃ a : ℕ, ((a = i ∧ j = a + 1) ∨ (a = j ∧ i = a + 1)) ∧ (a : ℝ) ≤ z.1 ∧ z.1 ≤ a + 1 := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := seg_coords hz
  have h1' : z.1 = (i : ℝ) + t * ((j : ℝ) - i) := h1
  have h2' : z.2 = 0 + t * (0 - 0) := h2
  refine ⟨by rw [h2']; ring, ?_⟩
  rcases h with h | h
  · have hj : (j : ℝ) = i + 1 := by exact_mod_cast h.symm
    have e : z.1 = i + t := by rw [h1', hj]; ring
    exact ⟨i, Or.inl ⟨rfl, h.symm⟩, by linarith, by linarith⟩
  · have hi : (i : ℝ) = j + 1 := by exact_mod_cast h.symm
    have e : z.1 = j + 1 - t := by rw [h1', hi]; ring
    exact ⟨j, Or.inr ⟨rfl, h.symm⟩, by linarith, by linarith⟩

/-- A point of an apex edge, in coordinates. -/
lemma apex_seg {i : ℕ} {c : Fin 2} {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ ((i : ℝ), (0 : ℝ)) ((0 : ℝ), apexY c)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z.1 = (1 - t) * i ∧ z.2 = t * apexY c := by
  obtain ⟨t, ht0, ht1, h1, h2⟩ := seg_coords hz
  refine ⟨t, ht0, ht1, ?_, ?_⟩
  · have h1' : z.1 = (i : ℝ) + t * (0 - i) := h1
    rw [h1']; ring
  · have h2' : z.2 = 0 + t * (apexY c - 0) := h2
    rw [h2']; ring

/-- An apex edge meets the `x`-axis only at its path end. -/
lemma apex_seg_axis {i : ℕ} {c : Fin 2} {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ ((i : ℝ), (0 : ℝ)) ((0 : ℝ), apexY c)) (h0 : z.2 = 0) : z = ((i : ℝ), 0) := by
  obtain ⟨t, -, -, h1, h2⟩ := apex_seg hz
  have ht : t = 0 := by
    rw [h0] at h2
    rcases mul_eq_zero.mp h2.symm with h | h
    · exact h
    · exact absurd h (apexY_ne_zero c)
  subst ht
  exact Prod.ext (show z.1 = (i : ℝ) by rw [h1]; ring) h0

/-- A natural number in the real interval `[a, a + 1]` is `a` or `a + 1`. -/
lemma nat_between {a m : ℕ} (h1 : (a : ℝ) ≤ m) (h2 : (m : ℝ) ≤ a + 1) : m = a ∨ m = a + 1 := by
  have h1' : a ≤ m := by exact_mod_cast h1
  have h2' : m ≤ a + 1 := by exact_mod_cast h2
  omega

/-- Two different unit intervals `[a, a + 1]`, `[b, b + 1]` (`a, b` natural) meet only in an end of the first. -/
lemma two_unit_intervals {a b : ℕ} {x : ℝ} (hab : a ≠ b) (h1 : (a : ℝ) ≤ x) (h2 : x ≤ a + 1)
    (h3 : (b : ℝ) ≤ x) (h4 : x ≤ b + 1) : ∃ m : ℕ, x = m ∧ (m = a ∨ m = a + 1) := by
  rcases (by omega : a + 2 ≤ b ∨ b + 2 ≤ a ∨ b = a + 1 ∨ a = b + 1) with h | h | h | h
  · have : (a : ℝ) + 2 ≤ b := by exact_mod_cast h
    exfalso; linarith
  · have : (b : ℝ) + 2 ≤ a := by exact_mod_cast h
    exfalso; linarith
  · have : (b : ℝ) = a + 1 := by exact_mod_cast h
    exact ⟨a + 1, by push_cast; linarith, Or.inr rfl⟩
  · have : (a : ℝ) = b + 1 := by exact_mod_cast h
    exact ⟨a, by linarith, Or.inl rfl⟩

/-- A point on the `x`-axis at an end `m` of the path edge `{i, j}` is one of the two drawn ends. -/
lemma axis_endpoint {i j a m : ℕ} {z : ℝ × ℝ} (hz2 : z.2 = 0) (hzm : z.1 = m)
    (ha : (a = i ∧ j = a + 1) ∨ (a = j ∧ i = a + 1)) (hm : m = a ∨ m = a + 1) :
    z = ((i : ℝ), 0) ∨ z = ((j : ℝ), 0) := by
  have : m = i ∨ m = j := by omega
  rcases this with rfl | rfl
  · exact Or.inl (Prod.ext hzm hz2)
  · exact Or.inr (Prod.ext hzm hz2)

/-- Two different edges, the first and second written from a path end: a common point is an end of the first. -/
lemma edge_endpoint_core {n : ℕ} {i i' : Fin n} {v v' : Fin n ⊕ Fin 2}
    (h : (Hgraph n).Adj (.inl i) v) (h' : (Hgraph n).Adj (.inl i') v')
    (hne : s(Sum.inl i, v) ≠ s(Sum.inl i', v')) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (drawH n (.inl i)) (drawH n v))
    (hz' : z ∈ segment ℝ (drawH n (.inl i')) (drawH n v')) :
    z = drawH n (.inl i) ∨ z = drawH n v := by
  rcases v with j | c <;> rcases v' with j' | c'
  · -- path edge / path edge
    have hp : i.val + 1 = j.val ∨ j.val + 1 = i.val := h
    have hp' : i'.val + 1 = j'.val ∨ j'.val + 1 = i'.val := h'
    obtain ⟨hz2, a, ha, ha1, ha2⟩ := path_seg_bounds hp hz
    obtain ⟨-, b, hb, hb1, hb2⟩ := path_seg_bounds hp' hz'
    have hab : a ≠ b := by
      rintro rfl
      apply hne
      rw [Sym2.eq_iff]
      simp only [Sum.inl.injEq, Fin.ext_iff]
      omega
    obtain ⟨m, hzm, hm⟩ := two_unit_intervals hab ha1 ha2 hb1 hb2
    exact axis_endpoint hz2 hzm ha hm
  · -- path edge / apex edge
    have hp : i.val + 1 = j.val ∨ j.val + 1 = i.val := h
    obtain ⟨hz2, a, ha, ha1, ha2⟩ := path_seg_bounds hp hz
    have hz'' := apex_seg_axis hz' hz2
    have hzm : z.1 = (i'.val : ℝ) := by rw [hz'']
    rw [hzm] at ha1 ha2
    exact axis_endpoint hz2 hzm ha (nat_between ha1 ha2)
  · -- apex edge / path edge
    have hp' : i'.val + 1 = j'.val ∨ j'.val + 1 = i'.val := h'
    obtain ⟨hz2, -⟩ := path_seg_bounds hp' hz'
    exact Or.inl (apex_seg_axis hz hz2)
  · -- apex edge / apex edge
    obtain ⟨t, ht0, ht1, h1, h2⟩ := apex_seg hz
    obtain ⟨t', ht0', ht1', h1', h2'⟩ := apex_seg hz'
    by_cases ht : t = 0
    · subst ht
      left
      exact Prod.ext (by rw [h1]; simp [drawH]) (by rw [h2]; simp [drawH])
    by_cases ht' : t = 1
    · subst ht'
      right
      exact Prod.ext (by rw [h1]; simp [drawH]) (by rw [h2]; simp [drawH])
    exfalso
    have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have htlt : t < 1 := lt_of_le_of_ne ht1 ht'
    have e2 : t * apexY c = t' * apexY c' := by rw [← h2, ← h2']
    have htt : t = t' := by
      rcases apexY_cases c with hc | hc <;> rcases apexY_cases c' with hc' | hc' <;>
        rw [hc, hc'] at e2 <;> linarith
    have hcc : c = c' := by
      apply apexY_inj
      rcases apexY_cases c with hc | hc <;> rcases apexY_cases c' with hc' | hc' <;>
        rw [hc, hc'] at e2 ⊢ <;> linarith
    subst htt hcc
    have e1 : (1 - t) * (i.val : ℝ) = (1 - t) * (i'.val : ℝ) := by rw [← h1, ← h1']
    have hii : (i.val : ℝ) = i'.val := mul_left_cancel₀ (by intro h0; linarith) e1
    have hii' : i = i' := Fin.ext (by exact_mod_cast hii)
    subst hii'
    exact hne rfl

/-- As `edge_endpoint_core`, the second edge written either way. -/
lemma edge_endpoint_half {n : ℕ} {i : Fin n} {v u' v' : Fin n ⊕ Fin 2}
    (h : (Hgraph n).Adj (.inl i) v) (h' : (Hgraph n).Adj u' v')
    (hne : s(Sum.inl i, v) ≠ s(u', v')) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (drawH n (.inl i)) (drawH n v))
    (hz' : z ∈ segment ℝ (drawH n u') (drawH n v')) :
    z = drawH n (.inl i) ∨ z = drawH n v := by
  rcases u' with i' | c'
  · exact edge_endpoint_core h h' hne hz hz'
  · rcases v' with i' | d
    · refine edge_endpoint_core h h'.symm (fun heq => hne (heq.trans Sym2.eq_swap)) hz ?_
      rw [segment_symm]; exact hz'
    · exact (h' : False).elim

/-- Two different edges of `H_n`: a common point of their drawings is an end of the first. -/
lemma edge_endpoint {n : ℕ} {u v u' v' : Fin n ⊕ Fin 2}
    (h : (Hgraph n).Adj u v) (h' : (Hgraph n).Adj u' v')
    (hne : s(u, v) ≠ s(u', v')) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (drawH n u) (drawH n v))
    (hz' : z ∈ segment ℝ (drawH n u') (drawH n v')) :
    z = drawH n u ∨ z = drawH n v := by
  rcases u with i | c
  · exact edge_endpoint_half h h' hne hz hz'
  · rcases v with i | d
    · refine (edge_endpoint_half h.symm h' (fun heq => hne (Sym2.eq_swap.trans heq)) ?_ hz').symm
      rw [segment_symm]; exact hz
    · exact (h : False).elim

/-- A drawn vertex on an edge written from its path end is an end of that edge. -/
lemma vertex_endpoint_core {n : ℕ} {i : Fin n} {v w : Fin n ⊕ Fin 2}
    (h : (Hgraph n).Adj (.inl i) v)
    (hw : drawH n w ∈ segment ℝ (drawH n (.inl i)) (drawH n v)) :
    drawH n w = drawH n (.inl i) ∨ drawH n w = drawH n v := by
  rcases v with j | c
  · have hp : i.val + 1 = j.val ∨ j.val + 1 = i.val := h
    obtain ⟨hz2, a, ha, ha1, ha2⟩ := path_seg_bounds hp hw
    rcases w with m | d
    · have hzm : (drawH n (.inl m)).1 = (m.val : ℝ) := rfl
      rw [hzm] at ha1 ha2
      exact axis_endpoint hz2 hzm ha (nat_between ha1 ha2)
    · exact absurd hz2 (apexY_ne_zero d)
  · rcases w with m | d
    · exact Or.inl (apex_seg_axis hw rfl)
    · obtain ⟨t, ht0, ht1, h1, h2⟩ := apex_seg hw
      have e : apexY d = t * apexY c := h2
      right
      have : apexY d = apexY c := by
        rcases apexY_cases c with hc | hc <;> rcases apexY_cases d with hd | hd <;>
          rw [hc, hd] at e ⊢ <;> linarith
      show ((0 : ℝ), apexY d) = (0, apexY c)
      rw [this]

/-- A drawn vertex on a drawn edge of `H_n` is an end of that edge. -/
lemma vertex_endpoint {n : ℕ} {u v w : Fin n ⊕ Fin 2} (h : (Hgraph n).Adj u v)
    (hw : drawH n w ∈ segment ℝ (drawH n u) (drawH n v)) :
    drawH n w = drawH n u ∨ drawH n w = drawH n v := by
  rcases u with i | c
  · exact vertex_endpoint_core h hw
  · rcases v with i | d
    · refine (vertex_endpoint_core h.symm ?_).symm
      rw [segment_symm]; exact hw
    · exact (h : False).elim

lemma drawH_injective (n : ℕ) : Function.Injective (drawH n) := by
  intro x y hxy
  rcases x with i | c <;> rcases y with j | d
  · have h1 : (i.val : ℝ) = j.val := congrArg Prod.fst hxy
    exact congrArg Sum.inl (Fin.ext (by exact_mod_cast h1))
  · have h2 : (0 : ℝ) = apexY d := congrArg Prod.snd hxy
    exact absurd h2.symm (apexY_ne_zero d)
  · have h2 : apexY c = 0 := congrArg Prod.snd hxy
    exact absurd h2 (apexY_ne_zero c)
  · have h2 : apexY c = apexY d := congrArg Prod.snd hxy
    exact congrArg Sum.inr (apexY_inj h2)

/-- If a point is an end of both edges, it is the drawing of a common end. -/
lemma mem_image_of_endpoints {V : Type} {p : V → ℝ × ℝ} (hinj : Function.Injective p) {u v u' v' : V}
    {z : ℝ × ℝ} (e1 : z = p u ∨ z = p v) (e2 : z = p u' ∨ z = p v') : z ∈ p '' ({u, v} ∩ {u', v'}) := by
  rcases e1 with rfl | rfl
  · refine ⟨u, ⟨by simp, ?_⟩, rfl⟩
    rcases e2 with h2 | h2
    · rw [hinj h2]; simp
    · rw [hinj h2]; simp
  · refine ⟨v, ⟨by simp, ?_⟩, rfl⟩
    rcases e2 with h2 | h2
    · rw [hinj h2]; simp
    · rw [hinj h2]; simp

theorem Hgraph_planar_proved (n : ℕ) : IsStraightLinePlanar (Hgraph n) := by
  refine ⟨drawH n, drawH_injective n, ?_, ?_⟩
  · intro u v w h hwu hwv hw
    rcases vertex_endpoint h hw with e | e
    · exact hwu (drawH_injective n e)
    · exact hwv (drawH_injective n e)
  · intro u v u' v' h h' hne z hz
    exact mem_image_of_endpoints (drawH_injective n)
      (edge_endpoint h h' hne hz.1 hz.2) (edge_endpoint h' h (Ne.symm hne) hz.2 hz.1)

end Cereceda.PlanarAux
