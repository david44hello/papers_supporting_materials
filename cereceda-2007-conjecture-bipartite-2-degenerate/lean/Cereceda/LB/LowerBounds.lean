/-
Cereceda/LB/LowerBounds.lean — Propositions 4.1 (prop:LBH) and 4.6 (prop:LB6) of the paper (short version,
Section 4): every walk from σ⁺ to σ⁻ in R_4 is long.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route = the paper's (short v3.90 l. 644-660 and 705-714). Along a walk, as long as all colourings are plain, Lemma 4.2
carries a height function, and each move changes `∑ |h_t - h_0|` by at most `2`. If no apex ever moves, the height goes
from all steps `+1` to all steps `-1` (cost `(n²-1)/2`). Otherwise, just before the first apex move the colouring is
flat (Lemma 4.3 / 4.7), so Lemma 4.4 gives `q²/8 ≤ 2·(moves before)`; reading the walk backwards from σ⁻, the same
holds after the last apex move (mirror form of Lemma 4.4). The two parts are disjoint.
The `diam` parts take `ediam ≠ ⊤` (connectivity of R_4, from Theorem 1.2) as a hypothesis.
-/
import Cereceda.LB.Moves
import Cereceda.LB.Cost

namespace Cereceda.LBAux

open Finset MovesAux

variable {n k : ℕ} {f : Fin n → Fin k}

/-! ### σ⁺ and σ⁻ as colourings, and their heights -/

theorem sigmaPlus_valid {u v : Fin n ⊕ Fin k} (huv : (pathApex n k f).Adj u v) :
    sigmaPlus n k u ≠ sigmaPlus n k v := by
  rcases u with i | i <;> rcases v with j | j
  · intro e
    have e' := congrArg Fin.val e
    simp only [sigmaPlus] at e'
    have : i.val + 1 = j.val ∨ j.val + 1 = i.val := huv
    omega
  · intro e
    have e' := congrArg Fin.val e
    simp only [sigmaPlus] at e'
    omega
  · intro e
    have e' := congrArg Fin.val e
    simp only [sigmaPlus] at e'
    omega
  · exact absurd huv id

theorem sigmaMinus_valid {u v : Fin n ⊕ Fin k} (huv : (pathApex n k f).Adj u v) :
    sigmaMinus n k u ≠ sigmaMinus n k v := by
  rcases u with i | i <;> rcases v with j | j
  · intro e
    have e' := congrArg Fin.val e
    simp only [sigmaMinus] at e'
    have : i.val + 1 = j.val ∨ j.val + 1 = i.val := huv
    omega
  · intro e
    have e' := congrArg Fin.val e
    simp only [sigmaMinus] at e'
    omega
  · intro e
    have e' := congrArg Fin.val e
    simp only [sigmaMinus] at e'
    omega
  · exact absurd huv id

/-- σ⁺ as a proper colouring. -/
def sigmaPlusCol (n k : ℕ) (f : Fin n → Fin k) : (pathApex n k f).Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk (sigmaPlus n k) sigmaPlus_valid

/-- σ⁻ as a proper colouring. -/
def sigmaMinusCol (n k : ℕ) (f : Fin n → Fin k) : (pathApex n k f).Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk (sigmaMinus n k) sigmaMinus_valid

theorem sigmaPlus_plain : IsPlain (sigmaPlus n k) := fun _ => rfl

theorem sigmaMinus_plain : IsPlain (sigmaMinus n k) := fun _ => rfl

theorem sp_res (i : ℕ) (hi : i < n) :
    ((((sigmaPlus n k (.inl ⟨i, hi⟩)).val : ℕ)) : ZMod 3) = ((i : ℕ) : ZMod 3) := by
  show (((i % 3 : ℕ)) : ZMod 3) = ((i : ℕ) : ZMod 3)
  rw [ZMod.natCast_mod]

theorem sm_res (i : ℕ) (hi : i < n) :
    ((((sigmaMinus n k (.inl ⟨i, hi⟩)).val : ℕ)) : ZMod 3) = -((i : ℕ) : ZMod 3) := by
  show ((((3 - i % 3) % 3 : ℕ)) : ZMod 3) = -((i : ℕ) : ZMod 3)
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega : i % 3 ≤ 3), ZMod.natCast_mod]
  have h3 : ((3 : ℕ) : ZMod 3) = 0 := ZMod.natCast_self 3
  rw [h3, zero_sub]

/-- `i ↦ i` is a height of σ⁺ (all steps `+1`). -/
theorem sp_height : IsPathHeight (sigmaPlus n k) (fun i => (i : ℤ)) := by
  intro i hi
  refine ⟨Or.inl (by push_cast; ring), ?_⟩
  rw [sp_res, sp_res]
  push_cast
  ring

/-- `i ↦ -i` is a height of σ⁻ (all steps `-1`). -/
theorem sm_height : IsPathHeight (sigmaMinus n k) (fun i => -(i : ℤ)) := by
  intro i hi
  refine ⟨Or.inr (by push_cast; ring), ?_⟩
  rw [sm_res, sm_res]
  push_cast
  ring

/-- Every height of σ⁻ has all steps `-1`. -/
theorem sm_steps (g : ℕ → ℤ) (hg : IsPathHeight (sigmaMinus n k) g) :
    ∀ i, i + 1 < n → g (i + 1) - g i = -1 := by
  intro i hi
  obtain ⟨hs, hm⟩ := hg i hi
  rcases hs with e | e
  · exfalso
    rw [e, sm_res, sm_res] at hm
    push_cast at hm
    have : (1 : ZMod 3) = -1 := by linear_combination hm
    revert this
    decide
  · exact e

/-- The steps of any height are `±1`. -/
theorem height_steps {c : Fin n ⊕ Fin k → Fin 4} {g : ℕ → ℤ} (hg : IsPathHeight c g) :
    ∀ i, i + 1 < n → g (i + 1) - g i = 1 ∨ g (i + 1) - g i = -1 := fun i hi => (hg i hi).1

/-! ### Tracking a height along a walk -/

theorem proper_of_coloring (x : (pathApex n k f).Coloring (Fin 4)) : IsProperFn (pathApex n k f) ⇑x :=
  fun _ _ huv => x.valid huv

/-- One step of `R_4` between plain colourings carries a height, and moves `∑ |· - r|` by at most `2`. -/
theorem step_track (x y : (pathApex n k f).Coloring (Fin 4)) (hxy : (recolGraph (pathApex n k f) 4).Adj x y)
    (hpx : IsPlain ⇑x) (hpy : IsPlain ⇑y) (hx : ℕ → ℤ) (hhx : IsPathHeight ⇑x hx) (r : ℕ → ℤ) :
    ∃ hy, IsPathHeight ⇑y hy ∧ ∑ j ∈ range n, |hy j - r j| ≤ ∑ j ∈ range n, |hx j - r j| + 2 := by
  obtain ⟨v, hv, hw⟩ := hxy
  rcases v with i | j
  · have hmove : LegalMove (pathApex n k f) (fun _ => univ) ⇑x (.inl i, y (.inl i)) := by
      refine ⟨fun e => hv e.symm, Finset.mem_univ _, fun u hu => ?_⟩
      rw [hw u (hu.ne.symm)]
      exact (y.valid hu).symm
    obtain ⟨ε, hε, hh'⟩ := lem_4_2_proved n k f x y (proper_of_coloring x) hpx hpy i hmove
      (fun w hw' => (hw w hw').symm) hx hhx
    refine ⟨_, hh', PathAux.l1_step r hx _ i.val (fun j hj => Function.update_of_ne hj _ _) ?_⟩
    rw [Function.update_self]
    rcases hε with rfl | rfl <;> norm_num
  · exact absurd (by rw [hpx j, hpy j]) hv

/-- Along a sequence of colourings, consecutive ones adjacent in `R_4` and all plain, a height of the first one is
carried to a height of the `m`-th one, with `∑ |h_m - h_0| ≤ 2m`. -/
theorem seq_track (X : ℕ → (pathApex n k f).Coloring (Fin 4)) (m : ℕ)
    (hadj : ∀ s, s < m → (recolGraph (pathApex n k f) 4).Adj (X s) (X (s + 1)))
    (hplain : ∀ s, s ≤ m → IsPlain ⇑(X s)) (h0 : ℕ → ℤ) (hh0 : IsPathHeight ⇑(X 0) h0) :
    ∃ hm, IsPathHeight ⇑(X m) hm ∧ ∑ j ∈ range n, |hm j - h0 j| ≤ 2 * m := by
  induction m with
  | zero => exact ⟨h0, hh0, by simp⟩
  | succ m ih =>
    obtain ⟨hm, hhm, hb⟩ := ih (fun s hs => hadj s (by omega)) (fun s hs => hplain s (by omega))
    obtain ⟨hm', hhm', hb'⟩ := step_track (X m) (X (m + 1)) (hadj m (by omega)) (hplain m (by omega))
      (hplain (m + 1) le_rfl) hm hhm h0
    exact ⟨hm', hhm', by push_cast; linarith⟩

/-- A plain colouring adjacent in `R_4` to a colouring that is not plain allows a move of an apex. -/
theorem apex_move_of_adj (x y : (pathApex n k f).Coloring (Fin 4))
    (hxy : (recolGraph (pathApex n k f) 4).Adj x y) (hpx : IsPlain ⇑x) (hpy : ¬ IsPlain ⇑y) :
    ∃ j z, LegalMove (pathApex n k f) (fun _ => univ) ⇑x (.inr j, z) := by
  obtain ⟨v, hv, hw⟩ := hxy
  obtain ⟨j, hj⟩ : ∃ j, y (.inr j) ≠ 3 := by
    simp only [IsPlain, not_forall] at hpy
    exact hpy
  have hvj : v = .inr j := by
    by_contra hne
    apply hj
    rw [← hw (.inr j) (fun e => hne e.symm)]
    exact hpx j
  subst hvj
  refine ⟨j, y (.inr j), fun e => hv e.symm, Finset.mem_univ _, fun u hu => ?_⟩
  rw [hw u hu.ne.symm]
  exact (y.valid hu).symm

/-! ### The lower bound for every walk from σ⁺ to σ⁻ -/

/-- The common core of Propositions 4.1 and 4.6. `hflat`: in every plain proper colouring that allows an apex move,
every height has `-(n-1) + q ≤ W ≤ (n-1) - q` (Lemma 4.3 / 4.7). Then every walk from σ⁺ to σ⁻ has length at least
`q²/8` (needs `q²/8 ≤ (n²-1)/4` for the case without apex moves). -/
theorem walk_lower_bound (q : ℝ) (hq : 0 ≤ q) (hqn : q / 4 + 1 ≤ (n : ℝ) / 2)
    (hfull : q ^ 2 / 8 ≤ ((n : ℝ) ^ 2 - 1) / 4)
    (hflat : ∀ c : Fin n ⊕ Fin k → Fin 4, IsProperFn (pathApex n k f) c → IsPlain c →
      (∃ j y, LegalMove (pathApex n k f) (fun _ => univ) c (.inr j, y)) → ∀ g, IsPathHeight c g →
        ((g (n - 1) - g 0 : ℤ) : ℝ) ≤ ((n : ℝ) - 1) - q ∧ -((n : ℝ) - 1) + q ≤ ((g (n - 1) - g 0 : ℤ) : ℝ))
    (p : (recolGraph (pathApex n k f) 4).Walk (sigmaPlusCol n k f) (sigmaMinusCol n k f)) :
    q ^ 2 / 8 ≤ p.length := by
  classical
  set L := p.length with hL
  have hX0 : p.getVert 0 = sigmaPlusCol n k f := p.getVert_zero
  have hXL : p.getVert L = sigmaMinusCol n k f := p.getVert_length
  have hadjF : ∀ s, s < L → (recolGraph (pathApex n k f) 4).Adj (p.getVert s) (p.getVert (s + 1)) :=
    fun s hs => p.adj_getVert_succ hs
  by_cases hall : ∀ t, t ≤ L → IsPlain ⇑(p.getVert t)
  · -- no apex ever moves: full reversal
    obtain ⟨g, hg, hb⟩ := seq_track (fun t => p.getVert t) L hadjF hall (fun i => (i : ℤ))
      (by rw [hX0]; exact sp_height)
    rw [hXL] at hg
    have hrev := PathAux.full_reversal (n := n) (fun i => (i : ℤ)) g
      (fun i _ => by push_cast; ring) (sm_steps g hg)
    have hZ : (n : ℤ) ^ 2 - 1 ≤ 4 * L := by linarith
    have hR : ((n : ℝ) ^ 2 - 1) ≤ 4 * (L : ℝ) := by exact_mod_cast hZ
    linarith
  · simp only [not_forall, exists_prop] at hall
    have hex : ∃ t, t ≤ L ∧ ¬ IsPlain ⇑(p.getVert t) := hall
    set P : ℕ → Prop := fun t => ¬ IsPlain ⇑(p.getVert t) with hP
    -- the first colouring that is not plain
    set t1 := Nat.find hex with ht1
    obtain ⟨ht1L, ht1P⟩ := Nat.find_spec hex
    have hbefore : ∀ s, s < t1 → IsPlain ⇑(p.getVert s) := by
      intro s hs
      have := Nat.find_min hex hs
      by_contra hc
      exact this ⟨by omega, hc⟩
    have ht1pos : 0 < t1 := by
      rcases Nat.eq_zero_or_pos t1 with h0 | h0
      · exfalso; apply ht1P; rw [← ht1, h0, hX0]; exact sigmaPlus_plain
      · exact h0
    -- the last colouring that is not plain
    set t2 := Nat.findGreatest P L with ht2
    have ht2P : P t2 := Nat.findGreatest_spec ht1L ht1P
    have ht12 : t1 ≤ t2 := Nat.le_findGreatest ht1L ht1P
    have ht2L : t2 < L := by
      rcases lt_or_eq_of_le (Nat.findGreatest_le (P := P) L) with h | h
      · exact h
      · exfalso; apply ht2P; rw [ht2, h, hXL]; exact sigmaMinus_plain
    have hafter : ∀ s, t2 < s → s ≤ L → IsPlain ⇑(p.getVert s) := by
      intro s hs hsL
      have := Nat.findGreatest_is_greatest hs hsL
      simp only [hP, not_not] at this
      exact this
    -- forward part: before the first apex move
    obtain ⟨g1, hg1, hb1⟩ := seq_track (fun t => p.getVert t) (t1 - 1)
      (fun s hs => hadjF s (by omega)) (fun s hs => hbefore s (by omega)) (fun i => (i : ℤ))
      (by rw [hX0]; exact sp_height)
    have hmove1 := apex_move_of_adj (p.getVert (t1 - 1)) (p.getVert t1)
      (by have := hadjF (t1 - 1) (by omega); rwa [show t1 - 1 + 1 = t1 by omega] at this)
      (hbefore _ (by omega)) ht1P
    have hW1 := hflat _ (proper_of_coloring _) (hbefore _ (by omega)) hmove1 g1 hg1
    have hc1 := cost_proved n (fun i => (i : ℤ)) g1 q (fun i _ => by push_cast; ring) (height_steps hg1) hq
      hW1.1 hqn
    -- backward part: after the last apex move, read from σ⁻
    obtain ⟨g2, hg2, hb2⟩ := seq_track (fun s => p.getVert (L - s)) (L - t2 - 1)
      (fun s hs => by
        have := (hadjF (L - s - 1) (by omega)).symm
        rwa [show L - s - 1 + 1 = L - s by omega, show L - s - 1 = L - (s + 1) by omega] at this)
      (fun s hs => hafter _ (by omega) (by omega)) (fun i => -(i : ℤ))
      (by simp only [Nat.sub_zero]; rw [hXL]; exact sm_height)
    simp only [show L - (L - t2 - 1) = t2 + 1 by omega] at hg2
    have hmove2 := apex_move_of_adj (p.getVert (t2 + 1)) (p.getVert t2) (hadjF t2 ht2L).symm
      (hafter _ (by omega) (by omega)) ht2P
    have hW2 := hflat _ (proper_of_coloring _) (hafter _ (by omega) (by omega)) hmove2 g2 hg2
    have hc2 := cost_mirror_proved n (fun i => -(i : ℤ)) g2 q (fun i _ => by push_cast; ring)
      (height_steps hg2) hq hW2.2 hqn
    -- combine
    have hb1R : ((∑ j ∈ range n, |g1 j - (j : ℤ)| : ℤ) : ℝ) ≤ 2 * ((t1 - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb1
    have hb2R : ((∑ j ∈ range n, |g2 j - -(j : ℤ)| : ℤ) : ℝ) ≤ 2 * ((L - t2 - 1 : ℕ) : ℝ) := by
      exact_mod_cast hb2
    rw [Int.cast_sum] at hb1R hb2R
    have hcount : ((t1 - 1 : ℕ) : ℝ) + ((L - t2 - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
      have : (t1 - 1) + (L - t2 - 1) ≤ L := by omega
      exact_mod_cast this
    have e1 : q ^ 2 / 8 ≤ 2 * ((t1 - 1 : ℕ) : ℝ) := hc1.trans hb1R
    have e2 : q ^ 2 / 8 ≤ 2 * ((L - t2 - 1 : ℕ) : ℝ) := hc2.trans hb2R
    linarith

/-- From a lower bound on every walk between two colourings to a lower bound on `diam`, when `R_4` has finite
`ediam` (then it is connected and `dist ≤ diam`). -/
theorem diam_ge_of_walks {G : SimpleGraph (Fin n ⊕ Fin k)} (x y : G.Coloring (Fin 4)) (B : ℝ)
    (hw : ∀ p : (recolGraph G 4).Walk x y, B ≤ p.length) (hfin : (recolGraph G 4).ediam ≠ ⊤) :
    B ≤ ((recolGraph G 4).diam : ℝ) := by
  obtain ⟨p, hp⟩ := (SimpleGraph.preconnected_of_ediam_ne_top hfin x y).exists_walk_length_eq_dist
  have h1 := hw p
  have h2 : (recolGraph G 4).dist x y ≤ (recolGraph G 4).diam := SimpleGraph.dist_le_diam hfin
  rw [hp] at h1
  have h2' : ((recolGraph G 4).dist x y : ℝ) ≤ ((recolGraph G 4).diam : ℝ) := by exact_mod_cast h2
  linarith

end Cereceda.LBAux

namespace Cereceda

open Finset LBAux

/-- **Proposition 4.1 (prop:LBH)** (v3.90 l. 586-589), with connectivity of `R_4(H_n)` (from Theorem 1.2) as the
hypothesis `hfin` for the `diam` part. -/
theorem prop_4_1_proved (n : ℕ) (hn : 5 ≤ n) (hfin : (recolGraph (Hgraph n) 4).ediam ≠ ⊤) :
    (∃ σp σm : (Hgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 2 ∧ ⇑σm = sigmaMinus n 2 ∧
      ∀ p : (recolGraph (Hgraph n) 4).Walk σp σm, ((n : ℝ) - 5) ^ 2 / 8 ≤ p.length) ∧
    ((((n + 2 : ℕ) : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph (Hgraph n) 4).diam : ℝ)) := by
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hwalk : ∀ p : (recolGraph (Hgraph n) 4).Walk (sigmaPlusCol n 2 _) (sigmaMinusCol n 2 _),
      ((n : ℝ) - 5) ^ 2 / 8 ≤ p.length := by
    intro p
    refine walk_lower_bound ((n : ℝ) - 5) (by linarith) (by linarith) (by nlinarith) ?_ p
    intro c hc hp hmove g hg
    have hW := abs_le.mp (lem_4_3_proved n c hc hp hmove g hg)
    have e1 : ((g (n - 1) - g 0 : ℤ) : ℝ) ≤ 4 := by exact_mod_cast hW.2
    have e2 : (-4 : ℝ) ≤ ((g (n - 1) - g 0 : ℤ) : ℝ) := by exact_mod_cast hW.1
    constructor <;> linarith
  refine ⟨⟨sigmaPlusCol n 2 _, sigmaMinusCol n 2 _, rfl, rfl, hwalk⟩, ?_⟩
  have e : (((n + 2 : ℕ) : ℝ) - 7) = (n : ℝ) - 5 := by push_cast; ring
  rw [e]
  exact diam_ge_of_walks _ _ _ hwalk hfin

/-- **Proposition 4.6 (prop:LB6)** (v3.90 l. 681-683), with connectivity of `R_4(J_n)` (from Theorem 1.2) as the
hypothesis `hfin` for the `diam` part. -/
theorem prop_4_6_proved (n : ℕ) (hn : 29 ≤ n) (hfin : (recolGraph (Jgraph n) 4).ediam ≠ ⊤) :
    (∃ σp σm : (Jgraph n).Coloring (Fin 4), ⇑σp = sigmaPlus n 4 ∧ ⇑σm = sigmaMinus n 4 ∧
      ∀ p : (recolGraph (Jgraph n) 4).Walk σp σm, ((n : ℝ) - 29) ^ 2 / 128 ≤ p.length) ∧
    ((((n + 4 : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph n) 4).diam : ℝ)) := by
  have hn' : (29 : ℝ) ≤ n := by exact_mod_cast hn
  have hwalk : ∀ p : (recolGraph (Jgraph n) 4).Walk (sigmaPlusCol n 4 _) (sigmaMinusCol n 4 _),
      ((n : ℝ) - 29) ^ 2 / 128 ≤ p.length := by
    intro p
    have hq : ((n : ℝ) - 29) ^ 2 / 128 = (((n : ℝ) - 29) / 4) ^ 2 / 8 := by ring
    rw [hq]
    refine walk_lower_bound (((n : ℝ) - 29) / 4) (by linarith) (by linarith) (by nlinarith) ?_ p
    intro c hc hp hmove g hg
    have hW := abs_le.mp (lem_4_7_proved n c hc hp hmove g hg)
    push_cast
    constructor <;> linarith [hW.1, hW.2]
  refine ⟨⟨sigmaPlusCol n 4 _, sigmaMinusCol n 4 _, rfl, rfl, hwalk⟩, ?_⟩
  have e : (((n + 4 : ℕ) : ℝ) - 33) = (n : ℝ) - 29 := by push_cast; ring
  rw [e]
  exact diam_ge_of_walks _ _ _ hwalk hfin

end Cereceda
