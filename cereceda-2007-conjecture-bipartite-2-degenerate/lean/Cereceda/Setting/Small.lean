/-
Cereceda/Setting/Small.lean — small Section 2 claims (cones, greedy, sequences, sweep's gamma), and two facts of the
proof of Theorem 1.2 (short v3.90 l. 568-570: the cone instances are single-sink, and bipartite when `G` is).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance

namespace Cereceda

open Finset

namespace Small

/-- A function defined by well-founded recursion through `dep`: existence and uniqueness of a solution of the
local equations `Q v (values on dep v) (value at v)`, when `Q` has exactly one solution for every small enough
set of used values. -/
theorem wf_existsUnique {W α : Type} [DecidableEq α] (r : W → W → Prop) (hr : WellFounded r)
    (dep : W → Finset W) (hdep : ∀ v, ∀ u ∈ dep v, r u v) (Q : W → Finset α → α → Prop)
    (hex : ∀ v (S : Finset α), S.card ≤ (dep v).card → ∃ y, Q v S y)
    (huniq : ∀ v S y y', Q v S y → Q v S y' → y = y') :
    ∃! c : W → α, ∀ v, Q v ((dep v).image c) (c v) := by
  classical
  -- existence: recursion along `r`
  let F : ∀ v, (∀ u, r u v → α) → α := fun v rec =>
    Classical.choose (hex v ((dep v).attach.image (fun u => rec u.1 (hdep v u.1 u.2)))
      (card_image_le.trans (by simp)))
  let c : W → α := hr.fix F
  have hc : ∀ v, c v = F v (fun u _ => c u) := fun v => hr.fix_eq F v
  have himg : ∀ v, (dep v).attach.image (fun u => c u.1) = (dep v).image c := by
    intro v
    ext y
    simp
  have hsol : ∀ v, Q v ((dep v).image c) (c v) := by
    intro v
    have hspec := Classical.choose_spec (hex v ((dep v).attach.image (fun u => c u.1))
      (card_image_le.trans (by simp)))
    have hval : c v = Classical.choose (hex v ((dep v).attach.image (fun u => c u.1))
      (card_image_le.trans (by simp))) := hc v
    rw [hval, ← himg v]
    exact hspec
  refine ⟨c, hsol, ?_⟩
  · intro c' hc'
    funext v
    induction v using hr.induction with
    | _ v ih =>
      have heq : (dep v).image c' = (dep v).image c := by
        apply Finset.image_congr
        intro u hu
        exact ih u (hdep v u hu)
      have h1 := hc' v
      rw [heq] at h1
      exact huniq v _ _ _ h1 (hsol v)

theorem isLeastFree_unique {L S : Finset (Fin 4)} {y y' : Fin 4} (h : IsLeastFree L S y)
    (h' : IsLeastFree L S y') : y = y' := by
  rcases lt_trichotomy y y' with hlt | heq | hgt
  · exact absurd (h'.2.2 y h.1 hlt) h.2.1
  · exact heq
  · exact absurd (h.2.2 y' h'.1 hgt) h'.2.1

theorem isLeastFree_exists {L S : Finset (Fin 4)} (hne : (L \ S).Nonempty) : ∃ y, IsLeastFree L S y := by
  refine ⟨(L \ S).min' hne, ?_, ?_, ?_⟩
  · exact (mem_sdiff.mp ((L \ S).min'_mem hne)).1
  · exact (mem_sdiff.mp ((L \ S).min'_mem hne)).2
  · intro z hz hlt
    by_contra hzS
    exact absurd ((L \ S).min'_le z (mem_sdiff.mpr ⟨hz, hzS⟩)) (not_le.mpr hlt)

theorem sdiff_nonempty_of_card {L S : Finset (Fin 4)} (h : S.card < L.card) : (L \ S).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have := Finset.sdiff_eq_empty_iff_subset.mp he
  exact absurd (Finset.card_le_card this) (not_le.mpr h)

end Small

open Cereceda.Small

theorem def_2_1_cones_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n) :
    (∀ w, w ∈ cone G ρ w) ∧ (∀ w u, u ∈ cone G ρ w → ρ u ≤ ρ w) ∧
      2 * ∑ w, (cone G ρ w).card ≤ n * (n + 1) := by
  classical
  refine ⟨fun w => mem_cone_self G ρ w, fun _ _ h => le_of_mem_cone h, ?_⟩
  have hle : ∀ w, (cone G ρ w).card ≤ (ρ w).val + 1 := by
    intro w
    have hsub : cone G ρ w ⊆ (Finset.Iic (ρ w)).map ρ.symm.toEmbedding := by
      intro u hu
      simp only [mem_map_equiv, Equiv.symm_symm, mem_Iic]
      exact le_of_mem_cone hu
    refine (card_le_card hsub).trans ?_
    simp
  have hsum : ∑ w, (cone G ρ w).card ≤ ∑ w, ((ρ w).val + 1) := sum_le_sum (fun w _ => hle w)
  have hre : ∑ w, ((ρ w).val + 1) = ∑ i : Fin n, (i.val + 1) :=
    Fintype.sum_equiv ρ _ _ (fun _ => rfl)
  have hgauss : ∀ m : ℕ, 2 * ∑ i ∈ range m, (i + 1) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih => rw [sum_range_succ, mul_add, ih]; ring
  have hfin : ∑ i : Fin n, (i.val + 1) = ∑ i ∈ range n, (i + 1) := Fin.sum_univ_eq_sum_range (fun i => i + 1) n
  calc 2 * ∑ w, (cone G ρ w).card ≤ 2 * ∑ w, ((ρ w).val + 1) := Nat.mul_le_mul_left 2 hsum
    _ = n * (n + 1) := by rw [hre, hfin, hgauss]

theorem def_2_2_greedy_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) :
    ∃! c, I.IsGreedy c0 c := by
  classical
  have key := wf_existsUnique (fun u v => I.rank u < I.rank v) (InvImage.wf I.rank Nat.lt_wfRel.wf)
    I.out (fun v u hu => I.out_before v u hu)
    (fun v S y => if v = I.sink then y = c0 else IsLeastFree (I.L v) S y)
    (by
      intro v S hS
      by_cases hv : v = I.sink
      · exact ⟨c0, by simp [hv]⟩
      · simp only [hv, ite_false]
        exact isLeastFree_exists (sdiff_nonempty_of_card (by have := I.L_card v; omega)))
    (by
      intro v S y y' h h'
      by_cases hv : v = I.sink
      · simp only [hv, ite_true] at h h'
        rw [h, h']
      · simp only [hv, ite_false] at h h'
        exact isLeastFree_unique h h')
  obtain ⟨c, hc, huniq⟩ := key
  have hiff : ∀ c' : W → Fin 4, I.IsGreedy c0 c' ↔
      ∀ v, (if v = I.sink then c' v = c0 else IsLeastFree (I.L v) ((I.out v).image c') (c' v)) := by
    intro c'
    constructor
    · rintro ⟨hs, hv⟩ v
      by_cases h : v = I.sink
      · simp only [h, ite_true]; exact hs
      · simp only [h, ite_false]; exact hv v h
    · intro h
      refine ⟨by simpa using h I.sink, fun v hv => ?_⟩
      have := h v
      simpa [hv] using this
  exact ⟨c, (hiff c).mpr hc, fun c' hc' => huniq c' ((hiff c').mp hc')⟩

theorem def_2_2_seq_proper_proved {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) (A : W → Finset (Fin 4))
    (c c' : W → Fin 4) (ms : List (W × Fin 4)) (hs : IsSeq H A c ms c') (hc : IsProperFn H c)
    (hA : ∀ v, c v ∈ A v) (k : ℕ) :
    IsProperFn H (applyMoves c (ms.take k)) ∧ ∀ v, applyMoves c (ms.take k) v ∈ A v := by
  induction ms generalizing c k with
  | nil => simpa [applyMoves] using ⟨hc, hA⟩
  | cons m ms ih =>
    cases k with
    | zero => simpa [applyMoves] using ⟨hc, hA⟩
    | succ k =>
      obtain ⟨hm, hrest⟩ := hs
      have hc1 : IsProperFn H (Function.update c m.1 m.2) := by
        intro u v huv
        by_cases hu : u = m.1
        · subst hu
          have hv : v ≠ m.1 := fun h => H.loopless.irrefl _ (h ▸ huv)
          rw [Function.update_self, Function.update_of_ne hv]
          exact (hm.2.2 v huv).symm
        · by_cases hv : v = m.1
          · subst hv
            rw [Function.update_self, Function.update_of_ne hu]
            exact hm.2.2 u (H.symm.symm _ _ huv)
          · rw [Function.update_of_ne hu, Function.update_of_ne hv]
            exact hc u v huv
      have hA1 : ∀ v, Function.update c m.1 m.2 v ∈ A v := by
        intro v
        by_cases hv : v = m.1
        · subst hv; rw [Function.update_self]; exact hm.2.1
        · rw [Function.update_of_ne hv]; exact hA v
      have := ih (Function.update c m.1 m.2) hrest hc1 hA1 k
      simpa [applyMoves, List.take_succ_cons, List.foldl_cons] using this

theorem sweep_greedy_unique_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) :
    ∃! γ : V → Fin 4, ∀ v, IsLeastFree univ ((laterNbrs G ρ v).image γ) (γ v) := by
  classical
  refine wf_existsUnique (fun u v => ρ v < ρ u) (InvImage.wf (fun v => ρ v) wellFounded_gt)
    (laterNbrs G ρ) (fun v u hu => by
      simp only [laterNbrs, mem_filter, mem_univ, true_and] at hu
      exact hu.2)
    (fun _ S y => IsLeastFree univ S y)
    (fun v S hS => isLeastFree_exists (sdiff_nonempty_of_card (by
      have := hρ v
      simp only [card_univ, Fintype.card_fin]
      omega)))
    (fun _ _ _ _ h h' => isLeastFree_unique h h')

theorem thm_1_2_cone_out_neighbour_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V) :
    (coneSkeleton G ρ hρ w).NoRoots := by
  classical
  rintro u ⟨hus, hout⟩
  have hu := u.2
  simp only [cone, mem_filter, mem_univ, true_and] at hu
  obtain ⟨_, hpath⟩ := hu
  have hne : u.1 ≠ w := fun h => hus (Subtype.ext h)
  rcases Relation.ReflTransGen.cases_head hpath with h | ⟨b, ⟨harc, _, hbw⟩, hbpath⟩
  · exact hne h
  · have hb : b ∈ cone G ρ w := by
      simp only [cone, mem_filter, mem_univ, true_and]
      exact ⟨hbw, hbpath⟩
    have hmem : (⟨b, hb⟩ : ConeV G ρ w) ∈ (coneSkeleton G ρ hρ w).out u := by
      simp only [coneSkeleton, mem_filter, mem_attach, true_and]
      exact harc
    rw [hout] at hmem
    simp at hmem

theorem thm_1_2_cones_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) {n : ℕ} (ρ : V ≃ Fin n) (hρ : IsDegOrder G 2 ρ) (w : V) :
    (coneSkeleton G ρ hρ w).graph.IsBipartite ∧ (coneSkeleton G ρ hρ w).NoRoots := by
  classical
  refine ⟨?_, thm_1_2_cone_out_neighbour_proved G ρ hρ w⟩
  obtain ⟨C⟩ := hbip
  refine ⟨SimpleGraph.Coloring.mk (fun u => C u.1) ?_⟩
  intro u v huv
  simp only [Skeleton.graph, SimpleGraph.fromRel_adj] at huv
  obtain ⟨_, h⟩ := huv
  have hadj : G.Adj u.1 v.1 := by
    rcases h with h | h
    · simp only [coneSkeleton, mem_filter, mem_attach, true_and] at h
      exact h.1
    · simp only [coneSkeleton, mem_filter, mem_attach, true_and] at h
      exact h.1.symm
  exact C.valid hadj

theorem def_2_1_cone_reach_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {n : ℕ} (ρ : V ≃ Fin n)
    (w u : V) : u ∈ cone G ρ w ↔ Relation.ReflTransGen (Arc G ρ) u w := by
  classical
  simp only [cone, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩
    exact Relation.ReflTransGen.mono (fun a b (hab : Arc G ρ a b ∧ ρ a ≤ ρ w ∧ ρ b ≤ ρ w) => hab.1) _ _ h
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨le_rfl, Relation.ReflTransGen.refl⟩
    | head hab _ ih =>
      obtain ⟨hb, hpath⟩ := ih
      have hlt := hab.2
      exact ⟨le_of_lt (lt_of_lt_of_le hlt hb),
        Relation.ReflTransGen.head ⟨hab, le_of_lt (lt_of_lt_of_le hlt hb), hb⟩ hpath⟩

end Cereceda
