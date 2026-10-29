/-
Cereceda/Bip/MuV40.lean — Section 3 of short v3.90 (l. 491-547): Lemma 3.6, the greedy `μ` of Definition 3.7,
Proposition 3.8, and the step of the proof of Theorem 3.1.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route = the paper's (v3.90 l. 491-547). Lemma 3.6 (a), (b) are `Bip.fixed2_out_fixed` / `Bip.high_two_has_fixed`
(Bip/SidesFacts.lean) plus the fact that an out-neighbour of a vertex on 2 is not on 2 (`greedy_out_ne`). Proposition 3.8: `Bip.mu_step` is the induction step of the paper's
proof (a candidate for `μ(v)` exists; a fixed `v` has the candidate `α(v)`); `Bip.greedyMu` builds `μ` by recursion
along the instance order (least candidate among `0, 1, 2, 3`); uniqueness by strong induction on the rank.
-/
import Cereceda.Bip.SidesFacts

namespace Cereceda

open Finset

namespace Bip

variable {W : Type} [Fintype W] [DecidableEq W]

/-- `y` is a candidate for `μ(v)` (Definition 3.7, v3.90 l. 514-517), given the values of `μ` on the out-neighbours of `v`. -/
def MuCand (I : Instance W) (α β μ : W → Fin 4) (v : W) (y : Fin 4) : Prop :=
  y ∈ I.L v ∧ max (α v) (β v) ≤ y ∧ ∀ u ∈ I.out v, μ u ≠ y

theorem fin4_cases_le_two {a : Fin 4} (h : a ≤ 2) : a = 0 ∨ a = 1 ∨ a = 2 := by
  revert a
  decide

theorem exists_ge_one_avoid (a b : Fin 4) : ∃ y : Fin 4, 1 ≤ y ∧ y ≠ a ∧ y ≠ b := by
  revert a b
  decide

theorem exists_high_avoid (a b : Fin 4) (h : a ≤ 1 ∨ b ≤ 1) : ∃ y : Fin 4, 2 ≤ y ∧ y ≠ a ∧ y ≠ b := by
  revert a b
  decide

section V40

variable {I : Instance W} {α β : W → Fin 4} (hg0 : I.g = 0) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β)
  {side : W → Fin 2} (hside : IsProperFn I.graph side)

include hg0 hα hβ hside in
/-- Lemma 3.6 (a), v3.90 l. 493: every out-neighbour of a vertex fixed on 2 is fixed on 0 or on 1. -/
theorem twofacts_a {v : W} (hfix : IsFixed α β v) (h2 : α v = 2) {p : W} (hp : p ∈ I.out v) :
    IsFixed α β p ∧ (α p = 0 ∨ α p = 1) := by
  have hv := ne_sink_of_fixed I hα hβ hfix
  have hfp := fixed2_out_fixed hg0 hα hβ hside hv hfix h2 hp
  refine ⟨hfp, ?_⟩
  have hp2 : α p ≠ 2 := fun e => greedy_out_ne I hα hp (e.trans h2.symm)
  have hp3 := greedy_ne_three I hα (ne_sink_of_fixed I hα hβ hfp)
  revert hp2 hp3
  generalize α p = a
  revert a
  decide

include hg0 hα hβ hside in
/-- Lemma 3.6 (b), v3.90 l. 494-495: a vertex with two out-neighbours, not fixed, with the colour 2 at one end, has an
out-neighbour fixed on 0 or on 1. -/
theorem twofacts_b {v : W} (hc : (I.out v).card = 2) (hnf : ¬ IsFixed α β v) (h2 : α v = 2 ∨ β v = 2) :
    ∃ p ∈ I.out v, IsFixed α β p ∧ (α p = 0 ∨ α p = 1) := by
  have hv : v ≠ I.sink := by
    intro h
    rw [h, I.sink_out] at hc
    simp at hc
  obtain ⟨a, b, hab, hout⟩ := Finset.card_eq_two.1 hc
  have val : ∀ u ∈ I.out v, IsFixed α β u → (α u = 0 ∨ α u = 1) := by
    intro u hu hf
    have h3 := greedy_ne_three I hα (ne_sink_of_fixed I hα hβ hf)
    have hu2 : α u ≠ 2 := by
      intro e
      rcases h2 with h | h
      · exact greedy_out_ne I hα hu (e.trans h.symm)
      · exact greedy_out_ne I hβ hu ((hf.symm.trans e).trans h.symm)
    revert h3 hu2
    generalize α u = c
    revert c
    decide
  have ha : a ∈ I.out v := by rw [hout]; simp
  have hb : b ∈ I.out v := by rw [hout]; simp
  rcases high_two_has_fixed hg0 hα hβ hside hv ⟨hnf, h2⟩ (Ne.symm hab) hout with hf | hf
  · exact ⟨a, ha, hf, val a ha hf⟩
  · exact ⟨b, hb, hf, val b hb hf⟩

include hg0 hα hβ hside in
/-- The induction step of the proof of Proposition 3.8 (v3.90 l. 523-542): if `μ` is right on the out-neighbours of `v ≠ s`, then a candidate
for `μ(v)` exists, and a fixed `v` has the candidate `α(v)`. -/
theorem mu_step {μ : W → Fin 4} {v : W} (hv : v ≠ I.sink)
    (hb : ∀ u ∈ I.out v, (u = I.sink → μ u = I.x) ∧
      (u ≠ I.sink → max (α u) (β u) ≤ μ u ∧ (IsFixed α β u → μ u = α u))) :
    (∃ y, MuCand I α β μ v y) ∧ (IsFixed α β v → MuCand I α β μ v (α v)) := by
  have hαL := greedy_mem_L I hα (x_mem_L I)
  have hβL := greedy_mem_L I hβ (g_mem_L I)
  have lower : ∀ u ∈ I.out v, α u ≤ μ u ∧ β u ≤ μ u := by
    intro u hu
    by_cases hus : u = I.sink
    · rw [(hb u hu).1 hus, hus, hα.1, hβ.1, hg0]
      exact ⟨le_rfl, Fin.zero_le _⟩
    · exact max_le_iff.1 ((hb u hu).2 hus).1
  have fixedval : ∀ u ∈ I.out v, IsFixed α β u → μ u = α u := fun u hu hf =>
    ((hb u hu).2 (ne_sink_of_fixed I hα hβ hf)).2 hf
  have hle := lem_3_2_proved I α β hα hβ v hv
  -- (ii) a fixed vertex has the candidate α(v)
  have hfixcase : IsFixed α β v → MuCand I α β μ v (α v) := by
    intro hfix
    refine ⟨hαL v, max_le le_rfl (le_of_eq hfix.symm), fun u hu e => ?_⟩
    have hαu : α u ≠ α v := greedy_out_ne I hα hu
    have hβu : β u ≠ β v := greedy_out_ne I hβ hu
    have hlo := lower u hu
    rw [e] at hlo
    rcases fin4_cases_le_two hle.1 with h0 | h1 | h2
    · rw [h0] at hlo hαu
      exact hαu (le_antisymm hlo.1 (Fin.zero_le _))
    · rw [h1] at hlo hαu
      rw [← hfix, h1] at hβu
      have hα0 : α u = 0 := by
        revert hlo hαu
        generalize α u = c
        generalize β u = d
        revert c d
        decide
      have hβ0 : β u = 0 := by
        revert hlo hβu
        generalize α u = c
        generalize β u = d
        revert c d
        decide
      have hfu : IsFixed α β u := hα0.trans hβ0.symm
      have := fixedval u hu hfu
      rw [e, h1, hα0] at this
      exact absurd this (by decide)
    · obtain ⟨hfu, hval⟩ := twofacts_a hg0 hα hβ hside hfix h2 hu
      have := fixedval u hu hfu
      rw [e, h2] at this
      rcases hval with h | h <;> rw [h] at this <;> exact absurd this (by decide)
  refine ⟨?_, hfixcase⟩
  by_cases hfix : IsFixed α β v
  · exact ⟨α v, hfixcase hfix⟩
  · obtain ⟨p, hp⟩ := out_nonempty_of_not_fixed I hα hβ hv hfix
    by_cases h2 : α v = 2 ∨ β v = 2
    · -- M = 2: candidates among 2, 3
      have hM : max (α v) (β v) ≤ 2 := max_le hle.1 hle.2
      rcases out_cases I hp with h1 | ⟨q, hqp, hpq⟩
      · have h2L : (2 : Fin 4) ∈ I.L v := by
          rcases h2 with h | h
          · exact h ▸ hαL v
          · exact h ▸ hβL v
        have h3L : (3 : Fin 4) ∈ I.L v := by
          rcases h2 with h | h
          · exact three_mem_of_one I hα hv h1 h
          · exact three_mem_of_one I hβ hv h1 h
        by_cases hp2 : μ p = 2
        · refine ⟨3, h3L, le_trans hM (by decide), fun u hu => ?_⟩
          rw [h1, Finset.mem_singleton] at hu
          rw [hu, hp2]
          decide
        · refine ⟨2, h2L, hM, fun u hu => ?_⟩
          rw [h1, Finset.mem_singleton] at hu
          rw [hu]
          exact hp2
      · have hL := L_eq_univ_of_two I hqp hpq
        have hc : (I.out v).card = 2 := by
          rw [hpq]
          exact Finset.card_pair (Ne.symm hqp)
        obtain ⟨f, hf, hff, hfv⟩ := twofacts_b hg0 hα hβ hside hc hfix h2
        have hμf : μ f ≤ 1 := by
          rw [fixedval f hf hff]
          rcases hfv with h | h <;> simp [h]
        have hpq1 : μ p ≤ 1 ∨ μ q ≤ 1 := by
          rw [hpq, Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with e | e
          · exact Or.inl (e ▸ hμf)
          · exact Or.inr (e ▸ hμf)
        obtain ⟨y, hy2, hyp, hyq⟩ := exists_high_avoid (μ p) (μ q) hpq1
        refine ⟨y, by rw [hL]; exact Finset.mem_univ y, le_trans hM hy2, fun u hu => ?_⟩
        rw [hpq, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with e | e
        · rw [e]
          exact Ne.symm hyp
        · rw [e]
          exact Ne.symm hyq
    · -- M ≤ 1: candidates among 1, 2, 3
      have hM : max (α v) (β v) ≤ 1 := by
        push Not at h2
        refine max_le ?_ ?_
        · have := hle.1
          revert this h2
          generalize α v = c
          generalize β v = d
          revert c d
          decide
        · have := hle.2
          revert this h2
          generalize α v = c
          generalize β v = d
          revert c d
          decide
      rcases out_cases I hp with h1 | ⟨q, hqp, hpq⟩
      · by_contra hno
        have hsub : I.L v ⊆ {0, μ p} := by
          intro z hz
          by_cases hz0 : z = 0
          · rw [hz0]
            simp
          · have hz1 : 1 ≤ z := by
              revert hz0
              generalize z = c
              revert c
              decide
            have hz' : ∃ u ∈ I.out v, μ u = z := by
              by_contra hn
              push Not at hn
              exact hno ⟨z, hz, le_trans hM hz1, hn⟩
            obtain ⟨u, hu, hu'⟩ := hz'
            rw [h1, Finset.mem_singleton] at hu
            rw [← hu', hu]
            simp
        have h3 := L_card_of_one I h1
        have h4 := Finset.card_le_card hsub
        have h5 := Finset.card_insert_le (0 : Fin 4) ({μ p} : Finset (Fin 4))
        rw [Finset.card_singleton] at h5
        omega
      · have hL := L_eq_univ_of_two I hqp hpq
        obtain ⟨y, hy1, hyp, hyq⟩ := exists_ge_one_avoid (μ p) (μ q)
        refine ⟨y, by rw [hL]; exact Finset.mem_univ y, le_trans hM hy1, fun u hu => ?_⟩
        rw [hpq, Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with e | e
        · rw [e]
          exact Ne.symm hyp
        · rw [e]
          exact Ne.symm hyq

end V40

/-- The least colour satisfying `C`, searching `0, 1, 2, 3` (3 if none of `0, 1, 2` does). -/
def leastOf (C : Fin 4 → Prop) [DecidablePred C] : Fin 4 :=
  if C 0 then 0 else if C 1 then 1 else if C 2 then 2 else 3

theorem leastOf_spec (C : Fin 4 → Prop) [DecidablePred C] (h : ∃ y, C y) :
    C (leastOf C) ∧ ∀ y, C y → leastOf C ≤ y := by
  obtain ⟨y0, hy0⟩ := h
  have key : ∀ y : Fin 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide
  unfold leastOf
  split_ifs with h0 h1 h2
  · exact ⟨h0, fun _ _ => Fin.zero_le _⟩
  · refine ⟨h1, fun y hy => ?_⟩
    rcases key y with e | e | e | e <;> subst e
    · exact absurd hy h0
    all_goals decide
  · refine ⟨h2, fun y hy => ?_⟩
    rcases key y with e | e | e | e <;> subst e
    · exact absurd hy h0
    · exact absurd hy h1
    all_goals decide
  · have h3 : C 3 := by
      rcases key y0 with e | e | e | e <;> subst e
      · exact absurd hy0 h0
      · exact absurd hy0 h1
      · exact absurd hy0 h2
      · exact hy0
    refine ⟨h3, fun y hy => ?_⟩
    rcases key y with e | e | e | e <;> subst e
    · exact absurd hy h0
    · exact absurd hy h1
    · exact absurd hy h2
    · exact le_rfl

open Classical in
/-- Definition 3.7 (v3.90 l. 514-517) by recursion along the instance order: `μ(s) = x`; `μ(v)` = the least candidate. -/
noncomputable def greedyMu (I : Instance W) (α β : W → Fin 4) (v : W) : Fin 4 :=
  if v = I.sink then I.x
  else leastOf (fun y => y ∈ I.L v ∧ max (α v) (β v) ≤ y ∧
    ∀ u ∈ (I.out v).attach, greedyMu I α β u.1 ≠ y)
termination_by I.rank v
decreasing_by all_goals exact I.out_before _ _ (Subtype.property _)

theorem greedyMu_sink (I : Instance W) (α β : W → Fin 4) : greedyMu I α β I.sink = I.x := by
  rw [greedyMu]
  simp

/-- At `v ≠ s`, if a candidate exists, `greedyMu` takes the least candidate. -/
theorem greedyMu_ne (I : Instance W) (α β : W → Fin 4) {v : W} (hv : v ≠ I.sink)
    (hex : ∃ y, MuCand I α β (greedyMu I α β) v y) :
    MuCand I α β (greedyMu I α β) v (greedyMu I α β v) ∧
      ∀ y, MuCand I α β (greedyMu I α β) v y → greedyMu I α β v ≤ y := by
  classical
  · have hC : ∀ y, (y ∈ I.L v ∧ max (α v) (β v) ≤ y ∧ ∀ u ∈ (I.out v).attach, greedyMu I α β u.1 ≠ y) ↔
        MuCand I α β (greedyMu I α β) v y := by
      intro y
      unfold MuCand
      constructor
      · rintro ⟨a, b, c⟩
        exact ⟨a, b, fun u hu => c ⟨u, hu⟩ (Finset.mem_attach _ _)⟩
      · rintro ⟨a, b, c⟩
        exact ⟨a, b, fun u _ => c u.1 u.2⟩
    have hspec := leastOf_spec (fun y => y ∈ I.L v ∧ max (α v) (β v) ≤ y ∧
      ∀ u ∈ (I.out v).attach, greedyMu I α β u.1 ≠ y) (by obtain ⟨y, hy⟩ := hex; exact ⟨y, (hC y).2 hy⟩)
    have heq : greedyMu I α β v = leastOf (fun y => y ∈ I.L v ∧ max (α v) (β v) ≤ y ∧
        ∀ u ∈ (I.out v).attach, greedyMu I α β u.1 ≠ y) := by
      rw [greedyMu]
      simp [hv]
    rw [heq]
    exact ⟨(hC _).1 hspec.1, fun y hy => hspec.2 y ((hC y).2 hy)⟩

section Exist

variable {I : Instance W} {α β : W → Fin 4} (hg0 : I.g = 0) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β)
  {side : W → Fin 2} (hside : IsProperFn I.graph side)

include hg0 hα hβ hside in
/-- `greedyMu` follows Definition 3.7 at every vertex, and `μ(v) = α(v)` on fixed vertices (strong induction). -/
theorem greedyMu_good (v : W) :
    v ≠ I.sink → MuCand I α β (greedyMu I α β) v (greedyMu I α β v) ∧
      (∀ y, MuCand I α β (greedyMu I α β) v y → greedyMu I α β v ≤ y) ∧
      (IsFixed α β v → greedyMu I α β v = α v) := by
  induction hn : I.rank v using Nat.strong_induction_on generalizing v with
  | _ n ihn =>
    intro hv
    have hb : ∀ u ∈ I.out v, (u = I.sink → greedyMu I α β u = I.x) ∧
        (u ≠ I.sink → max (α u) (β u) ≤ greedyMu I α β u ∧ (IsFixed α β u → greedyMu I α β u = α u)) := by
      intro u hu
      refine ⟨fun h => h ▸ greedyMu_sink I α β, fun hus => ?_⟩
      have ih := ihn (I.rank u) (hn ▸ I.out_before v u hu) u rfl hus
      exact ⟨ih.1.2.1, ih.2.2⟩
    obtain ⟨hex, hfixc⟩ := mu_step hg0 hα hβ hside hv hb
    obtain ⟨hc, hleast⟩ := greedyMu_ne I α β hv hex
    refine ⟨hc, hleast, fun hfix => le_antisymm (hleast _ (hfixc hfix)) ?_⟩
    exact le_trans (le_max_left _ _) hc.2.1

end Exist

/-- Two colourings following Definition 3.7 agree (strong induction on the rank). -/
theorem greedyMu_unique {I : Instance W} {α β μ₁ μ₂ : W → Fin 4} (h₁ : IsGreedyMu I α β μ₁)
    (h₂ : IsGreedyMu I α β μ₂) (v : W) : μ₁ v = μ₂ v := by
  induction hn : I.rank v using Nat.strong_induction_on generalizing v with
  | _ n ihn =>
    by_cases hv : v = I.sink
    · rw [hv, h₁.1, h₂.1]
    · have hout : ∀ u ∈ I.out v, μ₁ u = μ₂ u := fun u hu => ihn _ (hn ▸ I.out_before v u hu) u rfl
      obtain ⟨a1, b1, c1, d1⟩ := h₁.2 v hv
      obtain ⟨a2, b2, c2, d2⟩ := h₂.2 v hv
      apply le_antisymm
      · exact d1 _ a2 b2 (fun u hu => by rw [hout u hu]; exact c2 u hu)
      · exact d2 _ a1 b1 (fun u hu => by rw [← hout u hu]; exact c1 u hu)

end Bip

/-- Lemma 3.6 (lem:twofacts), v3.90 l. 491-496. -/
theorem lem_3_6_v40_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (hg0 : I.g = 0) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∀ v, IsFixed α β v → α v = 2 → ∀ p ∈ I.out v, IsFixed α β p ∧ (α p = 0 ∨ α p = 1)) ∧
    (∀ v, (I.out v).card = 2 → ¬ IsFixed α β v → (α v = 2 ∨ β v = 2) →
      ∃ p ∈ I.out v, IsFixed α β p ∧ (α p = 0 ∨ α p = 1)) := by
  have _hnr := hnr  -- the paper's hypothesis "single-sink"; the proof does not need it
  obtain ⟨C⟩ := hbip
  have hside : IsProperFn I.graph (fun w => C w) := fun u w huw => C.valid huw
  exact ⟨fun v hfix h2 p hp => Bip.twofacts_a hg0 hα hβ hside hfix h2 hp,
    fun v hc hnf h2 => Bip.twofacts_b hg0 hα hβ hside hc hnf h2⟩

/-- Proposition 3.8 (prop:mu), v3.90 l. 519-521: `μ` of Definition 3.7 exists and is unique, and
`μ(v) = α(v)` for every fixed vertex `v`. -/
theorem prop_3_8_v40_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (hg0 : I.g = 0) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    (∃! μ, IsGreedyMu I α β μ) ∧ ∀ μ, IsGreedyMu I α β μ → ∀ v, IsFixed α β v → μ v = α v := by
  have _hnr := hnr  -- the paper's hypothesis "single-sink"; the proof does not need it
  obtain ⟨C⟩ := hbip
  have hside : IsProperFn I.graph (fun w => C w) := fun u w huw => C.valid huw
  have hgood := fun v => Bip.greedyMu_good hg0 hα hβ hside (I := I) v
  have hG : IsGreedyMu I α β (Bip.greedyMu I α β) := by
    refine ⟨Bip.greedyMu_sink I α β, fun v hv => ?_⟩
    obtain ⟨⟨a, b, c⟩, d, _⟩ := hgood v hv
    exact ⟨a, b, c, fun y hy1 hy2 hy3 => d y ⟨hy1, hy2, hy3⟩⟩
  refine ⟨⟨Bip.greedyMu I α β, hG, fun μ hμ => funext fun v => Bip.greedyMu_unique hμ hG v⟩, ?_⟩
  intro μ hμ v hfix
  rw [Bip.greedyMu_unique hμ hG v]
  exact (hgood v (Bip.ne_sink_of_fixed I hα hβ hfix)).2.2 hfix

/-- Proof of Theorem 3.1, v3.90 l. 545-547: the greedy `μ` satisfies the hypotheses of Lemma 3.4. -/
theorem thm_3_1_mu_v40_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (hg0 : I.g = 0) (α β : W → Fin 4)
    (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) (μ : W → Fin 4) (hμ : IsGreedyMu I α β μ) :
    IsProperFn I.graph μ ∧ (∀ v, μ v ∈ I.L v) ∧ (∀ v, α v ≤ μ v ∧ β v ≤ μ v) ∧ μ I.sink = I.x := by
  have _hyp : I.NoRoots ∧ I.graph.IsBipartite ∧ I.g = 0 := ⟨hnr, hbip, hg0⟩  -- the paper's hypotheses; not needed here
  refine ⟨fun u v huv => ?_, fun v => ?_, fun v => ?_, hμ.1⟩
  · rcases Bip.mem_out_of_adj huv with h | h
    · exact ((hμ.2 u (Bip.ne_sink_of_mem_out h)).2.2.1 v h).symm
    · exact (hμ.2 v (Bip.ne_sink_of_mem_out h)).2.2.1 u h
  · by_cases hv : v = I.sink
    · rw [hv, hμ.1]
      exact Bip.x_mem_L I
    · exact (hμ.2 v hv).1
  · by_cases hv : v = I.sink
    · rw [hv, hμ.1, hα.1, hβ.1]
      exact ⟨le_rfl, le_of_lt I.g_lt_x⟩
    · exact max_le_iff.1 (hμ.2 v hv).2.1

end Cereceda
