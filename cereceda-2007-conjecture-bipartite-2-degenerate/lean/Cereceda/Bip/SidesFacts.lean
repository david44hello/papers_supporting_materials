/-
Cereceda/Bip/SidesFacts.lean — facts on greedy colourings and the sides of a bipartite instance (case g = 0) for Lemma 3.6.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Moved from Bip/Roles.lean (deleted with the earlier proof route of Theorem 3.1), content unchanged: the facts that
Bip/MuV40.lean uses. Two facts from Lemma 3.5 carry Lemma 3.6 of v3.90 (l. 491-496): every out-neighbour of a vertex
fixed on 2 is fixed (`fixed2_out_fixed`, case (a)), and a high mover with two out-neighbours has a fixed one
(`high_two_has_fixed`, case (c)); each ends in a finite check over the patterns of Lemma 3.5.
-/
import Cereceda.Bip.Sides

namespace Cereceda

open Finset

namespace Bip

variable {W : Type} [Fintype W] [DecidableEq W]

section Facts

theorem leastFree_unique {L U : Finset (Fin 4)} {y y' : Fin 4} (h : IsLeastFree L U y)
    (h' : IsLeastFree L U y') : y = y' := by
  rcases lt_trichotomy y y' with hlt | heq | hgt
  · exact absurd (h'.2.2 y h.1 hlt) h.2.1
  · exact heq
  · exact absurd (h.2.2 y' h'.1 hgt) h'.2.1

theorem sink_not_fixed (I : Instance W) {α β : W → Fin 4} (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ¬ IsFixed α β I.sink := by
  unfold IsFixed
  rw [hα.1, hβ.1]
  exact ne_of_gt I.g_lt_x

theorem ne_sink_of_fixed (I : Instance W) {α β : W → Fin 4} (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β)
    {v : W} (h : IsFixed α β v) : v ≠ I.sink := fun e => sink_not_fixed I hα hβ (e ▸ h)

/-- A vertex without out-neighbours is fixed (both greedy colours are the least colour of its list). -/
theorem out_nonempty_of_not_fixed (I : Instance W) {α β : W → Fin 4} (hα : I.IsGreedy I.x α)
    (hβ : I.IsGreedy I.g β) {v : W} (hv : v ≠ I.sink) (hnf : ¬ IsFixed α β v) : (I.out v).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  apply hnf
  have h1 := hα.2 v hv
  have h2 := hβ.2 v hv
  rw [h, Finset.image_empty] at h1 h2
  exact leastFree_unique h1 h2

theorem out_cases (I : Instance W) {v p : W} (hp : p ∈ I.out v) :
    I.out v = {p} ∨ ∃ q, q ≠ p ∧ I.out v = {p, q} := by
  have h2 := I.out_card v
  have h1 : 0 < (I.out v).card := Finset.card_pos.2 ⟨p, hp⟩
  have hc : (I.out v).card = 1 ∨ (I.out v).card = 2 := by omega
  rcases hc with hc | hc
  · left
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    rw [ha] at hp ⊢
    rw [Finset.mem_singleton.1 hp]
  · right
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.1 hc
    rw [he] at hp
    rcases Finset.mem_insert.1 hp with h | h
    · exact ⟨b, fun e => hab (h.symm.trans e.symm), by rw [he, h]⟩
    · rw [Finset.mem_singleton] at h
      exact ⟨a, fun e => hab (e.trans h), by rw [he, h, Finset.pair_comm]⟩

theorem L_eq_univ_of_two (I : Instance W) {v p q : W} (hpq : q ≠ p) (h : I.out v = {p, q}) : I.L v = univ := by
  apply Finset.eq_univ_of_card
  have h1 := I.L_card v
  have h2 := Finset.card_le_univ (I.L v)
  have h3 : (I.out v).card = 2 := by
    rw [h]
    exact Finset.card_pair (Ne.symm hpq)
  simp only [Fintype.card_fin] at h2 ⊢
  omega

theorem L_card_of_one (I : Instance W) {v p : W} (h : I.out v = {p}) : 3 ≤ (I.L v).card := by
  have h1 := I.L_card v
  rw [h, Finset.card_singleton] at h1
  exact h1

theorem exists_low_of_three {L : Finset (Fin 4)} (h : 3 ≤ L.card) : ∃ z ∈ L, z < 2 := by
  by_contra hne
  push Not at hne
  have hsub : L ⊆ {2, 3} := by
    intro z hz
    have key : ∀ z : Fin 4, 2 ≤ z → z ∈ ({2, 3} : Finset (Fin 4)) := by decide
    exact key z (hne z hz)
  have := Finset.card_le_card hsub
  have h23 : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
  omega

/-- With one out-neighbour, a vertex whose greedy colour is 2 has 3 in its list. -/
theorem three_mem_of_one (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c) {v p : W}
    (hv : v ≠ I.sink) (h : I.out v = {p}) (h2 : c v = 2) : (3 : Fin 4) ∈ I.L v := by
  by_contra h3
  have hsub : I.L v ⊆ {c p, 2} := by
    intro z hz
    have key : ∀ z : Fin 4, z ≠ 3 → z ≠ 2 → z < 2 := by decide
    by_cases hz2 : z = 2
    · rw [hz2]
      simp
    · have hlt := key z (fun e => h3 (e ▸ hz)) hz2
      obtain ⟨u, hu, hcu⟩ := greedy_below I hc hv hz (h2 ▸ hlt)
      rw [h, Finset.mem_singleton] at hu
      rw [← hcu, hu]
      simp
  have h1 := Finset.card_le_card hsub
  have h2' := Finset.card_insert_le (c p) ({2} : Finset (Fin 4))
  have h3' := L_card_of_one I h
  rw [Finset.card_singleton] at h2'
  omega

/-- Two out-neighbours `p, q` of a vertex whose greedy colour is 2 (list `{0,1,2,3}`) hold the colours 0 and 1. -/
theorem cover01 (I : Instance W) {c0 : Fin 4} {c : W → Fin 4} (hc : I.IsGreedy c0 c) {v p q : W}
    (hv : v ≠ I.sink) (hpq : q ≠ p) (h : I.out v = {p, q}) (h2 : c v = 2) :
    (c p = 0 ∨ c q = 0) ∧ (c p = 1 ∨ c q = 1) := by
  have hL := L_eq_univ_of_two I hpq h
  have get : ∀ z : Fin 4, z < 2 → (c p = z ∨ c q = z) := by
    intro z hz
    obtain ⟨u, hu, hcu⟩ := greedy_below I hc hv (by rw [hL]; exact Finset.mem_univ z) (h2 ▸ hz)
    rw [h, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu | hu
    · exact Or.inl (hu ▸ hcu)
    · exact Or.inr (hu ▸ hcu)
  exact ⟨get 0 (by decide), get 1 (by decide)⟩

end Facts

section SideFacts

variable {I : Instance W} {α β : W → Fin 4} (hg0 : I.g = 0) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β)
  {side : W → Fin 2} (hside : IsProperFn I.graph side)

theorem leaver_joiner_of_cover (ap bp aq bq : Fin 4) (h1 : ap = 0 ∨ aq = 0) (h2 : ap = 1 ∨ aq = 1)
    (h3 : bp = 0 ∨ bq = 0) (h4 : bp = 1 ∨ bq = 1) (hne : ap ≠ bp) :
    (ap = 0 ∧ bp ≠ 0 ∧ aq ≠ 0 ∧ bq = 0) ∨ (ap ≠ 0 ∧ bp = 0 ∧ aq = 0 ∧ bq ≠ 0) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
    subst_vars <;> simp_all

include hg0 hα hβ hside in
/-- A leaver lies away from the sink (Lemma 3.5). -/
theorem leaver_away {u : W} (h0 : α u = 0) (hb : β u ≠ 0) : side u ≠ side I.sink := by
  intro hs
  have hus : u ≠ I.sink := fun e => x_ne_zero I (by rw [← hα.1, ← e, h0])
  have hmem := (sides hg0 hα hβ hside u).1 hus hs
  rw [h0] at hmem
  revert hmem hb
  generalize β u = b
  revert b
  decide

include hg0 hα hβ hside in
/-- A joiner lies on the side of the sink (Lemma 3.5). -/
theorem joiner_home {u : W} (ha : α u ≠ 0) (h0 : β u = 0) : side u = side I.sink := by
  by_contra hs
  have hmem := (sides hg0 hα hβ hside u).2 hs
  rw [h0] at hmem
  revert hmem ha
  generalize α u = a
  revert a
  decide

include hg0 hα hβ hside in
/-- Proof of Prop 3.7, case (a): every out-neighbour of a vertex fixed on 2 is fixed. -/
theorem fixed2_out_fixed {v : W} (hv : v ≠ I.sink) (hfix : IsFixed α β v) (h2 : α v = 2) {p : W}
    (hp : p ∈ I.out v) : IsFixed α β p := by
  have hβ2 : β v = 2 := hfix ▸ h2
  rcases out_cases I hp with h1 | ⟨q, hqp, hpq⟩
  · obtain ⟨z, hz, hzlt⟩ := exists_low_of_three (L_card_of_one I h1)
    obtain ⟨u, hu, hαu⟩ := greedy_below I hα hv hz (h2 ▸ hzlt)
    obtain ⟨u', hu', hβu'⟩ := greedy_below I hβ hv hz (hβ2 ▸ hzlt)
    rw [h1, Finset.mem_singleton] at hu hu'
    subst hu hu'
    unfold IsFixed
    rw [hαu, hβu']
  · by_contra hnf
    have cα := cover01 I hα hv hqp hpq h2
    have cβ := cover01 I hβ hv hqp hpq hβ2
    have hsp := hside v p (adj_of_mem_out hp)
    have hsq := hside v q (adj_of_mem_out (by rw [hpq]; simp))
    have hsame : side p = side q := fin2_eq_of_ne_ne (Ne.symm hsp) hsq
    rcases leaver_joiner_of_cover _ _ _ _ cα.1 cα.2 cβ.1 cβ.2 hnf with h | h
    · exact leaver_away hg0 hα hβ hside h.1 h.2.1
        (hsame.trans (joiner_home hg0 hα hβ hside h.2.2.1 h.2.2.2))
    · exact leaver_away hg0 hα hβ hside h.2.2.1 h.2.2.2
        (hsame.symm.trans (joiner_home hg0 hα hβ hside h.1 h.2.1))

theorem high_two_S0 : ∀ ab ∈ patS0, ∀ pp ∈ patS1, ∀ qq ∈ patS1,
    (ab.1 ≠ ab.2 ∧ (ab.1 = 2 ∨ ab.2 = 2)) →
    (ab.1 = 2 → (pp.1 = 0 ∨ qq.1 = 0) ∧ (pp.1 = 1 ∨ qq.1 = 1)) →
    (ab.2 = 2 → (pp.2 = 0 ∨ qq.2 = 0) ∧ (pp.2 = 1 ∨ qq.2 = 1)) → pp.1 = pp.2 ∨ qq.1 = qq.2 := by
  decide

theorem high_two_S1 : ∀ ab ∈ patS1, ∀ pp ∈ insert (3, 0) patS0, ∀ qq ∈ insert (3, 0) patS0,
    (ab.1 ≠ ab.2 ∧ (ab.1 = 2 ∨ ab.2 = 2)) →
    (ab.1 = 2 → (pp.1 = 0 ∨ qq.1 = 0) ∧ (pp.1 = 1 ∨ qq.1 = 1)) →
    (ab.2 = 2 → (pp.2 = 0 ∨ qq.2 = 0) ∧ (pp.2 = 1 ∨ qq.2 = 1)) → pp.1 = pp.2 ∨ qq.1 = qq.2 := by
  decide

include hg0 hα hβ hside in
/-- A vertex on the side of the sink has a pattern in `patS0` or is the sink (pattern `(x, 0)`). -/
theorem pat_side0 {u : W} (hu : side u = side I.sink) :
    (α u, β u) ∈ insert ((3 : Fin 4), (0 : Fin 4)) patS0 := by
  by_cases hus : u = I.sink
  · rw [hus, hα.1, hβ.1, hg0]
    have hx := x_ne_zero I
    revert hx
    generalize I.x = y
    revert y
    decide
  · exact Finset.mem_insert_of_mem ((sides hg0 hα hβ hside u).1 hus hu)

include hg0 hα hβ hside in
/-- Proof of Prop 3.7, case (c): a high mover with two out-neighbours has a fixed out-neighbour. -/
theorem high_two_has_fixed {v p q : W} (hv : v ≠ I.sink) (hh : IsHighMover α β v) (hqp : q ≠ p)
    (hpq : I.out v = {p, q}) : IsFixed α β p ∨ IsFixed α β q := by
  have hpm : p ∈ I.out v := by rw [hpq]; simp
  have hqm : q ∈ I.out v := by rw [hpq]; simp
  have cα : α v = 2 → (α p = 0 ∨ α q = 0) ∧ (α p = 1 ∨ α q = 1) := cover01 I hα hv hqp hpq
  have cβ : β v = 2 → (β p = 0 ∨ β q = 0) ∧ (β p = 1 ∨ β q = 1) := cover01 I hβ hv hqp hpq
  have hsp := hside v p (adj_of_mem_out hpm)
  have hsq := hside v q (adj_of_mem_out hqm)
  unfold IsFixed
  by_cases hs : side v = side I.sink
  · have hab := (sides hg0 hα hβ hside v).1 hv hs
    have hpp := (sides hg0 hα hβ hside p).2 (hs ▸ (Ne.symm hsp))
    have hqq := (sides hg0 hα hβ hside q).2 (hs ▸ (Ne.symm hsq))
    exact high_two_S0 _ hab _ hpp _ hqq hh cα cβ
  · have hab := (sides hg0 hα hβ hside v).2 hs
    have hpp := pat_side0 hg0 hα hβ hside (fin2_eq_of_ne_ne (Ne.symm hsp) hs)
    have hqq := pat_side0 hg0 hα hβ hside (fin2_eq_of_ne_ne (Ne.symm hsq) hs)
    exact high_two_S1 _ hab _ hpp _ hqq hh cα cβ

end SideFacts

end Bip

end Cereceda
