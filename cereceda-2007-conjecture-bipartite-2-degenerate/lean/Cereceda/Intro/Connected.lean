/-
Cereceda/Intro/Connected.lean — R_k(G) connected for k >= d+2 (DFFV06 statement, proved).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic
import Cereceda.Setting.Degeneracy

namespace Cereceda

open Finset

namespace IntroConnected

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}

/-- A move inside the vertex set `S`: recolour one `u ∈ S` to a new colour `y` that no neighbour of `u` in `S` has.
Vertices outside `S` are ignored (they "do not exist" yet). -/
def Step (S : Finset V) (a b : V → Fin k) : Prop :=
  ∃ u ∈ S, ∃ y, y ≠ a u ∧ (∀ w ∈ S, G.Adj u w → a w ≠ y) ∧ b = Function.update a u y

omit [Fintype V] in
/-- One move of `S.erase v` lifts to at most two moves of `S` (first move `v` out of the way if needed), as long as
`v` has at most `d` neighbours in `S` and `d + 2 ≤ k`. The lifted colourings agree with the old ones off `v`. -/
theorem lift_step {S : Finset V} {v : V} (hv : v ∈ S) {d : ℕ} (hdeg : (S.filter (G.Adj v)).card ≤ d)
    (hk : d + 2 ≤ k) {a b : V → Fin k} (hab : Step G (S.erase v) a b) (a' : V → Fin k)
    (ha' : ∀ x, x ≠ v → a' x = a x) :
    ∃ b', (∀ x, x ≠ v → b' x = b x) ∧ Relation.ReflTransGen (Step G S) a' b' := by
  obtain ⟨u, hu, y, hy, hfree, rfl⟩ := hab
  obtain ⟨huv, huS⟩ := mem_erase.mp hu
  have hfree' : ∀ w ∈ S, w ≠ v → G.Adj u w → a' w ≠ y := fun w hw hwv huw => by
    rw [ha' w hwv]; exact hfree w (mem_erase.mpr ⟨hwv, hw⟩) huw
  have hyu : y ≠ a' u := by rw [ha' u huv]; exact hy
  by_cases h : G.Adj u v ∧ a' v = y
  · -- `v` blocks the move: first give `v` a colour `z` not on its neighbours and different from `y`.
    have hlt : ((S.filter (G.Adj v)).image a' ∪ {y}).card < (univ : Finset (Fin k)).card := by
      have h1 := card_union_le ((S.filter (G.Adj v)).image a') {y}
      have h2 := card_image_le (s := S.filter (G.Adj v)) (f := a')
      simp only [card_univ, Fintype.card_fin, card_singleton] at h1 ⊢
      omega
    obtain ⟨z, -, hz⟩ := exists_mem_notMem_of_card_lt_card hlt
    simp only [mem_union, mem_image, mem_filter, mem_singleton, not_or, not_exists, not_and] at hz
    obtain ⟨hzN, hzy⟩ := hz
    refine ⟨Function.update (Function.update a' v z) u y, ?_, ?_⟩
    · intro x hxv
      by_cases hxu : x = u
      · subst hxu; simp
      · simp [Function.update_of_ne hxu, Function.update_of_ne hxv, ha' x hxv]
    · refine Relation.ReflTransGen.head ⟨v, hv, z, by rw [h.2]; exact hzy, ?_, rfl⟩
        (Relation.ReflTransGen.single ⟨u, huS, y, ?_, ?_, rfl⟩)
      · intro w hw hvw hwz
        exact hzN w ⟨hw, hvw⟩ hwz
      · rw [Function.update_of_ne huv]; exact hyu
      · intro w hw huw
        by_cases hwv : w = v
        · subst hwv; rw [Function.update_self]; exact fun hzy' => hzy hzy'
        · rw [Function.update_of_ne hwv]; exact hfree' w hw hwv huw
  · -- `v` does not block: make the same move.
    refine ⟨Function.update a' u y, ?_, Relation.ReflTransGen.single ⟨u, huS, y, hyu, ?_, rfl⟩⟩
    · intro x hxv
      by_cases hxu : x = u
      · subst hxu; simp
      · simp [Function.update_of_ne hxu, ha' x hxv]
    · intro w hw huw
      by_cases hwv : w = v
      · subst hwv; exact fun hy' => h ⟨huw, hy'⟩
      · exact hfree' w hw hwv huw

omit [Fintype V] in
/-- A walk of `S.erase v` lifts to a walk of `S` (colourings agree off `v`). -/
theorem lift {S : Finset V} {v : V} (hv : v ∈ S) {d : ℕ} (hdeg : (S.filter (G.Adj v)).card ≤ d)
    (hk : d + 2 ≤ k) {a b : V → Fin k} (hab : Relation.ReflTransGen (Step G (S.erase v)) a b) (a' : V → Fin k)
    (ha' : ∀ x, x ≠ v → a' x = a x) :
    ∃ b', (∀ x, x ≠ v → b' x = b x) ∧ Relation.ReflTransGen (Step G S) a' b' := by
  induction hab with
  | refl => exact ⟨a', ha', Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    obtain ⟨b', hb', hr⟩ := ih
    obtain ⟨c', hc', hr'⟩ := lift_step G hv hdeg hk hbc b' hb'
    exact ⟨c', hc', hr.trans hr'⟩

omit [DecidableEq V] in
/-- The vertex of `S` first in the order has at most `d` neighbours in `S`. -/
theorem card_nbrs_min_le {d n : ℕ} {ρ : V ≃ Fin n} (hρ : IsDegOrder G d ρ) {S : Finset V} {v : V}
    (hmin : ∀ u ∈ S, ρ v ≤ ρ u) : (S.filter (G.Adj v)).card ≤ d := by
  refine le_trans (card_le_card ?_) (hρ v)
  intro u hu
  rw [mem_filter] at hu
  simp only [laterNbrs, mem_filter, mem_univ, true_and]
  exact ⟨hu.2, lt_of_le_of_ne (hmin u hu.1) fun heq => hu.2.ne (ρ.injective heq)⟩

/-- Main claim: inside any vertex set `S`, every colouring `c` reaches every colouring `c'` that is proper on `S`
and agrees with `c` outside `S`. Induction on `S`, removing its first vertex `v` (at most `d` neighbours in `S`). -/
theorem reach {d n : ℕ} {ρ : V ≃ Fin n} (hρ : IsDegOrder G d ρ) (hk : d + 2 ≤ k) (S : Finset V) :
    ∀ c c' : V → Fin k, (∀ u ∈ S, ∀ w ∈ S, G.Adj u w → c' u ≠ c' w) → (∀ x, x ∉ S → c x = c' x) →
      Relation.ReflTransGen (Step G S) c c' := by
  induction S using Finset.strongInduction with
  | H S ih =>
    intro c c' hprop hout
    rcases S.eq_empty_or_nonempty with rfl | hne
    · have : c = c' := funext fun x => hout x (notMem_empty x)
      rw [this]
    obtain ⟨v, hv, hmin⟩ := S.exists_min_image ρ hne
    have hdeg := card_nbrs_min_le G hρ hmin
    -- the target `c'` with `v` keeping its `c`-colour: reached inside `S.erase v`
    have hsmall := ih (S.erase v) (erase_ssubset hv) c (Function.update c' v (c v))
      (fun u hu w hw huw => by
        rw [Function.update_of_ne (ne_of_mem_erase hu), Function.update_of_ne (ne_of_mem_erase hw)]
        exact hprop u (mem_of_mem_erase hu) w (mem_of_mem_erase hw) huw)
      (fun x hx => by
        by_cases hxv : x = v
        · subst hxv; simp
        · rw [Function.update_of_ne hxv]
          exact hout x fun hxS => hx (mem_erase.mpr ⟨hxv, hxS⟩))
    obtain ⟨b', hb', hr⟩ := lift G hv hdeg hk hsmall c (fun _ _ => rfl)
    have hb'' : ∀ x, x ≠ v → b' x = c' x := fun x hxv => by
      rw [hb' x hxv, Function.update_of_ne hxv]
    by_cases hbv : b' v = c' v
    · have : b' = c' := funext fun x => by
        by_cases hxv : x = v
        · subst hxv; exact hbv
        · exact hb'' x hxv
      rw [← this]; exact hr
    · -- one last move: `v` takes its `c'`-colour
      refine hr.tail ⟨v, hv, c' v, Ne.symm hbv, ?_, ?_⟩
      · intro w hw hvw
        rw [hb'' w hvw.ne.symm]
        exact (hprop v hv w hw hvw).symm
      · funext x
        by_cases hxv : x = v
        · subst hxv; simp
        · rw [Function.update_of_ne hxv, hb'' x hxv]

omit [DecidableRel G.Adj] in
/-- A walk of moves on all of `V` starting at a proper colouring is a walk of `recolGraph G k`. -/
theorem toReachable (c : G.Coloring (Fin k)) {b : V → Fin k} (h : Relation.ReflTransGen (Step G univ) (⇑c) b) :
    ∃ cb : G.Coloring (Fin k), ⇑cb = b ∧ (recolGraph G k).Reachable c cb := by
  induction h with
  | refl => exact ⟨c, rfl, SimpleGraph.Reachable.refl _⟩
  | tail _ hstep ih =>
    obtain ⟨cb, hcb, hr⟩ := ih
    obtain ⟨u, -, y, hy, hfree, rfl⟩ := hstep
    rename_i b _
    have hvalid : ∀ {x w : V}, G.Adj x w → Function.update b u y x ≠ Function.update b u y w := by
      intro x w hxw
      by_cases hxu : x = u
      · subst hxu
        rw [Function.update_self, Function.update_of_ne hxw.ne.symm]
        exact (hfree w (mem_univ w) hxw).symm
      · by_cases hwu : w = u
        · subst hwu
          rw [Function.update_self, Function.update_of_ne hxu]
          exact hfree x (mem_univ x) hxw.symm
        · rw [Function.update_of_ne hxu, Function.update_of_ne hwu, ← hcb]
          exact cb.valid hxw
    refine ⟨SimpleGraph.Coloring.mk _ hvalid, rfl, hr.trans (SimpleGraph.Adj.reachable ⟨u, ?_, ?_⟩)⟩
    · show cb u ≠ Function.update b u y u
      rw [Function.update_self, hcb]; exact hy.symm
    · intro w hwu
      show cb w = Function.update b u y w
      rw [Function.update_of_ne hwu, hcb]

end IntroConnected

theorem intro_connected_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (d k : ℕ)
    (hk : d + 2 ≤ k) (hd : IsDegenerate G d) : (recolGraph G k).Connected := by
  have hcol : G.Colorable k := (intro_degenerate_colorable_proved G d hd).mono (by omega)
  have : Nonempty (G.Coloring (Fin k)) := hcol
  obtain ⟨ρ, hρ⟩ := (sec2_order_iff_degenerate_proved G d).mpr hd
  refine SimpleGraph.Connected.mk ?_
  intro c c'
  have hr := IntroConnected.reach G hρ hk univ c c'
    (fun u _ w _ huw => c'.valid huw) (fun x hx => absurd (mem_univ x) hx)
  obtain ⟨cb, hcb, hreach⟩ := IntroConnected.toReachable G c hr
  have : cb = c' := DFunLike.coe_injective hcb
  rw [← this]; exact hreach

end Cereceda
