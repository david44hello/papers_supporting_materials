/-
Cereceda/Setting/SweepSteps.lean — abstract (short v3.90 l. 43-46): n stages, every vertex at most twice per stage.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Route: the sweep of Lemma 2.5 (Setting/Sweep.lean), keeping each step's moves as one block. A block is empty when the
current vertex is already greedy, else it is the sequence of Theorem 3.1 on the cone instance (bipartite, single-sink:
`thm_1_2_cones_proved`), along the paper's proof (`thm_3_1_of_v40` with `sec3_caseA_counts_paper_proved`), lifted
to `G` (`Sweep.isSeq_lift`); Theorem 3.1 moves every cone vertex at most twice, and the lift keeps the counts. After the n steps every vertex is greedy, so the colouring is the unique all-greedy `γ`.
-/
import Cereceda.Defs.Basic
import Cereceda.Defs.Instance
import Cereceda.Setting.Sweep
import Cereceda.Setting.Degeneracy
import Cereceda.Setting.Small
import Cereceda.Setting.CaseAPaperCounts
import Cereceda.Bip.MainV40

namespace Cereceda

open Finset

namespace SweepSteps

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}
  {ρ : V ≃ Fin n}

omit [DecidableRel G.Adj] in
/-- The lift of a list of cone moves keeps the number of moves of each vertex (0 outside the cone). -/
theorem movesOf_lift (w : V) (ms : List (ConeV G ρ w × Fin 4)) (v : V) :
    movesOf (ms.map (fun m => (m.1.1, m.2))) v = if hv : v ∈ cone G ρ w then movesOf ms ⟨v, hv⟩ else 0 := by
  unfold movesOf
  rw [List.countP_map]
  split_ifs with hv
  · congr 1
    funext m
    simp [Subtype.ext_iff]
  · rw [List.countP_eq_zero]
    intro m _
    simp only [Function.comp_apply, decide_eq_true_eq]
    intro h
    exact hv (h ▸ m.1.2)

/-- One step of the sweep as one block: if every vertex before `w` is greedy in the proper colouring `c`, a block in
which every vertex moves at most twice makes all vertices up to `w` greedy. -/
theorem step_block (hbip : G.IsBipartite) (hρ : IsDegOrder G 2 ρ) (w : V) (c : V → Fin 4) (hc : IsProperFn G c)
    (hgr : ∀ u, ρ u < ρ w → Sweep.IsGr G ρ c u) :
    ∃ ms c', IsSeq G (fun _ => univ) c ms c' ∧ (∀ v, movesOf ms v ≤ 2) ∧ (∀ m ∈ ms, m.1 ∈ cone G ρ w) ∧
      ∀ u, ρ u ≤ ρ w → Sweep.IsGr G ρ c' u := by
  obtain ⟨g, hg⟩ := Sweep.exists_isLeastFree ((laterNbrs G ρ w).image c)
    (lt_of_le_of_lt (card_image_le.trans (hρ w)) (by norm_num))
  by_cases hxg : c w = g
  · refine ⟨[], c, rfl, fun v => by simp [movesOf], fun m hm => by simp at hm, fun u hu => ?_⟩
    rcases lt_or_eq_of_le hu with h | h
    · exact hgr u h
    · have huw := ρ.injective h
      subst huw
      unfold Sweep.IsGr
      rw [hxg]
      exact hg
  · have hfree : c w ∉ (laterNbrs G ρ w).image c := by
      intro h
      obtain ⟨v, hv, hcv⟩ := mem_image.1 h
      exact hc w v (Sweep.mem_laterNbrs.1 hv).1 hcv.symm
    have hgx : g < c w := by
      rcases lt_trichotomy g (c w) with h | h | h
      · exact h
      · exact absurd h.symm hxg
      · exact absurd (hg.2.2 (c w) (mem_univ _) h) hfree
    obtain ⟨β, hβ, -⟩ := def_2_2_greedy_proved (Sweep.coneInst hρ w c g hgx) (Sweep.coneInst hρ w c g hgx).g
    have hα := Sweep.isGreedy_x hρ w c g hgx hgr
    obtain ⟨hcb, hcnr⟩ := thm_1_2_cones_proved G hbip ρ hρ w
    obtain ⟨ms, hms, hsink, hle, -⟩ := thm_3_1_of_v40 sec3_caseA_counts_paper_proved (Sweep.coneInst hρ w c g hgx)
      hcnr hcb _ β hα hβ
    refine ⟨ms.map (fun m => (m.1.1, m.2)), Sweep.glue w c β, ?_, fun v => ?_, fun m hm => ?_,
      Sweep.isGr_after hρ w c g hgx hg hgr β hβ⟩
    · have h := Sweep.isSeq_lift hρ w c g hgx hc hg.2.1 ms _ β hms
      rwa [Sweep.glue_val] at h
    · rw [movesOf_lift]
      split_ifs with hv
      · by_cases hs : (⟨v, hv⟩ : ConeV G ρ w) = (Sweep.coneInst hρ w c g hgx).sink
        · rw [hs, hsink]
          norm_num
        · exact hle _ hs
      · norm_num
    · obtain ⟨m0, -, rfl⟩ := List.mem_map.1 hm
      exact m0.1.2

/-- The sweep in blocks: from a proper colouring, `k` blocks (each moving every vertex at most twice) make the first
`k` vertices greedy. -/
theorem blocks_upto (hbip : G.IsBipartite) (hρ : IsDegOrder G 2 ρ) :
    ∀ k, k ≤ n → ∀ c : V → Fin 4, IsProperFn G c →
      ∃ steps : List (List (V × Fin 4)), ∃ c', steps.length = k ∧ IsSeq G (fun _ => univ) c steps.flatten c' ∧
        (∀ ms ∈ steps, ∀ v, movesOf ms v ≤ 2) ∧
        (∀ t, ∀ m ∈ steps.getD t [], ∀ u, (ρ u).val = t → m.1 ∈ cone G ρ u) ∧
        ∀ u, (ρ u).val < k → Sweep.IsGr G ρ c' u
  | 0, _, c, _ => ⟨[], c, rfl, rfl, by simp, fun t m hm => by simp at hm,
      fun u hu => absurd hu (Nat.not_lt_zero _)⟩
  | k + 1, hk, c, hc => by
      obtain ⟨steps, c₁, hlen, hs₁, hb₁, hcone₁, hg₁⟩ := blocks_upto hbip hρ k (by omega) c hc
      have hc₁ := Sweep.isProperFn_of_isSeq G _ steps.flatten c c₁ hs₁ hc
      have hkn : k < n := by omega
      have hρw : ρ (ρ.symm ⟨k, hkn⟩) = ⟨k, hkn⟩ := ρ.apply_symm_apply _
      obtain ⟨ms, c₂, hs₂, hb₂, hcone₂, hg₂⟩ := step_block hbip hρ (ρ.symm ⟨k, hkn⟩) c₁ hc₁
        (fun u hu => hg₁ u (by rw [hρw] at hu; exact hu))
      refine ⟨steps ++ [ms], c₂, by simp [hlen], ?_, ?_, ?_, fun u hu => hg₂ u ?_⟩
      · rw [List.flatten_append, List.flatten_singleton]
        exact Sweep.isSeq_append G _ _ _ c c₁ c₂ hs₁ hs₂
      · intro b hb
        rcases List.mem_append.1 hb with h | h
        · exact hb₁ b h
        · rw [List.mem_singleton] at h
          rw [h]
          exact hb₂
      · intro t m hm u hu
        rw [List.getD_eq_getElem?_getD] at hm
        rcases lt_or_ge t steps.length with ht | ht
        · rw [List.getElem?_append_left ht, ← List.getD_eq_getElem?_getD] at hm
          exact hcone₁ t m hm u hu
        · rw [List.getElem?_append_right ht] at hm
          rcases Nat.eq_or_lt_of_le ht with heq | hgt
          · rw [← heq, Nat.sub_self] at hm
            simp only [List.getElem?_cons_zero, Option.getD_some] at hm
            have hu' : u = ρ.symm ⟨k, hkn⟩ := by
              rw [Equiv.eq_symm_apply]
              exact Fin.ext (by simp only; omega)
            rw [hu']
            exact hcone₂ m hm
          · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t - steps.length ≠ 0)
            rw [hj] at hm
            simp at hm
      · rw [hρw, Fin.le_iff_val_le_val]
        simp only
        omega

end SweepSteps

theorem abstract_steps_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (hdeg : IsDegenerate G 2) :
    ∃ (ρ : V ≃ Fin (Fintype.card V)) (γ : V → Fin 4), IsDegOrder G 2 ρ ∧
      (∀ v, IsLeastFree univ ((laterNbrs G ρ v).image γ) (γ v)) ∧
      ∀ c : V → Fin 4, IsProperFn G c → ∃ steps : List (List (V × Fin 4)),
        steps.length = Fintype.card V ∧ IsSeq G (fun _ => univ) c steps.flatten γ ∧
        (∀ ms ∈ steps, ∀ v, movesOf ms v ≤ 2) ∧
        ∀ t (ht : t < Fintype.card V), ∀ m ∈ steps.getD t [], m.1 ∈ cone G ρ (ρ.symm ⟨t, ht⟩) := by
  obtain ⟨ρ, hρ⟩ := (sec2_order_iff_degenerate_proved G 2).2 hdeg
  obtain ⟨γ, hγ, huniq⟩ := sweep_greedy_unique_proved G ρ hρ
  refine ⟨ρ, γ, hρ, hγ, fun c hc => ?_⟩
  obtain ⟨steps, c', hlen, hs, hb, hcone, hgr⟩ := SweepSteps.blocks_upto hbip hρ _ le_rfl c hc
  have hc' : c' = γ := huniq c' (fun v => hgr v (ρ v).isLt)
  subst hc'
  exact ⟨steps, hlen, hs, hb, fun t ht m hm => hcone t m hm _ (by simp)⟩

end Cereceda
