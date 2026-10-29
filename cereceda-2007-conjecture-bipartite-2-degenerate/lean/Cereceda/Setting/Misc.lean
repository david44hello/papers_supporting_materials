/-
Cereceda/Setting/Misc.lean — small claims: Grundy number is a maximum, five colours, two out-neighbours -> full list,
limits.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Intro
import Cereceda.Defs.Instance
import Cereceda.Setting.Small
import Cereceda.Setting.CaseA

namespace Cereceda

open Finset

namespace Misc

/-- The least natural number outside a finite set exists. -/
theorem exists_least_not_mem (S : Finset ℕ) : ∃ y, y ∉ S ∧ ∀ z < y, z ∈ S := by
  classical
  have hex : ∃ y, y ∉ S := ⟨S.sup id + 1, fun h => by
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun z hz => ?_⟩
  by_contra hzS
  exact absurd (Nat.find_min' hex hzS) (not_le.mpr hz)

/-- Every order has a greedy colouring `C(G, O)`. -/
theorem exists_greedyRel {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {n : ℕ}
    (ρ : V ≃ Fin n) : ∃ c : V → ℕ, IsGreedyRel G ρ c := by
  obtain ⟨c, hc, -⟩ := Small.wf_existsUnique (fun u v => ρ u < ρ v) (InvImage.wf (fun v => ρ v) wellFounded_lt)
    (fun v => univ.filter (fun u => G.Adj v u ∧ ρ u < ρ v))
    (fun v u hu => by simp only [mem_filter, mem_univ, true_and] at hu; exact hu.2)
    (fun _ S y => y ∉ S ∧ ∀ z < y, z ∈ S)
    (fun _ S _ => exists_least_not_mem S)
    (fun _ S y y' h h' => by
      rcases lt_trichotomy y y' with hlt | heq | hgt
      · exact absurd (h'.2 y hlt) h.1
      · exact heq
      · exact absurd (h.2 y' hgt) h'.1)
  exact ⟨c, hc⟩

/-- A colour graph with a vertex and a finite bound on `ediam` is connected (`ediam` is `⊤` when disconnected). Used for
the connectivity parts of Theorem 1.2 and of the class statements. -/
theorem recolGraph_connected_of_ediam_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k B : ℕ)
    (hk : G.Colorable k) (h : (recolGraph G k).ediam ≤ (B : ℕ∞)) : (recolGraph G k).Connected := by
  haveI : Nonempty (G.Coloring (Fin k)) := hk
  exact SimpleGraph.connected_of_ediam_ne_top (ne_top_of_le_ne_top (ENat.coe_ne_top _) h)

end Misc

theorem grundyNumber_spec_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∃ (ρ : V ≃ Fin (Fintype.card V)) (c : V → ℕ), IsGreedyRel G ρ c ∧ (univ.image c).card = grundyNumber G) ∧
    ∀ (ρ : V ≃ Fin (Fintype.card V)) (c : V → ℕ), IsGreedyRel G ρ c → (univ.image c).card ≤ grundyNumber G := by
  set S : Set ℕ := {k | ∃ ρ : V ≃ Fin (Fintype.card V), ∃ c : V → ℕ, IsGreedyRel G ρ c ∧ (univ.image c).card = k}
    with hS
  have hne : S.Nonempty := by
    obtain ⟨c, hc⟩ := Misc.exists_greedyRel G (Fintype.equivFin V)
    exact ⟨_, Fintype.equivFin V, c, hc, rfl⟩
  have hbdd : BddAbove S := by
    refine ⟨Fintype.card V, ?_⟩
    rintro k ⟨ρ, c, -, rfl⟩
    exact card_image_le.trans (by simp)
  have hgr : grundyNumber G = sSup S := rfl
  refine ⟨?_, fun ρ c hc => ?_⟩
  · obtain ⟨ρ, c, hc, hk⟩ := Nat.sSup_mem hne hbdd
    exact ⟨ρ, c, hc, hk.trans hgr.symm⟩
  · rw [hgr]
    exact le_csSup hbdd ⟨ρ, c, hc, rfl⟩

theorem intro_five_colours_proved (k : ℕ) : ((3 : ℝ) / 2 * (2 + 1) ≤ k ↔ 5 ≤ k) := by
  constructor
  · intro h
    by_contra hk
    have : (k : ℝ) ≤ 4 := by exact_mod_cast (by omega : k ≤ 4)
    linarith
  · intro h
    have : (5 : ℝ) ≤ k := by exact_mod_cast h
    linarith

theorem sec3_two_out_full_list_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (v : W)
    (hv : (I.out v).card = 2) : I.L v = univ := by
  apply Finset.eq_univ_of_card
  have h1 := I.L_card v
  have h2 : (I.L v).card ≤ Fintype.card (Fin 4) := card_le_univ _
  simp only [Fintype.card_fin] at h2 ⊢
  omega

theorem open_3_limits_proved :
    Filter.Tendsto (fun n : ℕ => (2 * n * (n + 1) : ℝ) / (n : ℝ) ^ 2) Filter.atTop (nhds 2) ∧
    Filter.Tendsto (fun N : ℕ => ((N : ℝ) - 7) ^ 2 / 8 / (N : ℝ) ^ 2) Filter.atTop (nhds (1 / 8)) := by
  have h0 : ∀ a : ℝ, Filter.Tendsto (fun n : ℕ => a / (n : ℝ)) Filter.atTop (nhds 0) :=
    fun a => tendsto_const_div_atTop_nhds_zero_nat a
  constructor
  · have hlim : Filter.Tendsto (fun n : ℕ => 2 + 2 / (n : ℝ)) Filter.atTop (nhds (2 + 0)) :=
      tendsto_const_nhds.add (h0 2)
    rw [add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    field_simp
  · have hlim : Filter.Tendsto (fun N : ℕ => (1 - 7 / (N : ℝ)) ^ 2 / 8) Filter.atTop (nhds ((1 - 0) ^ 2 / 8)) :=
      ((tendsto_const_nhds.sub (h0 7)).pow 2).div_const 8
    rw [sub_zero, one_pow] at hlim
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    field_simp

theorem lem_2_3_K_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) : ∀ v, α v = 0 ↔ β v = 0 :=
  CaseA.zero_iff hg hα hβ

theorem lem_2_3_F1_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) (v : W) (hv : c v ≠ 0) : ((I.out v).filter (fun u => c u ≠ 0)).card ≤ 1 := by
  rcases eq_or_ne v I.sink with rfl | hvs
  · rw [I.sink_out]; simp
  · rw [Finset.card_le_one]
    intro a ha b hb
    simp only [mem_filter] at ha hb
    by_contra hab
    exact hb.2 (CaseA.parent_others_zero hc hvs hv ha.1 ha.2 b hb.1 (fun h => hab h.symm))

theorem lem_2_3_F2_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (c0 : Fin 4) (c : W → Fin 4)
    (hc : I.IsGreedy c0 c) (v p : W) (hv : c v ≠ 0) (hp : p ∈ I.out v) (hcp : c p ≠ 0) :
    ({1, 2, 3} : Finset (Fin 4)) ⊆ I.L v := by
  have hvs : v ≠ I.sink := CaseA.ne_sink_of_mem_out hp
  intro z hz
  exact CaseA.parent_lists hc hvs hv hp hcp z (by simp only [mem_insert, mem_singleton] at hz; omega)

end Cereceda
