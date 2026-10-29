/-
Cereceda/Setting/Degeneracy.lean — degeneracy: orders, subgraph form, (d+1)-colouring.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Basic

namespace Cereceda

open Finset

namespace Degeneracy

variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Removal ranks on a finite set `s`: repeatedly remove a vertex with at most `d` neighbours in the remaining set;
the vertex removed first gets rank `0`. Ranks are injective on `s`, smaller than `#s`, and every `v ∈ s` has at
most `d` neighbours in `s` of larger rank. -/
theorem exists_rank (d : ℕ) (hd : IsDegenerate G d) (s : Finset V) :
    ∃ f : V → ℕ, Set.InjOn f s ∧ (∀ v ∈ s, f v < s.card) ∧
      ∀ v ∈ s, (s.filter (fun u => G.Adj v u ∧ f v < f u)).card ≤ d := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp, by simp, by simp⟩
    obtain ⟨v, hv, hvd⟩ := hd s hne
    obtain ⟨f', hinj, hlt, hlater⟩ := ih (s.erase v) (erase_ssubset hv)
    refine ⟨fun u => if u = v then 0 else f' u + 1, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      by_cases hav : a = v <;> by_cases hbv : b = v
      · rw [hav, hbv]
      · simp [hav, hbv] at hab
      · simp [hav, hbv] at hab
      · simp only [hav, hbv, ite_false] at hab
        exact hinj (mem_erase.mpr ⟨hav, ha⟩) (mem_erase.mpr ⟨hbv, hb⟩) (by omega)
    · intro u hu
      have hcard := card_erase_of_mem hv
      have hpos : 0 < s.card := card_pos.mpr hne
      by_cases huv : u = v
      · simp [huv, hpos]
      · have := hlt u (mem_erase.mpr ⟨huv, hu⟩)
        simp only [huv, ite_false]
        omega
    · intro u hu
      by_cases huv : u = v
      · subst huv
        refine le_trans (card_le_card ?_) hvd
        intro w hw
        simp only [mem_filter] at hw ⊢
        exact ⟨hw.1, hw.2.1⟩
      · refine le_trans (card_le_card ?_) (hlater u (mem_erase.mpr ⟨huv, hu⟩))
        intro w hw
        simp only [mem_filter, huv, ite_false] at hw ⊢
        have hwv : w ≠ v := by
          rintro rfl
          simp at hw
        simp only [hwv, ite_false] at hw
        exact ⟨mem_erase.mpr ⟨hwv, hw.1⟩, hw.2.1, by omega⟩

/-- Greedy colouring on a finite set `s`: colour `s` minus a vertex `v` with at most `d` neighbours in `s`, then give
`v` a colour of `Fin (d + 1)` that none of these at most `d` neighbours has. -/
theorem exists_coloring_on (d : ℕ) (hd : IsDegenerate G d) (s : Finset V) :
    ∃ c : V → Fin (d + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨fun _ => 0, by simp⟩
    obtain ⟨v, hv, hvd⟩ := hd s hne
    obtain ⟨c', hc'⟩ := ih (s.erase v) (erase_ssubset hv)
    have hlt : ((s.filter (G.Adj v)).image c').card < (univ : Finset (Fin (d + 1))).card := by
      have := card_image_le (s := s.filter (G.Adj v)) (f := c')
      simp only [card_univ, Fintype.card_fin]
      omega
    obtain ⟨col, -, hcol⟩ := exists_mem_notMem_of_card_lt_card hlt
    have hfree : ∀ w ∈ s, G.Adj v w → col ≠ c' w := by
      intro w hw hvw heq
      exact hcol (mem_image.mpr ⟨w, mem_filter.mpr ⟨hw, hvw⟩, heq.symm⟩)
    refine ⟨Function.update c' v col, ?_⟩
    intro u hu w hw huw
    by_cases huv : u = v
    · subst huv
      have hwu : w ≠ u := huw.ne.symm
      rw [Function.update_self, Function.update_of_ne hwu]
      exact hfree w hw huw
    · by_cases hwv : w = v
      · subst hwv
        rw [Function.update_self, Function.update_of_ne huv]
        exact (hfree u hu huw.symm).symm
      · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
        exact hc' u (mem_erase.mpr ⟨huv, hu⟩) w (mem_erase.mpr ⟨hwv, hw⟩) huw

end Degeneracy

theorem sec2_order_iff_degenerate_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) :
    (∃ ρ : V ≃ Fin (Fintype.card V), IsDegOrder G d ρ) ↔ IsDegenerate G d := by
  constructor
  · rintro ⟨ρ, hρ⟩ s hs
    obtain ⟨v, hv, hmin⟩ := s.exists_min_image ρ hs
    refine ⟨v, hv, le_trans (card_le_card ?_) (hρ v)⟩
    intro u hu
    rw [mem_filter] at hu
    simp only [laterNbrs, mem_filter, mem_univ, true_and]
    exact ⟨hu.2, lt_of_le_of_ne (hmin u hu.1) fun heq => hu.2.ne (ρ.injective heq)⟩
  · intro hd
    obtain ⟨f, hinj, hlt, hlater⟩ := Degeneracy.exists_rank G d hd univ
    have hlt' : ∀ v, f v < Fintype.card V := fun v => by simpa using hlt v (mem_univ v)
    have hinj' : Function.Injective (fun v => (⟨f v, hlt' v⟩ : Fin (Fintype.card V))) := by
      intro a b hab
      exact hinj (mem_coe.mpr (mem_univ a)) (mem_coe.mpr (mem_univ b)) (congrArg Fin.val hab)
    let ρ := Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj', by simp⟩)
    refine ⟨ρ, fun v => le_trans (le_of_eq ?_) (hlater v (mem_univ v))⟩
    unfold laterNbrs
    congr 1

theorem degenerate_iff_subgraph_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) :
    IsDegenerate G d ↔ ∀ H : G.Subgraph, H.verts.Nonempty → ∃ v ∈ H.verts, (H.neighborSet v).ncard ≤ d := by
  classical
  constructor
  · intro hd H hH
    obtain ⟨v, hv, hvd⟩ := hd H.verts.toFinset (by simpa using hH)
    refine ⟨v, by simpa using hv, ?_⟩
    calc (H.neighborSet v).ncard
        ≤ ((H.verts.toFinset.filter (G.Adj v) : Finset V) : Set V).ncard := by
          apply Set.ncard_le_ncard _ (Finset.finite_toSet _)
          intro w hw
          have hadj : H.Adj v w := hw
          simp [H.edge_vert hadj.symm, H.adj_sub hadj]
      _ = (H.verts.toFinset.filter (G.Adj v)).card := Set.ncard_coe_finset _
      _ ≤ d := hvd
  · intro h s hs
    obtain ⟨v, hv, hvd⟩ := h ((⊤ : G.Subgraph).induce (s : Set V)) (by simpa using hs)
    have hv' : v ∈ s := by simpa using hv
    refine ⟨v, hv', ?_⟩
    have hset : ((⊤ : G.Subgraph).induce (s : Set V)).neighborSet v = ↑(s.filter (G.Adj v)) := by
      ext w
      simp [SimpleGraph.Subgraph.mem_neighborSet, hv']
    rw [hset, Set.ncard_coe_finset] at hvd
    exact hvd

theorem intro_degenerate_colorable_proved {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hd : IsDegenerate G d) : G.Colorable (d + 1) := by
  obtain ⟨c, hc⟩ := Degeneracy.exists_coloring_on G d hd univ
  exact ⟨SimpleGraph.Coloring.mk c (fun {u w} h => hc u (mem_univ u) w (mem_univ w) h)⟩

end Cereceda
