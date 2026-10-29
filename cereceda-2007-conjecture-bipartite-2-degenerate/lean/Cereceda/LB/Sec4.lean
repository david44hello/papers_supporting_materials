/-
Cereceda/LB/Sec4.lean — assembly of the Section 4 statements about H_n and J_n, Remark 4.5 and Proposition 1.3
of the paper (short version).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

Connectivity of R_4 comes from Theorem 1.2 (thm_1_2 in Statements); here it enters as the hypothesis `h12` of exactly
thm_1_2's type (`Thm12`), so this file does not import Statements.
-/
import Cereceda.LB.LowerBounds
import Cereceda.LB.Planar
import Cereceda.LB.GirthJ
import Cereceda.LB.Facts

namespace Cereceda.Sec4Aux

open Finset

/-- The type of Theorem 1.2 (`thm_1_2` in Statements), used as a hypothesis. -/
def Thm12 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.IsBipartite → IsDegenerate G 2 →
      (recolGraph G 4).ediam ≤ ((2 * Fintype.card V * (Fintype.card V + 1) : ℕ) : ℕ∞)

theorem Hgraph_bipartite (n : ℕ) : (Hgraph n).IsBipartite :=
  FactsAux.bipartite_of_sides _ _ (FactsAux.Hgraph_sides n)

theorem Hgraph_degenerate (n : ℕ) : IsDegenerate (Hgraph n) 2 :=
  FactsAux.degenerate_of_order _ 2 _ (FactsAux.Hgraph_order n)

theorem Jgraph_bipartite (n : ℕ) : (Jgraph n).IsBipartite :=
  FactsAux.bipartite_of_sides _ _ (FactsAux.Jgraph_sides n)

theorem Jgraph_degenerate (n : ℕ) : IsDegenerate (Jgraph n) 2 :=
  FactsAux.degenerate_of_order _ 2 _ (FactsAux.Jgraph_order n)

/-- Theorem 1.2 makes `R_4(H_n)` of finite diameter. -/
theorem hfinH (h12 : Thm12) (n : ℕ) : (recolGraph (Hgraph n) 4).ediam ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h12 (Hgraph n) (Hgraph_bipartite n) (Hgraph_degenerate n))

/-- Theorem 1.2 makes `R_4(J_n)` of finite diameter. -/
theorem hfinJ (h12 : Thm12) (n : ℕ) : (recolGraph (Jgraph n) 4).ediam ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (h12 (Jgraph n) (Jgraph_bipartite n) (Jgraph_degenerate n))

end Cereceda.Sec4Aux

namespace Cereceda

open Finset Sec4Aux

/-- Section 4, short v3.90 l. 580-583: `H_n` (card, sides, straight-line drawing, order). -/
theorem sec4_Hgraph_proved (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (Fin n ⊕ Fin 2) = n + 2 ∧
      IsProperFn (Hgraph n) (sideH n) ∧ IsStraightLinePlanar (Hgraph n) ∧
      IsDegOrder (Hgraph n) 2 (finSumFinEquiv : Fin n ⊕ Fin 2 ≃ Fin (n + 2)) :=
  ⟨FactsAux.Hgraph_card n, FactsAux.Hgraph_sides n, PlanarAux.Hgraph_planar_proved n, FactsAux.Hgraph_order n⟩

/-- Section 4: `H_n` (`n ≥ 3`) is not `1`-degenerate. -/
theorem sec4_Hgraph_not_one_degenerate_proved (n : ℕ) (hn : 3 ≤ n) : ¬ IsDegenerate (Hgraph n) 1 :=
  FactsAux.Hgraph_not_one_degenerate n hn

/-- Section 4.2 (girth six), short v3.90 l. 672-679: `J_n` (card, order, sides, girth `6`). -/
theorem sec4_Jgraph_proved (n : ℕ) (hn : 5 ≤ n) :
    Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧
      IsDegOrder (Jgraph n) 2 (finSumFinEquiv : Fin n ⊕ Fin 4 ≃ Fin (n + 4)) ∧
      IsProperFn (Jgraph n) (sideJ n) ∧ (Jgraph n).egirth = 6 :=
  ⟨FactsAux.Jgraph_card n, FactsAux.Jgraph_order n, FactsAux.Jgraph_sides n, GirthAux.Jgraph_egirth_proved n hn⟩

/-- Section 4: `J_n` (`n ≥ 5`) is not `1`-degenerate. -/
theorem sec4_Jgraph_not_one_degenerate_proved (n : ℕ) (hn : 5 ≤ n) : ¬ IsDegenerate (Jgraph n) 1 :=
  FactsAux.Jgraph_not_one_degenerate n hn

set_option linter.unusedVariables false in
/-- A remark of an earlier proof route (not in short v3.90, whose Remark 4.5 is `rem_4_5_apex_split` in
Paper/Statements.lean): `H_n` is planar (v3.90 l. 582), triangle-free, and `R_4(H_n)` is connected, with Theorem 1.2
as the hypothesis `h12`.
(`hn` is part of the statement; the proof does not need it.) -/
theorem rem_4_5_proved (n : ℕ) (hn : 2 ≤ n) (h12 : Thm12) :
    IsStraightLinePlanar (Hgraph n) ∧ (Hgraph n).CliqueFree 3 ∧ (recolGraph (Hgraph n) 4).Connected := by
  have : Nonempty ((Hgraph n).Coloring (Fin 4)) := ⟨LBAux.sigmaPlusCol n 2 _⟩
  exact ⟨PlanarAux.Hgraph_planar_proved n, FactsAux.cliqueFree_three_of_bipartite _ (Hgraph_bipartite n),
    SimpleGraph.connected_of_ediam_ne_top (hfinH h12 n)⟩

/-- **Proposition 1.3 (prop:lb)** (v3.90 l. 84-89), with Theorem 1.2 as the hypothesis `h12`. -/
theorem prop_1_3_lforms_proved (h12 : Thm12) :
    (∀ n : ℕ, 5 ≤ n →
      (Hgraph n).IsBipartite ∧ IsStraightLinePlanar (Hgraph n) ∧
      IsDegenerate (Hgraph n) 2 ∧ ¬ IsDegenerate (Hgraph n) 1 ∧
      Fintype.card (Fin n ⊕ Fin 2) = n + 2 ∧
      ((((n + 2 : ℕ) : ℝ) - 7) ^ 2 / 8 ≤ ((recolGraph (Hgraph n) 4).diam : ℝ))) ∧
    (∀ n : ℕ, 29 ≤ n →
      (Jgraph n).IsBipartite ∧ IsDegenerate (Jgraph n) 2 ∧ ¬ IsDegenerate (Jgraph n) 1 ∧
      (Jgraph n).egirth = 6 ∧ Fintype.card (Fin n ⊕ Fin 4) = n + 4 ∧
      ((((n + 4 : ℕ) : ℝ) - 33) ^ 2 / 128 ≤ ((recolGraph (Jgraph n) 4).diam : ℝ))) := by
  refine ⟨fun n hn => ⟨Hgraph_bipartite n, PlanarAux.Hgraph_planar_proved n, Hgraph_degenerate n,
      FactsAux.Hgraph_not_one_degenerate n (by omega), FactsAux.Hgraph_card n,
      (prop_4_1_proved n hn (hfinH h12 n)).2⟩,
    fun n hn => ⟨Jgraph_bipartite n, Jgraph_degenerate n, FactsAux.Jgraph_not_one_degenerate n (by omega),
      GirthAux.Jgraph_egirth_proved n (by omega), FactsAux.Jgraph_card n,
      (prop_4_6_proved n hn (hfinJ h12 n)).2⟩⟩

end Cereceda
