/-
Cereceda/Setting/CaseAPaperCounts.lean — the case g != 0 of Theorem 3.1 (v3.90 l. 404-405) along the paper's proof of Lemma 2.3.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

`sec3_caseA_counts_paper_proved`: the statement of the row `sec3_caseA_counts` (Paper/Statements.lean), with the row's
inline proof (heights on `T`, `|E(v)| ≤ 4`, the sequence of Lemma 2.4; Setting/CaseAPaper.lean), for the proof modules
(Setting/SweepSteps.lean). `lem_2_3_proved` (moved from Setting/CaseA.lean) now follows from it.
-/
import Cereceda.Defs.Instance
import Cereceda.Setting.CaseA
import Cereceda.Setting.CaseAPaper

namespace Cereceda

open Finset

/-- Section 3, v3.90 l. 404-405, along the paper's proof of Lemma 2.3: the sink moves exactly once, every other
vertex at most twice. Same statement and proof as the row `sec3_caseA_counts`. -/
theorem sec3_caseA_counts_paper_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ movesOf ms I.sink = 1 ∧ ∀ v, v ≠ I.sink → movesOf ms v ≤ 2 := by
  obtain ⟨hA, hB, hhA, hhB, hs⟩ := lem_2_3_heights_proved I hg α β hα hβ
  obtain ⟨ms, hseq, hmv, hout, hsink, -⟩ := lem_2_3_paper_route_proved I hg α β hα hβ hA hB hhA hhB hs
  refine ⟨ms, hseq, hsink, fun v _ => ?_⟩
  by_cases hv : (I.fGraph α).Reachable I.sink v
  · have h2 := hmv v hv
    have h4 : |hB v - hA v| ≤ 4 := (lem_2_3_E_bound_proved I hg α β hα hβ hA hB hhA hhB hs v hv).2
    have h4' : (hB v - hA v).natAbs ≤ 4 := by
      rw [Int.abs_eq_natAbs] at h4
      exact_mod_cast h4
    omega
  · rw [hout v hv]
    omega

/-- Lemma 2.3, first part (the row `lem_2_3`): at most `2m` moves, from `sec3_caseA_counts_paper_proved`. -/
theorem lem_2_3_proved {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hg : 0 < I.g)
    (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ ms.length ≤ 2 * Fintype.card W := by
  obtain ⟨ms, hseq, hsink, hrest⟩ := sec3_caseA_counts_paper_proved I hg α β hα hβ
  refine ⟨ms, hseq, ?_⟩
  rw [CaseA.length_eq_sum_movesOf]
  calc ∑ v, movesOf ms v ≤ ∑ _v : W, 2 := Finset.sum_le_sum fun v _ => by
          rcases eq_or_ne v I.sink with rfl | hv
          · omega
          · exact hrest v hv
    _ = 2 * Fintype.card W := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

end Cereceda
