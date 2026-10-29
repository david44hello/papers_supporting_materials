/-
Cereceda/Bip/MainV40.lean — Section 3 of short v3.90: Theorem 3.1 along the paper's proof (the greedy `μ` of
Definition 3.7, Proposition 3.8 and Lemma 3.4; l. 449-450 and 545-547), from the case g != 0 (a hypothesis:
`sec3_caseA_counts`).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Bip.MuV40
import Cereceda.Bip.Counts

namespace Cereceda

open Bip in
/-- **Theorem 3.1** (thm:BIPinst, v3.90 l. 396-399) along the paper's proof (l. 545-547): the greedy `μ` (Proposition 3.8) satisfies
the hypotheses of Lemma 3.4. `hA` = the type of `sec3_caseA_counts`. -/
theorem thm_3_1_of_v40
    (hA : ∀ {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (_hg : 0 < I.g)
      (α β : W → Fin 4) (_hα : I.IsGreedy I.x α) (_hβ : I.IsGreedy I.g β),
      ∃ ms, I.IsSeq α ms β ∧ movesOf ms I.sink = 1 ∧ ∀ v, v ≠ I.sink → movesOf ms v ≤ 2)
    {W : Type} [Fintype W] [DecidableEq W] (I : Instance W) (hnr : I.NoRoots)
    (hbip : I.graph.IsBipartite) (α β : W → Fin 4) (hα : I.IsGreedy I.x α) (hβ : I.IsGreedy I.g β) :
    ∃ ms, I.IsSeq α ms β ∧ movesOf ms I.sink = 1 ∧ (∀ v, v ≠ I.sink → movesOf ms v ≤ 2) ∧
      ms.length ≤ 2 * Fintype.card W - 1 := by
  by_cases hg0 : I.g = 0
  · obtain ⟨⟨μ, hμ, _⟩, _⟩ := prop_3_8_v40_proved I hnr hbip hg0 α β hα hβ
    obtain ⟨hμp, hμL, hμab, hμs⟩ := thm_3_1_mu_v40_proved I hnr hbip hg0 α β hα hβ μ hμ
    obtain ⟨ord1, h1, hs1⟩ := sorted_all (κ := μ) (fun a b => b ≤ a)
      (fun _ _ _ hab hbc => le_trans hbc hab) (fun a b => le_total b a)
    obtain ⟨ord2, h2, hs2⟩ := sorted_all (κ := μ) (fun a b => a ≤ b)
      (fun _ _ _ hab hbc => le_trans hab hbc) (fun a b => le_total a b)
    obtain ⟨hseq, hle, hsink⟩ := lem_3_4_proved I α β μ hα hβ hμp hμL (fun v => (hμab v).1)
      (fun v => (hμab v).2) hμs ord1 ord2 h1 h2 hs1 hs2
    exact ⟨_, hseq, hsink, fun v _ => hle v, length_le_of_counts I _ hsink (fun v _ => hle v)⟩
  · obtain ⟨ms, hseq, hsink, hle⟩ := hA I (lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hg0)) α β hα hβ
    exact ⟨ms, hseq, hsink, hle, length_le_of_counts I ms hsink hle⟩

end Cereceda
