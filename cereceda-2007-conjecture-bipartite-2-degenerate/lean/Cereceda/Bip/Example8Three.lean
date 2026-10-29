/-
Cereceda/Bip/Example8Three.lean — the instance `ex8` of open problem 1 (short v3.90 l. 743-752): a 13-move sequence from
α to β in which one vertex moves three times and every other vertex at most twice (not stated in v3.90).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Example8
import Cereceda.Bip.Example8

namespace Cereceda

open Finset

namespace Ex8Three

/-- A legal move of `ex8` from the colouring `c`, as a Boolean (sound by `legalF_sound`). -/
def legalF (c : Fin 8 → Fin 4) (m : Fin 8 × Fin 4) : Bool :=
  decide (m.2 ≠ c m.1) && decide (m.2 ∈ ex8.L m.1) &&
    (List.finRange 8).all (fun u => !Ex8Aux.adjB m.1 u || decide (c u ≠ m.2))

/-- A sequence of `ex8` from `c` to `c'`, as a Boolean (sound by `seqF_sound`). -/
def seqF : (Fin 8 → Fin 4) → List (Fin 8 × Fin 4) → (Fin 8 → Fin 4) → Bool
  | c, [], c' => decide (c' = c)
  | c, m :: ms, c' => legalF c m && seqF (Function.update c m.1 m.2) ms c'

theorem legalF_sound (c : Fin 8 → Fin 4) (m : Fin 8 × Fin 4) (h : legalF c m = true) :
    LegalMove ex8.graph ex8.L c m := by
  simp only [legalF, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, fun u hu => ?_⟩
  rcases h3 u with h | h
  · rw [(Ex8Aux.adj_iff _ _).1 hu] at h
    exact absurd h (by decide)
  · exact h

theorem seqF_sound : ∀ (ms : List (Fin 8 × Fin 4)) (c c' : Fin 8 → Fin 4), seqF c ms c' = true → ex8.IsSeq c ms c'
  | [], c, c', h => by
      simp only [seqF, decide_eq_true_eq] at h
      exact h
  | m :: ms, c, c', h => by
      simp only [seqF, Bool.and_eq_true] at h
      exact ⟨legalF_sound c m h.1, seqF_sound ms _ c' h.2⟩

/-- The 13-move sequence: the vertex `3` moves three times, every other vertex at most twice. -/
def seq13 : List (Fin 8 × Fin 4) :=
  [(2, 2), (3, 3), (1, 2), (0, 0), (1, 1), (3, 2), (4, 3), (2, 1), (6, 1), (7, 3), (3, 0), (4, 2), (7, 2)]

theorem seq13_ok : seqF Ex8Aux.alphaC seq13 Ex8Aux.betaC = true := by decide

end Ex8Three

theorem open_1_three_moves_suffice_proved :
    ∀ α β : Fin 8 → Fin 4, ex8.IsGreedy ex8.x α → ex8.IsGreedy ex8.g β →
      ∃ ms, ex8.IsSeq α ms β ∧ movesOf ms 3 = 3 ∧ ∀ v, v ≠ 3 → movesOf ms v ≤ 2 := by
  intro α β hα hβ
  have hα' : α = Ex8Aux.alphaC := (def_2_2_greedy_proved ex8 ex8.x).unique hα Ex8Aux.alpha_greedy
  have hβ' : β = Ex8Aux.betaC := (def_2_2_greedy_proved ex8 ex8.g).unique hβ Ex8Aux.beta_greedy
  subst hα' hβ'
  exact ⟨Ex8Three.seq13, Ex8Three.seqF_sound _ _ _ Ex8Three.seq13_ok, by decide, by decide⟩

end Cereceda
