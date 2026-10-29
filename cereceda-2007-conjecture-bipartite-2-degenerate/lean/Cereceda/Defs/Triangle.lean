/-
Cereceda/Defs/Triangle.lean — the instance of Remark 3.9 (`tri`, its lists and out-neighbours, its five moves `triMoves`) and the graph
of open problem 2 (`spacedGraph`), short v3.90 l. 550-563 and 755-759.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
-/
import Cereceda.Defs.Instance
import Cereceda.Defs.LowerBound

namespace Cereceda

open Finset

/-- Out-neighbours of the instance of Remark 3.9 (v3.90 l. 551-552): `s = 0`, `u_i = i`; `N⁺(u₁) = {s}`,
`N⁺(u₂) = {u₁}`, `N⁺(u₃) = {u₁, u₂}`. -/
def triOut : Fin 4 → Finset (Fin 4)
  | 1 => {0}
  | 2 => {1}
  | 3 => {1, 2}
  | _ => ∅

/-- Lists of the instance of Remark 3.9 (v3.90 l. 551-553): `L(s) = {0, 1}`, `L(u₁) = L(u₃) = {0,1,2,3}`,
`L(u₂) = {1,2,3}`. -/
def triL : Fin 4 → Finset (Fin 4)
  | 0 => {0, 1}
  | 2 => {1, 2, 3}
  | _ => {0, 1, 2, 3}

/-- The instance of Remark 3.9 (v3.90 l. 551-554): the sink `s = 0` with the list `{0, 1}`, `g = 0`, `x = 1`; vertices
`u₁, u₂, u₃ = 1, 2, 3`; instance order = index. -/
def tri : Instance (Fin 4) where
  sink := 0
  rank v := v.val
  rank_inj := fun a b h => Fin.ext h
  sink_first := fun v => Nat.zero_le _
  out := triOut
  out_before := by decide
  out_card := by decide
  sink_out := rfl
  L := triL
  L_card := by decide
  g := 0
  x := 1
  g_lt_x := by decide
  L_sink := rfl

/-- The five moves of Remark 3.9 (v3.90 l. 559-560): "recolour `u₁` to `3`, `s` to `0`, `u₃` to `0`, `u₂` to `2` and `u₁`
to `1`". -/
def triMoves : List (Fin 4 × Fin 4) := [(1, 3), (0, 0), (3, 0), (2, 2), (1, 1)]

/-- The graph of open problem 2 (v3.90 l. 755-758): the path `v_1 ⋯ v_n` and `p` vertices `a_0, …, a_{p-1}`, each `a_j`
joined to every `v_i` with `i ≡ j (mod p)` (`Sum.inl k` is `v_{k+1}`, so `a_j` is joined to `Sum.inl k` when
`(k + 1) % p = j`). The paper's `ℓ` is Lean's `n`; `p = 4` gives `Jgraph` (`J_ℓ` of Section 4.2). -/
abbrev spacedGraph (n p : ℕ) (hp : 0 < p) : SimpleGraph (Fin n ⊕ Fin p) :=
  pathApex n p (fun k => ⟨(k.val + 1) % p, Nat.mod_lt _ hp⟩)

end Cereceda
