/-
Cereceda/Defs/Example8.lean — the instance on 8 vertices of open problem 1 (short v3.90 l. 743-752: "two moves per
vertex are not always enough"; the paper cites [G, Remark 34.9] for this).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

TRUST SURFACE (v3.90 l. 744-751). Vertices `s, u_1, …, u_7` = `Fin 8` (`s` = `0`, `u_i` = `i`), instance order =
index, sink `s` with the list `{0,1}` and `x = 1`. Out-neighbours and lists: `u_1, u_2`: `{s}`, `{0,1,2}`;
`u_3`: `{u_1}`, `{0,2,3}`; `u_4`: `{u_2, u_3}`, `{0,1,2,3}`; `u_5`: `{u_4}`, `{0,1,2}`; `u_6`: `{u_4}`, `{1,2,3}`;
`u_7`: `{u_3, u_6}`, `{0,1,2,3}`.
-/
import Cereceda.Defs.Instance

namespace Cereceda

open Finset

/-- Out-neighbours of the example instance. -/
def ex8Out : Fin 8 → Finset (Fin 8)
  | 1 => {0}
  | 2 => {0}
  | 3 => {1}
  | 4 => {2, 3}
  | 5 => {4}
  | 6 => {4}
  | 7 => {3, 6}
  | _ => ∅

/-- Lists of the example instance. -/
def ex8L : Fin 8 → Finset (Fin 4)
  | 0 => {0, 1}
  | 1 => {0, 1, 2}
  | 2 => {0, 1, 2}
  | 3 => {0, 2, 3}
  | 5 => {0, 1, 2}
  | 6 => {1, 2, 3}
  | _ => {0, 1, 2, 3}

/-- The example instance (`g = 0`, `x = 1`). -/
def ex8 : Instance (Fin 8) where
  sink := 0
  rank v := v.val
  rank_inj := fun a b h => Fin.ext h
  sink_first := fun v => Nat.zero_le _
  out := ex8Out
  out_before := by decide
  out_card := by decide
  sink_out := rfl
  L := ex8L
  L_card := by decide
  g := 0
  x := 1
  g_lt_x := by decide
  L_sink := rfl

end Cereceda
