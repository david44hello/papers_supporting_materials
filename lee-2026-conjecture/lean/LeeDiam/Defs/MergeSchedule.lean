/-
LeeDiam/Defs/MergeSchedule.lean — the merged order of the paper's proof of Lemma 4.11 (Junction, sec_chain.tex v1.50
l. 133): "perform the moves of the first phase of Q before K; then the moves of W, where K is performed together with
the move of W at which c_i first appears; then the second phase of Q".
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.
Copyright (C) Dave Goel 2026--now.

State `t` of the merged walk is `W_{mergeIndexW κ n t} ∪ Q_{mergeIndexQ κ μ n t}`: `Q`'s move `κ` (from its state `κ`
to its state `κ + 1`) is `K`; `n` is the number of moves of `W`; `μ` is the state of `W` reached by the move at which
`c_i` first appears. The same two functions are `jW`, `jV` of Sec4/Junction.lean (checked by `rfl` in
Sec4/Lem411Step.lean).
-/

namespace LeeDiam

/-- The state of `W` at step `t` of the merged walk: `W` waits during the first `κ` moves of `Q`, then makes its `n`
moves, then stays at its last state. -/
def mergeIndexW (κ n t : Nat) : Nat := if t ≤ κ then 0 else if t ≤ κ + n then t - κ else n

/-- The state of `Q` at step `t` of the merged walk: its moves `0, …, κ - 1` first; its move `κ` (= `K`) together with
the move of `W` into state `μ`; its remaining moves after the last move of `W`. -/
def mergeIndexQ (κ μ n t : Nat) : Nat :=
  if t ≤ κ then t else if t < κ + μ then κ else if t ≤ κ + n then κ + 1 else κ + 1 + (t - κ - n)

end LeeDiam
