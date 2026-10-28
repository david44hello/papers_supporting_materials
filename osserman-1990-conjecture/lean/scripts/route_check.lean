/-
scripts/route_check.lean — the route claims of AUDIT.md's "Not formalized, and route differences" section, checked by
Lean (project 013).
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

For each check (claim, constant, expected), it walks every constant that the claim's type and proof mention,
transitively, and asks whether `constant` is among them. Any mismatch, or an unknown name, is an ERROR (exit 1).
Run (after `lake build`): LEAN_NUM_THREADS=1 nice -n 19 lake env lean scripts/route_check.lean (through the gate).
-/
import Osserman.Paper.Statements

open Lean Elab Command

/-- Every constant reachable from `root` through types and values. -/
def routeClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    let c := stack.head!
    stack := stack.tail!
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      let deps := ci.type.getUsedConstants ++
        ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
      for d in deps do stack := d :: stack
  return visited

/-- Check `(claim, constant, expected-used)` triples; log one line each, an error on any mismatch. -/
def routeChecks (checks : List (Name × Name × Bool)) : CommandElabM Unit := do
  let env ← getEnv
  for (claim, cst, expected) in checks do
    unless env.contains claim do logError m!"UNKNOWN claim {claim}"
    unless env.contains cst do logError m!"UNKNOWN constant {cst}"
    let used := (routeClosure env claim).contains cst
    let word := if used then "USES" else "does NOT use"
    if used == expected then logInfo m!"ROUTE OK: {claim} {word} {cst}"
    else logError m!"ROUTE MISMATCH: {claim} {word} {cst} (expected the opposite)"

-- Checks are added as the proofs land (e.g. thm_C uses Osserman.Cited.isoparametric_quartic_R32).
#eval routeChecks [
  -- AUDIT.md route note 4: Lemma 4.1 gets H(a)² = I and "onto" from the injectivity of a ↦ H(a)x.
  (`Osserman.Paper.lem_4_1_sq, `Osserman.Proofs.Threshold.columnMap_injective, true),
  (`Osserman.Paper.lem_4_1_onto, `Osserman.Proofs.Threshold.columnMap_injective, true),
  (`Osserman.Paper.lem_4_1_c, `Osserman.Proofs.Threshold.threshold_sq, true),
  (`Osserman.Paper.lem_4_1_image_open, `Osserman.Proofs.Threshold.threshold_onto, true),
  -- Trust note: (eq:plus)/(eq:minus) rest on the cited (A); the constants ε, m are proved without it.
  (`Osserman.Paper.sec3_plus_or_minus, `Osserman.Cited.isoparametric_quartic_R32, true),
  (`Osserman.Paper.sec3_eps_m, `Osserman.Cited.isoparametric_quartic_R32, false)]
