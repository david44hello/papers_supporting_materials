/-
scripts/route_check.lean — the route claims of AUDIT.md's "Route differences" section, checked by Lean.
Author: Dave Goel. Copyright (C) Dave Goel 2026--now.

For each check (claim, constant, expected), it walks every constant that the claim's type and proof mention,
transitively, and asks whether `constant` is among them. Any mismatch, or an unknown name, is an ERROR (exit 1).
Run (after `lake build`): LEAN_NUM_THREADS=1 nice -n 19 taskset -c 11 lake env lean scripts/route_check.lean
-/
import NagataHigman.Paper.Statements

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

-- Lemma 4.2 and Lemma 4.3 follow the paper's chain (a)-(e), not the identity ρ(s) = -Y_N Y_{N-1} Y_N;
-- step (d) is the paper's argument (D = ½ρ(J_{N-1}) from c_T(N-1)(c_T(N) - c_T(N-1)) = -2).
#eval routeChecks [
  (`NagataHigman.Paper.lem_4_2, `NagataHigman.Proofs.lem_4_2_d_nu, true),
  (`NagataHigman.Paper.lem_4_2, `NagataHigman.Proofs.lem_4_2_e_proved, true),
  (`NagataHigman.Paper.lem_4_2, `NagataHigman.Proofs.rho_swap_eq_neg_star, false),
  (`NagataHigman.Paper.lem_4_2, `NagataHigman.Proofs.lem_4_2_general, false),
  (`NagataHigman.Paper.lem_4_2_d, `NagataHigman.Proofs.rhoAlg_jucysMurphy_eq_two_smul_stepD, true),
  (`NagataHigman.Paper.lem_4_3, `NagataHigman.Proofs.lem_4_2_e_proved, true),
  (`NagataHigman.Paper.lem_4_3, `NagataHigman.Proofs.rho_swap_eq_neg_star, false),
  (`NagataHigman.Paper.lem_4_3, `NagataHigman.Proofs.lem_4_2_general, false),
  (`NagataHigman.Paper.thm_B, `NagataHigman.Proofs.rho_swap_eq_neg_star, false)]
-- Lemma 4.1 passes through the paper's steps: Q₊MQ₊ = 0 = Q₋MQ₋, then "M swaps the eigenspaces of Y_N", then Y_N M = -M Y_N.
#eval routeChecks [
  (`NagataHigman.Paper.lem_4_1, `NagataHigman.Proofs.trace_perp_commutant_iff_blocks, true),
  (`NagataHigman.Paper.lem_4_1, `NagataHigman.Proofs.blocks_iff_swaps_eigenspaces, true),
  (`NagataHigman.Paper.lem_4_1, `NagataHigman.Proofs.swaps_eigenspaces_iff_anticomm, true)]
-- Lemma 4.3 ends as in the paper: f vanishes off h(ν) by (T3), h(ν) is not an N-cycle type, f ∈ C_N; so f = 0.
#eval routeChecks [
  (`NagataHigman.Paper.lem_4_3, `NagataHigman.Proofs.coeff_nu_eq_zero_off_hooks, true),
  (`NagataHigman.Paper.lem_4_3, `NagataHigman.Proofs.nu_cycle_block_eq_zero, true),
  (`NagataHigman.Paper.thm_B, `NagataHigman.Proofs.nu_cycle_block_eq_zero, true)]
-- Proposition 2.1: step (5)'s sign fact is sgn π = sgn(τ̄) sgn(τ̄ ∘ π), not the sign of an N-cycle; step (7) uses (F7).
#eval routeChecks [
  (`NagataHigman.Paper.prop_2_1_step5, `NagataHigman.Proofs.Arcs.sign_of_isFullCycle, false),
  (`NagataHigman.Paper.prop_2_1_step7_box, `NagataHigman.Proofs.signTwist_of_mem_cycleSpan, true)]
-- Theorems A and B reach Proposition 2.1's forward half through the arcs of step (6) (the block lemma).
#eval routeChecks [
  (`NagataHigman.Paper.thm_A, `NagataHigman.Proofs.forward_block_lemma, true),
  (`NagataHigman.Paper.thm_B, `NagataHigman.Proofs.forward_block_lemma, true)]
-- Corollary 1.1: Theorem B over the algebraic closure, the cited Procesi–Formanek theorem there, base change back.
-- Negative controls: Theorems A and B do not use the cited Procesi–Formanek statement.
#eval routeChecks [
  (`NagataHigman.Paper.cor_1_1, `NagataHigman.Cited.procesi_formanek, true),
  (`NagataHigman.Paper.cor_1_1, `NagataHigman.Paper.thm_B, true),
  (`NagataHigman.Paper.cor_1_1, `NagataHigman.Proofs.MatInvDensity.isConjInvariant_map, true),
  (`NagataHigman.Paper.cor_1_1, `NagataHigman.Proofs.MatInvDescent.mem_adjoin_of_map_mem, true),
  (`NagataHigman.Paper.cor_1_1_functions, `NagataHigman.Paper.cor_1_1, true),
  (`NagataHigman.Paper.thm_A, `NagataHigman.Cited.procesi_formanek, false),
  (`NagataHigman.Paper.thm_B, `NagataHigman.Cited.procesi_formanek, false)]
-- The other routes named in AUDIT.md: the restriction fact from the Young basis (not branching + Burnside) in
-- Lemmas 3.1 and 4.1; the field step through Proposition 2.1; (F1) by polarization; (F3) by Fourier inversion;
-- (T3) with Γ² = d·id (no rescaling).
#eval routeChecks [
  (`NagataHigman.Paper.lem_3_1, `NagataHigman.Proofs.restriction_of_young, true),
  (`NagataHigman.Paper.lem_4_1, `NagataHigman.Proofs.restriction_of_young, true),
  (`NagataHigman.Paper.sec_4_1_field, `NagataHigman.Proofs.prop_2_1_general, true),
  (`NagataHigman.Paper.F1_symSum_mem, `NagataHigman.Proofs.polarization, true),
  (`NagataHigman.Paper.F3_orthogonal, `NagataHigman.Proofs.YoungSystem.coeffPairing_eq_sum, true),
  (`NagataHigman.Paper.Gamma_pm, `NagataHigman.Proofs.gamma_sq_scalar, true)]
-- Route items 6-10: Theorems A and B use "two N-cycles have the same sign" and never the first-return map of steps
-- (4)-(6); (F4) from the Young basis; step (7) I^⊥ ⊆ A by traces; Lemma 4.2(e) from the cited Wedderburn clause;
-- the step (6) formula with the paper's arcs compares τ with the cycle of its arcs, not the sum over θ.
#eval routeChecks [
  (`NagataHigman.Paper.thm_A, `NagataHigman.Proofs.Arcs.sign_of_isFullCycle, true),
  (`NagataHigman.Paper.thm_B, `NagataHigman.Proofs.Arcs.sign_of_isFullCycle, true),
  (`NagataHigman.Paper.prop_2_1, `NagataHigman.firstReturnFun, false),
  (`NagataHigman.Paper.thm_A, `NagataHigman.firstReturnFun, false),
  (`NagataHigman.Paper.thm_B, `NagataHigman.firstReturnFun, false),
  (`NagataHigman.Paper.F4_altIdeal, `NagataHigman.Proofs.YoungSystem.rhoAlg_altGen_ne_zero_iff, true),
  (`NagataHigman.Paper.prop_2_1_step7_perp, `NagataHigman.Proofs.YoungSystem.rhoAlg_eq_zero_of_pairing, true),
  (`NagataHigman.Paper.lem_4_2_e, `NagataHigman.Proofs.YoungSystem.rhoAlg_surjective, true),
  (`NagataHigman.Paper.rem_2_2_forward, `NagataHigman.Proofs.converse_block_lemma, false),
  (`NagataHigman.Paper.prop_2_1_step6_formula_arcs, `NagataHigman.Proofs.Arcs.coeff_fullCycle, true),
  (`NagataHigman.Paper.prop_2_1_step6_formula_arcs, `NagataHigman.Proofs.prop21_step6_bij, false),
  (`NagataHigman.Paper.prop_2_1_step6_formula_arcs, `NagataHigman.Proofs.prop21_step5_sum, false)]
