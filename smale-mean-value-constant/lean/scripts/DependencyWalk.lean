/-
scripts/DependencyWalk.lean — which theorems does a theorem reach? Written by the team, so that a reader can repeat note N17 of
Smale/Paper/Statements.lean without trusting any stored list: it walks the type and the value of every constant reached.
Run from the project's root: lake env lean scripts/DependencyWalk.lean   It stops with an error if a line below does not hold.
-/
import Smale.Paper.Statements

open Lean Elab Command

/-- Every constant reachable from `root` through types, values, constructors and recursors. -/
def reached (env : Environment) (root : Name) : NameSet := Id.run do
  let mut stack := #[root]
  let mut seen : NameSet := {}
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | continue
    stack := stack ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then stack := stack ++ value.getUsedConstants
    match info with
    | .inductInfo i => stack := stack ++ i.ctors.toArray
    | .ctorInfo c => stack := stack.push c.induct
    | .recInfo r => stack := stack ++ r.all.toArray
    | _ => pure ()
  return seen

/-- Stop with an error unless `root` reaches each of `yes` and none of `no`. -/
def expect (root : Name) (yes no : List Name) : CoreM Unit := do
  let seen := reached (← getEnv) root
  for name in yes do
    unless seen.contains name do throwError "{root} does not reach {name}"
  for name in no do
    if seen.contains name then throwError "{root} reaches {name}"
  logInfo m!"{root}: {seen.size} constants; reaches {yes}; does not reach {no}"

-- N17: the main theorems use Proposition 4.2 and not Proposition 3.1, nor the Riemann map.
run_cmd liftCoreM do
  for root in [``Smale.thm_1_1_of_R, ``Smale.thm_5_1_of_R, ``Smale.cor_5_4_of_R] do
    expect root [``Smale.jatarNg_prop_4_2_proved] [``Smale.jatarNg_prop_3_1_proved, ``Complex.RiemannData]

-- The controls: rows that do use Proposition 3.1, so a walk that sees nothing cannot pass.
run_cmd liftCoreM do
  for root in [``Smale.rem_2_3_pair, ``Smale.rem_2_3_Kstar_le, ``Smale.thm_2_2_moreover] do
    expect root [``Smale.jatarNg_prop_3_1_proved, ``Complex.RiemannData] []
