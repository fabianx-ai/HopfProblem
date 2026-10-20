import Lib.AlgebraicTopology.SingularCochains.PositivePrimitives
noncomputable section

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if n.toString.endsWith "SingularCochains.dualHomotopyEquiv" then acc.push n else acc
  logInfo m!"found {names}"
  let some n := names[0]? | throwError "dualHomotopyEquiv not found"
  let some ci := env.find? n | throwError "no info"
  logInfo m!"levelParams {ci.levelParams}"
  let id := mkIdent n
  -- the old statement at u = 0, proved by the lifted constant
  elabCommand (← `(example (A : AddCommGrpCat.{0}) {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}
      (e : HomotopyEquiv K L) :
      HomotopyEquiv (AlgebraicTopology.SingularCochains.dualComplex A L)
        (AlgebraicTopology.SingularCochains.dualComplex A K) := $id A e))
  -- the lift is real: chains over ModuleCat.{1}
  elabCommand (← `(example (A : AddCommGrpCat.{0}) {K L : ChainComplex (ModuleCat.{1} ℤ) ℕ}
      (e : HomotopyEquiv K L) :
      HomotopyEquiv (AlgebraicTopology.SingularCochains.dualComplex A L)
        (AlgebraicTopology.SingularCochains.dualComplex A K) := $id A e))
  elabCommand (← `(set_option pp.universes true in #check @$id))
