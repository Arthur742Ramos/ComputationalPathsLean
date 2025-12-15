import Lean
import ComputationalPaths

open Lean
open Lean.Elab
open Lean.Elab.Command

namespace ComputationalPaths.Scripts

private def isComputationalPathsDecl (name : Name) : Bool :=
  (toString name).startsWith "ComputationalPaths"

syntax (name := listCpAxioms) "#list_cp_axioms" : command

@[command_elab listCpAxioms] def elabListCpAxioms : CommandElab := fun _stx => do
  let env ← getEnv
  let mut acc : Array Name := #[]
  for (name, info) in env.constants.toList do
    if isComputationalPathsDecl name then
      match info with
      | .axiomInfo _ => acc := acc.push name
      | _ => pure ()
  let sorted := acc.qsort (fun a b => toString a < toString b)
  logInfo m!"ComputationalPaths axioms (importing `ComputationalPaths`): {sorted.size}"
  for name in sorted do
    logInfo m!"- {name}"

#list_cp_axioms

end ComputationalPaths.Scripts
