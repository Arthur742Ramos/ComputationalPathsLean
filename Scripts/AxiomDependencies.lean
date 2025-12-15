import Lean
import ComputationalPaths.Path.HIT.CircleStep

open Lean
open Lean.Elab
open Lean.Elab.Command

namespace ComputationalPaths.Scripts

private def isComputationalPathsDecl (name : Name) : Bool :=
  (toString name).startsWith "ComputationalPaths"

private partial def collectConsts (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name :=
  match e with
  | .bvar _ => acc
  | .fvar _ => acc
  | .mvar _ => acc
  | .sort _ => acc
  | .const name _ => acc.insert name
  | .app f a => collectConsts a (collectConsts f acc)
  | .lam _ t b _ => collectConsts b (collectConsts t acc)
  | .forallE _ t b _ => collectConsts b (collectConsts t acc)
  | .letE _ t v b _ => collectConsts b (collectConsts v (collectConsts t acc))
  | .lit _ => acc
  | .mdata _ b => collectConsts b acc
  | .proj _ _ b => collectConsts b acc

private def collectConstInfoConsts (info : ConstantInfo) : Std.HashSet Name :=
  let acc := collectConsts info.type {}
  match info with
  | .axiomInfo _ => acc
  | .quotInfo _ => acc
  | .inductInfo _ => acc
  | .ctorInfo _ => acc
  | .recInfo _ => acc
  | .defnInfo v => collectConsts v.value acc
  | .thmInfo v => collectConsts v.value acc
  | .opaqueInfo v => collectConsts v.value acc

private partial def collectCpAxiomDeps
    (env : Environment)
    (root : Name)
    (visited : Std.HashSet Name := {})
    (axioms : Std.HashSet Name := {}) : Std.HashSet Name :=
  if visited.contains root then
    axioms
  else
    let visited := visited.insert root
    if !isComputationalPathsDecl root then
      axioms
    else
      match env.find? root with
      | none => axioms
      | some info =>
          match info with
          | .axiomInfo _ =>
              axioms.insert root
          | _ =>
              let refs := collectConstInfoConsts info
              refs.fold (init := axioms) fun acc dep =>
                collectCpAxiomDeps env dep visited acc

syntax (name := cpAxiomsFor) "#cp_axioms_for" ident : command

@[command_elab cpAxiomsFor] def elabCpAxiomsFor : CommandElab := fun stx => do
  let root := stx[1].getId
  let env ← getEnv
  let deps := collectCpAxiomDeps env root
  let sorted := deps.toArray.qsort (fun a b => toString a < toString b)
  logInfo m!"ComputationalPaths axioms used by `{root}`: {sorted.size}"
  for name in sorted do
    logInfo m!"- {name}"

end ComputationalPaths.Scripts

open ComputationalPaths.Scripts

#cp_axioms_for ComputationalPaths.Path.circlePiOneEquivInt
