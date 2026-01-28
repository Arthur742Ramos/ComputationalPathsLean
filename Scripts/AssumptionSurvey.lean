import Lean
import ComputationalPaths
import ComputationalPaths.Path.CompPath.SphereCompPath

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

namespace ComputationalPaths.Scripts

private partial def collectForallBinderInfos (e : Expr) (acc : Array BinderInfo := #[]) :
    Array BinderInfo :=
  match e with
  | .forallE _ _ body bi => collectForallBinderInfos body (acc.push bi)
  | _ => acc

syntax (name := cpAssumptionsFor) "#cp_assumptions_for" ident : command

@[command_elab cpAssumptionsFor] def elabCpAssumptionsFor : CommandElab := fun stx => do
  let root := stx[1].getId
  let env ← getEnv
  let some info := env.find? root
    | throwError m!"Unknown declaration: `{root}`"
  liftTermElabM do
    let binderInfos := collectForallBinderInfos info.type
    forallTelescope info.type fun params _body => do
      let mut propAssumptions : Array Expr := #[]
      let mut otherAssumptions : Array Expr := #[]
      for idx in [:params.size] do
        let p := params[idx]!
        let bi := binderInfos[idx]!
        if bi == BinderInfo.instImplicit then
          let ty ← whnf (← inferType p)
          if (← isProp ty) then
            propAssumptions := propAssumptions.push ty
          else
            otherAssumptions := otherAssumptions.push ty
      logInfo m!"Prop-valued typeclass assumptions for `{root}`: {propAssumptions.size}"
      for ty in propAssumptions do
        logInfo m!"- {(← ppExpr ty)}"
      logInfo m!"Non-Prop typeclass assumptions for `{root}`: {otherAssumptions.size}"
      for ty in otherAssumptions do
        logInfo m!"- {(← ppExpr ty)}"

end ComputationalPaths.Scripts

open ComputationalPaths.Scripts

#cp_assumptions_for ComputationalPaths.Path.circlePiOneEquivInt
#cp_assumptions_for ComputationalPaths.Path.torusPiOneEquivIntProd
#cp_assumptions_for ComputationalPaths.Path.seifertVanKampenEquiv
#cp_assumptions_for ComputationalPaths.Path.seifertVanKampenFullEquiv
#cp_assumptions_for ComputationalPaths.Path.seifertVanKampenEquiv_of_decodeAmalg_bijective
#cp_assumptions_for ComputationalPaths.Path.seifertVanKampenFullEquiv_of_decodeFullAmalg_bijective
#cp_assumptions_for ComputationalPaths.Path.hasPushoutSVKEncodeData_of_decodeAmalg_bijective
#cp_assumptions_for ComputationalPaths.Path.pushoutDecodeAmalg_surjective
#cp_assumptions_for ComputationalPaths.Path.pushoutEncodeAmalg_surjective
#cp_assumptions_for ComputationalPaths.Path.Sphere2.amalg_trivial_is_one
#cp_assumptions_for ComputationalPaths.Path.WedgeSVKInstances.wedgeDecodeEncodePrim
#cp_assumptions_for ComputationalPaths.Path.WedgeSVKInstances.wedgeEncodeDecodeQuotPrim
#cp_assumptions_for ComputationalPaths.Path.wedgeFundamentalGroupEquiv_of_decode_bijective
