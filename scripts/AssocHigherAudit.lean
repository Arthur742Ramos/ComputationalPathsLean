import ComputationalPaths.Path.OmegaGroupoid.AssocHigherBridge
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.PalomarAssociativity

/-! Regression checks for the higher certificate, including the original
syntactically distinct pentagon and the actual computational-path bridge. -/

example {α : Type} (w x y z : FreeMagma α) :
    pentagonShort w x y z ≠ pentagonLong w x y z :=
  pentagon_routes_distinct w x y z

noncomputable example {α : Type} (w x y z : FreeMagma α) :
    AssocHigher (pentagonShort w x y z).toRwEq (pentagonLong w x y z).toRwEq :=
  AssocHigher.directedParallel _ _

noncomputable example {α : Type} {x y : FreeMagma α} (p q : AssocRwEq x y) :
    AssocHigher (.symm p) (.symm q) := AssocHigher.allParallel _ _

noncomputable example {α A : Type} {a : A} (label : α → Path a a)
    (w x y z : FreeMagma α) :
    RwEq (Path.trans (Path.trans (Path.trans (evalTree label w) (evalTree label x))
      (evalTree label y)) (evalTree label z))
      (Path.trans (evalTree label w) (Path.trans (evalTree label x)
        (Path.trans (evalTree label y) (evalTree label z)))) :=
  evalPentagonShort label w x y z

#print axioms CoherentPeak.fill
#print axioms AssocSeq.terminalCoherence
#print axioms AssocHigher.normalizationSquare
#print axioms AssocHigher.allParallel
#print axioms evalStep
#print axioms evalTrace

noncomputable example {α A : Type} {a : A} (label : α → Path a a)
    {x y : FreeMagma α} (p q : AssocRwEq x y) :
    OmegaGroupoid.Derivation₃ (eval₂ label p) (eval₂ label q) :=
  evalHigher label (AssocHigher.allParallel p q)

noncomputable example {α A : Type} {a : A} (label : α → Path a a)
    (w x y z : FreeMagma α) :
    OmegaGroupoid.Derivation₃ (eval₂ label (pentagonShort w x y z).toRwEq)
      (eval₂ label (pentagonLong w x y z).toRwEq) :=
  nativePentagon label w x y z

#print axioms nativePentagon
#print axioms nativeInterchange
#print axioms nativeAllParallel
#print axioms evalHigher

/- Audit the transitive definition/proof-body dependencies of the public
bridge, not just its axiom list. Imported but unused declarations do not count.
This deliberately inspects bodies, not every constructor of an imported type. -/
run_cmd do
  let env ← Lean.getEnv
  for root in #[``CoherentPeak.fill, ``AssocHigher.allParallel, ``nativeAllParallel,
      ``evalHigher, ``evalHigherRwEq] do
    for ax in ← Lean.collectAxioms root do
      unless #[`propext, `Quot.sound].contains ax do
        throwError "Unapproved axiom in {root}: {ax}"
  let mut pending := #[``evalHigher]
  let mut seen : Lean.NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n == ``OmegaGroupoid.MetaStep₃.rweq_transport ||
        n.toString.startsWith "ComputationalPaths.Path.OmegaGroupoid.contractibility" ||
        n == `sorryAx || n == `Lean.ofReduceBool then
      throwError "Forbidden higher-bridge dependency: {n}"
    if let some ci := env.find? n then
      if let some body := ci.value? (allowOpaque := true) then
        pending := pending ++ body.getUsedConstants
  for required in #[``OmegaGroupoid.MetaStep₃.pentagon,
      ``OmegaGroupoid.MetaStep₃.interchange, ``OmegaGroupoid.MetaStep₃.diamond_filler] do
    unless seen.contains required do
      throwError "Expected native generator missing from bridge: {required}"
  Lean.logInfo "Higher bridge dependency audit passed: named generators present; no arbitrary-parallel or proof-irrelevant transport filler."
