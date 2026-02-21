import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Categorification.CategorifiedQuantumGroupPaths

/-!
# Categorification paths: 2-representations

This module records a lightweight 2-representation interface with explicit
computational paths for horizontal composition, whiskering, and mate
coherences. It also adds bridge data from categorified quantum groups to
2-representations, with `Path.Step` normalization witnesses.
-/

namespace ComputationalPaths
namespace Categorification
namespace TwoRepresentationPaths

open Path
open CategorifiedQuantumGroupPaths

universe u

/-- Domain-specific rewrite tags for 2-representation coherence moves. -/
inductive TwoRepStep : Type
  | identity
  | horizontal
  | vertical
  | mate
  | interchange

/-- Minimal computational-path interface for strict 2-representations. -/
structure TwoRepresentationPathData (Obj : Type u) where
  actObj : Obj → Obj
  actMor : {X Y : Obj} → Path X Y → Path (actObj X) (actObj Y)
  id2Cell :
    (X : Obj) →
      Path (actObj X) (actObj X)
  comp2Cell :
    {X Y Z : Obj} → (p : Path X Y) → (q : Path Y Z) →
      Path (Path.trans (actMor p) (actMor q))
        (actMor (Path.trans p q))
  whisker2Cell :
    {X Y : Obj} → (p : Path X Y) →
      Path (Path.trans (id2Cell X) (actMor p))
        (actMor p)
  mate2Cell :
    {X Y : Obj} → (p : Path X Y) →
      Path (Path.symm (actMor (Path.symm p)))
        (actMor p)

namespace TwoRepresentationPathData

variable {Obj : Type u}
variable (T : TwoRepresentationPathData Obj)

/-- Step witness: left-unit normalization for horizontal composition cells. -/
def comp_step {X Y Z : Obj} (p : Path X Y) (q : Path Y Z) :
    Path.Step
      (Path.trans
        (Path.refl (Path.trans (T.actMor p) (T.actMor q)))
        (T.comp2Cell p q))
      (T.comp2Cell p q) :=
  Path.Step.trans_refl_left (T.comp2Cell p q)

noncomputable def comp_rweq {X Y Z : Obj} (p : Path X Y) (q : Path Y Z) :
    RwEq
      (Path.trans
        (Path.refl (Path.trans (T.actMor p) (T.actMor q)))
        (T.comp2Cell p q))
      (T.comp2Cell p q) :=
  rweq_of_step (T.comp_step p q)

/-- Step witness: right-unit normalization for whiskering cells. -/
def whisker_step {X Y : Obj} (p : Path X Y) :
    Path.Step
      (Path.trans
        (T.whisker2Cell p)
        (Path.refl (T.actMor p)))
      (T.whisker2Cell p) :=
  Path.Step.trans_refl_right (T.whisker2Cell p)

noncomputable def whisker_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans
        (T.whisker2Cell p)
        (Path.refl (T.actMor p)))
      (T.whisker2Cell p) :=
  rweq_of_step (T.whisker_step p)

/-- Step witness: right-unit normalization for mate cells. -/
def mate_step {X Y : Obj} (p : Path X Y) :
    Path.Step
      (Path.trans
        (T.mate2Cell p)
        (Path.refl (T.actMor p)))
      (T.mate2Cell p) :=
  Path.Step.trans_refl_right (T.mate2Cell p)

noncomputable def mate_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans
        (T.mate2Cell p)
        (Path.refl (T.actMor p)))
      (T.mate2Cell p) :=
  rweq_of_step (T.mate_step p)

/-- Two-step mate composite used in 2-representation coherence checks. -/
def doubleMatePath {X Y : Obj} (p : Path X Y) :
    Path (Path.symm (Path.symm (T.actMor p)))
      (T.actMor p) :=
  Path.stepChain (Path.symm_symm (T.actMor p))

noncomputable def doubleMate_cancel_rweq {X Y : Obj} (p : Path X Y) :
    RwEq
      (Path.trans
        (Path.symm (T.doubleMatePath p))
        (T.doubleMatePath p))
      (Path.refl (T.actMor p)) :=
  rweq_cmpA_inv_left (T.doubleMatePath p)

end TwoRepresentationPathData

/-- Compatibility data between categorified quantum groups and a 2-representation. -/
structure QuantumTwoRepBridge (Obj : Type u)
    (Q : CatQuantumGroupPathData Obj)
    (T : TwoRepresentationPathData Obj) where
  eActionPath :
    ∀ X : Obj, Path (T.actObj (Q.e1 X)) (Q.e1 (T.actObj X))
  fActionPath :
    ∀ X : Obj, Path (T.actObj (Q.f1 X)) (Q.f1 (T.actObj X))
  crossingActionPath :
    ∀ X Y : Obj,
      Path
        (Path.trans
          (T.actMor (Q.crossingPath X Y))
          (Path.refl (T.actObj (Q.tensor (Q.f1 Y) (Q.e1 X)))))
        (T.actMor (Q.crossingPath X Y))

namespace QuantumTwoRepBridge

variable {Obj : Type u}
variable {Q : CatQuantumGroupPathData Obj}
variable {T : TwoRepresentationPathData Obj}
variable (B : QuantumTwoRepBridge Obj Q T)

/-- Step witness: right-unit normalization for crossing-action transport. -/
def crossingAction_step (X Y : Obj) :
    Path.Step
      (Path.trans
        (B.crossingActionPath X Y)
        (Path.refl (T.actMor (Q.crossingPath X Y))))
      (B.crossingActionPath X Y) :=
  Path.Step.trans_refl_right (B.crossingActionPath X Y)

noncomputable def crossingAction_rweq (X Y : Obj) :
    RwEq
      (Path.trans
        (B.crossingActionPath X Y)
        (Path.refl (T.actMor (Q.crossingPath X Y))))
      (B.crossingActionPath X Y) :=
  rweq_of_step (B.crossingAction_step X Y)

noncomputable def eAction_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (B.eActionPath X)) (B.eActionPath X))
      (Path.refl (Q.e1 (T.actObj X))) :=
  rweq_cmpA_inv_left (B.eActionPath X)

noncomputable def fAction_cancel_rweq (X : Obj) :
    RwEq
      (Path.trans (Path.symm (B.fActionPath X)) (B.fActionPath X))
      (Path.refl (Q.f1 (T.actObj X))) :=
  rweq_cmpA_inv_left (B.fActionPath X)

end QuantumTwoRepBridge

/-- Trivial 2-representation used as a base computational-path model. -/
def trivialTwoRepresentationPathData : TwoRepresentationPathData PUnit where
  actObj := fun _ => PUnit.unit
  actMor := fun {_ _} _ => Path.refl PUnit.unit
  id2Cell := fun _ => Path.refl PUnit.unit
  comp2Cell := fun _ _ => Path.refl (Path.refl PUnit.unit)
  whisker2Cell := fun _ => Path.refl (Path.refl PUnit.unit)
  mate2Cell := fun _ => Path.refl (Path.refl PUnit.unit)

/-- Trivial bridge between the trivial categorified quantum group and 2-representation. -/
def trivialQuantumTwoRepBridge :
    QuantumTwoRepBridge PUnit
      trivialCatQuantumGroupPathData
      trivialTwoRepresentationPathData where
  eActionPath := fun _ => Path.refl PUnit.unit
  fActionPath := fun _ => Path.refl PUnit.unit
  crossingActionPath := fun _ _ => Path.refl (Path.refl PUnit.unit)

end TwoRepresentationPaths
end Categorification
end ComputationalPaths
