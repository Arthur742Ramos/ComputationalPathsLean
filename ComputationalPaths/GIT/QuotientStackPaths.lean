import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Geometric invariant theory paths: quotient stacks

This module packages quotient-stack style action descent data with explicit
`Path.Step` witnesses, yielding canonical `RwEq` normalizations.
-/

namespace ComputationalPaths
namespace GIT
namespace QuotientStackPaths

open Path

universe u v

/-- Domain-specific rewrite tags for quotient-stack coherence moves. -/
inductive QuotientStackStep : Type
  | actionDescent
  | semistableTransport
  | atlasNormalization

/-- Quotient-stack data with computational-path witnesses for GIT descent. -/
structure QuotientStackPathData (Obj : Type u) (Group : Type v) where
  action : Group → Obj → Obj
  quotientMap : Obj → Obj
  semistable : Obj → Prop
  actionDescentPath :
    ∀ (g : Group) (x : Obj), Path (quotientMap (action g x)) (quotientMap x)
  actionDescentStep :
    ∀ (g : Group) (x : Obj),
      Path.Step
        (Path.trans (actionDescentPath g x) (Path.refl (quotientMap x)))
        (actionDescentPath g x)
  semistableTransportPath :
    ∀ (g : Group) (x : Obj), Path (semistable (action g x)) (semistable x)
  semistableTransportStep :
    ∀ (g : Group) (x : Obj),
      Path.Step
        (Path.trans
          (Path.refl (semistable (action g x)))
          (semistableTransportPath g x))
        (semistableTransportPath g x)
  atlasPath : ∀ x : Obj, Path (quotientMap x) (quotientMap x)
  atlasStep :
    ∀ x : Obj,
      Path.Step
        (Path.trans (atlasPath x) (Path.refl (quotientMap x)))
        (atlasPath x)

namespace QuotientStackPathData

variable {Obj : Type u} {Group : Type v} (Q : QuotientStackPathData Obj Group)

@[simp] theorem action_descent_rweq (g : Group) (x : Obj) :
    RwEq
      (Path.trans (Q.actionDescentPath g x) (Path.refl (Q.quotientMap x)))
      (Q.actionDescentPath g x) :=
  rweq_of_step (Q.actionDescentStep g x)

@[simp] theorem semistable_transport_rweq (g : Group) (x : Obj) :
    RwEq
      (Path.trans
        (Path.refl (Q.semistable (Q.action g x)))
        (Q.semistableTransportPath g x))
      (Q.semistableTransportPath g x) :=
  rweq_of_step (Q.semistableTransportStep g x)

@[simp] theorem atlas_rweq (x : Obj) :
    RwEq
      (Path.trans (Q.atlasPath x) (Path.refl (Q.quotientMap x)))
      (Q.atlasPath x) :=
  rweq_of_step (Q.atlasStep x)

/-- Compose two descent moves, corresponding to sequential group actions. -/
def actionDescentTwoStepPath (g h : Group) (x : Obj) :
    Path (Q.quotientMap (Q.action g (Q.action h x))) (Q.quotientMap x) :=
  Path.trans (Q.actionDescentPath g (Q.action h x)) (Q.actionDescentPath h x)

@[simp] theorem action_descent_two_step_rweq (g h : Group) (x : Obj) :
    RwEq
      (Path.trans (Q.actionDescentTwoStepPath g h x) (Path.refl (Q.quotientMap x)))
      (Q.actionDescentTwoStepPath g h x) :=
  rweq_cmpA_refl_right (Q.actionDescentTwoStepPath g h x)

@[simp] theorem action_descent_cancel_rweq (g : Group) (x : Obj) :
    RwEq
      (Path.trans (Path.symm (Q.actionDescentPath g x)) (Q.actionDescentPath g x))
      (Path.refl (Q.quotientMap x)) :=
  rweq_cmpA_inv_left (Q.actionDescentPath g x)

@[simp] theorem semistable_transport_cancel_rweq (g : Group) (x : Obj) :
    RwEq
      (Path.trans
        (Q.semistableTransportPath g x)
        (Path.symm (Q.semistableTransportPath g x)))
      (Path.refl (Q.semistable (Q.action g x))) :=
  rweq_cmpA_inv_right (Q.semistableTransportPath g x)

end QuotientStackPathData

/-- Trivial quotient-stack model with canonical Step witnesses. -/
def trivialQuotientStackPathData : QuotientStackPathData PUnit PUnit where
  action := fun _ _ => PUnit.unit
  quotientMap := fun _ => PUnit.unit
  semistable := fun _ => True
  actionDescentPath := fun _ _ => Path.refl PUnit.unit
  actionDescentStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  semistableTransportPath := fun _ _ => Path.refl True
  semistableTransportStep := fun _ _ => Path.Step.trans_refl_left (Path.refl True)
  atlasPath := fun _ => Path.refl PUnit.unit
  atlasStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end QuotientStackPaths
end GIT
end ComputationalPaths

