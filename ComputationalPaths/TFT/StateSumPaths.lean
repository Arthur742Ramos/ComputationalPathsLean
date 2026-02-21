import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.TFT.CobordismFunctorPaths

/-!
# Topological field theory paths: state sums

This module models state-sum assignments on cobordism categories and tracks
their gluing coherence via explicit `Path.Step` witnesses and `RwEq`.
-/

namespace ComputationalPaths
namespace TFT
namespace StateSumPaths

open Path
open CobordismFunctorPaths

universe u v w

/-- State-sum data over a cobordism category with path-level gluing laws. -/
structure StateSumModel (C : CobordismCategory.{u, v}) where
  amplitude : Type w
  add : amplitude → amplitude → amplitude
  zero : amplitude
  assign : {X Y : C.Obj} → C.Hom X Y → amplitude
  assign_id : (X : C.Obj) → Path (assign (C.id X)) zero
  assign_comp : {X Y Z : C.Obj} → (f : C.Hom X Y) → (g : C.Hom Y Z) →
    Path (assign (C.comp f g)) (add (assign f) (assign g))
  add_assoc : (a b c : amplitude) → Path (add (add a b) c) (add a (add b c))
  add_zero_left : (a : amplitude) → Path (add zero a) a
  add_zero_right : (a : amplitude) → Path (add a zero) a

namespace StateSumModel

variable {C : CobordismCategory.{u, v}}
variable (S : StateSumModel C)

/-- Step witness: right-unit normalization for identity amplitudes. -/
def assignId_step (X : C.Obj) :
    Path.Step
      (Path.trans (S.assign_id X) (Path.refl S.zero))
      (S.assign_id X) :=
  Path.Step.trans_refl_right (S.assign_id X)

noncomputable def assignId_rweq (X : C.Obj) :
    RwEq
      (Path.trans (S.assign_id X) (Path.refl S.zero))
      (S.assign_id X) :=
  rweq_of_step (S.assignId_step X)

/-- First leg of the gluing chain on amplitudes. -/
def gluingFirst {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (S.assign (C.comp (C.comp f g) h))
      (S.add (S.assign (C.comp f g)) (S.assign h)) :=
  S.assign_comp (C.comp f g) h

/-- Middle leg of the gluing chain on amplitudes. -/
def gluingMiddle {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (S.add (S.assign (C.comp f g)) (S.assign h))
      (S.add (S.add (S.assign f) (S.assign g)) (S.assign h)) :=
  Path.congrArg (fun t => S.add t (S.assign h)) (S.assign_comp f g)

/-- Final leg of the gluing chain on amplitudes. -/
def gluingLast {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (S.add (S.add (S.assign f) (S.assign g)) (S.assign h))
      (S.add (S.assign f) (S.add (S.assign g) (S.assign h))) :=
  S.add_assoc (S.assign f) (S.assign g) (S.assign h)

/-- Left-associated gluing coherence chain. -/
def gluingChainLeft {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (S.assign (C.comp (C.comp f g) h))
      (S.add (S.assign f) (S.add (S.assign g) (S.assign h))) :=
  Path.trans
    (Path.trans (S.gluingFirst f g h) (S.gluingMiddle f g h))
    (S.gluingLast f g h)

/-- Right-associated gluing coherence chain. -/
def gluingChainRight {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path
      (S.assign (C.comp (C.comp f g) h))
      (S.add (S.assign f) (S.add (S.assign g) (S.assign h))) :=
  Path.trans
    (S.gluingFirst f g h)
    (Path.trans (S.gluingMiddle f g h) (S.gluingLast f g h))

/-- Associativity of gluing as a primitive Step witness. -/
theorem gluing_assoc_step {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    Path.Step (S.gluingChainLeft f g h) (S.gluingChainRight f g h) := by
  simpa [gluingChainLeft, gluingChainRight] using
    (Path.Step.trans_assoc
      (S.gluingFirst f g h)
      (S.gluingMiddle f g h)
      (S.gluingLast f g h))

/-- Rewrite-equivalence form of gluing associativity. -/
noncomputable def gluing_assoc_rweq {W X Y Z : C.Obj}
    (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
    RwEq (S.gluingChainLeft f g h) (S.gluingChainRight f g h) :=
  rweq_of_step (S.gluing_assoc_step f g h)

/-- Step witness: right-unit normalization for left unit amplitudes. -/
def addLeftUnit_step (a : S.amplitude) :
    Path.Step
      (Path.trans (S.add_zero_left a) (Path.refl a))
      (S.add_zero_left a) :=
  Path.Step.trans_refl_right (S.add_zero_left a)

/-- Step witness: right-unit normalization for right unit amplitudes. -/
def addRightUnit_step (a : S.amplitude) :
    Path.Step
      (Path.trans (S.add_zero_right a) (Path.refl a))
      (S.add_zero_right a) :=
  Path.Step.trans_refl_right (S.add_zero_right a)

noncomputable def addLeftUnit_rweq (a : S.amplitude) :
    RwEq
      (Path.trans (S.add_zero_left a) (Path.refl a))
      (S.add_zero_left a) :=
  rweq_of_step (S.addLeftUnit_step a)

noncomputable def addRightUnit_rweq (a : S.amplitude) :
    RwEq
      (Path.trans (S.add_zero_right a) (Path.refl a))
      (S.add_zero_right a) :=
  rweq_of_step (S.addRightUnit_step a)

noncomputable def addLeftCancel_rweq (a : S.amplitude) :
    RwEq
      (Path.trans (Path.symm (S.add_zero_left a)) (S.add_zero_left a))
      (Path.refl a) :=
  rweq_cmpA_inv_left (S.add_zero_left a)

noncomputable def addRightCancel_rweq (a : S.amplitude) :
    RwEq
      (Path.trans (S.add_zero_right a) (Path.symm (S.add_zero_right a)))
      (Path.refl (S.add a S.zero)) :=
  rweq_cmpA_inv_right (S.add_zero_right a)

end StateSumModel

end StateSumPaths
end TFT
end ComputationalPaths
