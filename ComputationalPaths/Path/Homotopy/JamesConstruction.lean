/-
# James Construction and Suspension Loops

This module defines a reduced free-monoid on a pointed type (the James
construction) and constructs the canonical map to the loop space of the
suspension.

## Key Results

- `JamesConstruction`: quotient of lists by basepoint reduction
- `jamesMul`: concatenation on the quotient
- `jamesToLoop`: map to loop space of the suspension
- `jamesToLoop_base`, `jamesToLoop_mul`: compatibility with basepoint and
  concatenation

## References

- I. M. James, "Reduced product spaces", Annals of Mathematics (1955)
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace JamesConstruction

open SuspensionLoop

universe u

/-! ## Reduced lists -/

/-- Remove all occurrences of the basepoint from a list. -/
noncomputable def reduceList {A : Type u} (a0 : A) : List A → List A
  | [] => []
  | x :: xs => by
      classical
      by_cases h : x = a0
      · exact reduceList a0 xs
      · exact x :: reduceList a0 xs

theorem reduceList_append {A : Type u} (a0 : A) :
    ∀ l1 l2, reduceList a0 (l1 ++ l2) = reduceList a0 l1 ++ reduceList a0 l2 := by
  intro l1 l2
  induction l1 with
  | nil =>
      rfl
  | cons x xs ih =>
      classical
      by_cases h : x = a0
      · simp [reduceList, h, ih]
      · simp [reduceList, h, ih]





/-- Relation identifying lists after removing basepoint occurrences. -/
def JamesRel {A : Type u} (a0 : A) (l1 l2 : List A) : Prop :=
  reduceList a0 l1 = reduceList a0 l2




/-! ## James construction -/

/-- The James construction on a pointed type. -/
def JamesConstruction (X : SuspensionLoop.Pointed) : Type u :=
  Quot (JamesRel X.pt)

/-- Basepoint in the James construction (empty list). -/
def jamesBase (X : SuspensionLoop.Pointed) : JamesConstruction X :=
  Quot.mk _ []

/-- Concatenation on the James construction. -/
noncomputable def jamesMul (X : SuspensionLoop.Pointed) :
    JamesConstruction X → JamesConstruction X → JamesConstruction X :=
  Quot.lift
    (fun l1 =>
      Quot.lift
        (fun l2 => Quot.mk _ (l1 ++ l2))
        (by
          intro l2 l2' h2
          apply Quot.sound
          simp [JamesRel] at h2
          simp [JamesRel]
          simpa [reduceList_append] using
            _root_.congrArg (fun t => reduceList X.pt l1 ++ t) h2))
    (by
      intro l1 l1' h1
      apply funext
      intro q2
      refine Quot.inductionOn q2 ?_
      intro l2
      apply Quot.sound
      simp [JamesRel] at h1
      simp [JamesRel]
      simpa [reduceList_append] using
        _root_.congrArg (fun t => t ++ reduceList X.pt l2) h1)




/-- The James construction as a pointed type. -/
def jamesPointed (X : SuspensionLoop.Pointed) : SuspensionLoop.Pointed where
  carrier := JamesConstruction X
  pt := jamesBase X

/-! ## Loops of the suspension -/

variable {X : SuspensionLoop.Pointed}

/-- The basic loop in the suspension associated to a point. -/
def loopOfElem (X : SuspensionLoop.Pointed) (x : X.carrier) :
    LoopSpace (Suspension X.carrier) (Suspension.north (X := X.carrier)) :=
  Path.trans
    (Suspension.merid (X := X.carrier) x)
    (Path.symm (Suspension.merid (X := X.carrier) X.pt))

/-- Fold a list into the loop space of the suspension. -/
def loopOfList (X : SuspensionLoop.Pointed) :
    List X.carrier →
      LoopSpace (Suspension X.carrier) (Suspension.north (X := X.carrier))
  | [] => Path.refl (Suspension.north (X := X.carrier))
  | x :: xs => LoopSpace.comp (loopOfElem X x) (loopOfList X xs)

theorem loopOfList_append (X : SuspensionLoop.Pointed) :
    ∀ l1 l2, loopOfList X (l1 ++ l2) =
      LoopSpace.comp (loopOfList X l1) (loopOfList X l2) := by
  intro l1 l2
  induction l1 with
  | nil =>
      simp [loopOfList, LoopSpace.comp]
  | cons x xs ih =>
      simp [loopOfList, ih, LoopSpace.comp]



/-- Map from the James construction to the loop space of the suspension. -/
noncomputable def jamesToLoop (X : SuspensionLoop.Pointed) :
    JamesConstruction X →
      LoopSpace (Suspension X.carrier) (Suspension.north (X := X.carrier)) :=
  Quot.lift
    (fun l => loopOfList X (reduceList X.pt l))
    (by
      intro l1 l2 h
      simpa [JamesRel] using _root_.congrArg (fun t => loopOfList X t) h)




/-- Basepoint is sent to the reflexivity loop. -/
noncomputable def jamesToLoop_base (X : SuspensionLoop.Pointed) :
    Path
      (jamesToLoop X (jamesBase X))
      (Path.refl (Suspension.north (X := X.carrier))) := by
  apply Path.stepChain
  simp [jamesToLoop, jamesBase, loopOfList, reduceList]

/-- Concatenation in the James construction maps to loop composition. -/
noncomputable def jamesToLoop_mul (X : SuspensionLoop.Pointed) (a b : JamesConstruction X) :
    Path
      (jamesToLoop X (jamesMul X a b))
      (LoopSpace.comp (jamesToLoop X a) (jamesToLoop X b)) := by
  apply Path.stepChain
  refine Quot.inductionOn a ?_
  intro l1
  refine Quot.inductionOn b ?_
  intro l2
  simp [jamesMul, jamesToLoop, loopOfList_append, reduceList_append, LoopSpace.comp]

/-! ## Summary -/

end JamesConstruction
end Homotopy
end Path
end ComputationalPaths
