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

theorem reduceList_nil {A : Type u} (a0 : A) :
    reduceList a0 ([] : List A) = [] := by
  sorry

theorem reduceList_cons_base {A : Type u} (a0 : A) (xs : List A) :
    reduceList a0 (a0 :: xs) = reduceList a0 xs := by
  sorry

theorem reduceList_cons_of_ne {A : Type u} (a0 : A) (x : A) (xs : List A) (h : x ≠ a0) :
    reduceList a0 (x :: xs) = x :: reduceList a0 xs := by
  sorry

theorem reduceList_idempotent {A : Type u} (a0 : A) (l : List A) :
    reduceList a0 (reduceList a0 l) = reduceList a0 l := by
  sorry

/-- Relation identifying lists after removing basepoint occurrences. -/
def JamesRel {A : Type u} (a0 : A) (l1 l2 : List A) : Prop :=
  reduceList a0 l1 = reduceList a0 l2

theorem jamesRel_refl {A : Type u} (a0 : A) (l : List A) :
    JamesRel a0 l l := by
  sorry

theorem jamesRel_symm {A : Type u} (a0 : A) {l1 l2 : List A} :
    JamesRel a0 l1 l2 → JamesRel a0 l2 l1 := by
  sorry

theorem jamesRel_trans {A : Type u} (a0 : A) {l1 l2 l3 : List A} :
    JamesRel a0 l1 l2 → JamesRel a0 l2 l3 → JamesRel a0 l1 l3 := by
  sorry

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

theorem jamesMul_base_left (X : SuspensionLoop.Pointed) (a : JamesConstruction X) :
    jamesMul X (jamesBase X) a = a := by
  sorry

theorem jamesMul_base_right (X : SuspensionLoop.Pointed) (a : JamesConstruction X) :
    jamesMul X a (jamesBase X) = a := by
  sorry

theorem jamesMul_assoc (X : SuspensionLoop.Pointed)
    (a b c : JamesConstruction X) :
    jamesMul X (jamesMul X a b) c = jamesMul X a (jamesMul X b c) := by
  sorry

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

theorem loopOfList_singleton (X : SuspensionLoop.Pointed) (x : X.carrier) :
    loopOfList X [x] = LoopSpace.comp (loopOfElem X x) (loopOfList X []) := by
  sorry

theorem loopOfList_append_nil (X : SuspensionLoop.Pointed) (l : List X.carrier) :
    loopOfList X (l ++ []) = loopOfList X l := by
  sorry

/-- Map from the James construction to the loop space of the suspension. -/
noncomputable def jamesToLoop (X : SuspensionLoop.Pointed) :
    JamesConstruction X →
      LoopSpace (Suspension X.carrier) (Suspension.north (X := X.carrier)) :=
  Quot.lift
    (fun l => loopOfList X (reduceList X.pt l))
    (by
      intro l1 l2 h
      simpa [JamesRel] using _root_.congrArg (fun t => loopOfList X t) h)

theorem jamesToLoop_mk (X : SuspensionLoop.Pointed) (l : List X.carrier) :
    jamesToLoop X (Quot.mk (JamesRel X.pt) l) = loopOfList X (reduceList X.pt l) := by
  sorry

theorem jamesToLoop_base_eq (X : SuspensionLoop.Pointed) :
    jamesToLoop X (jamesBase X) = loopOfList X [] := by
  sorry

theorem jamesToLoop_mul_eq (X : SuspensionLoop.Pointed) (a b : JamesConstruction X) :
    jamesToLoop X (jamesMul X a b) =
      LoopSpace.comp (jamesToLoop X a) (jamesToLoop X b) := by
  sorry

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
