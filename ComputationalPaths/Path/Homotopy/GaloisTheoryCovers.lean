/-
# Galois Theory of Covering Spaces

This module records a lightweight interface for the Galois theory of covering
spaces in the computational paths setting.  We expose the etale fundamental
group, monodromy on fibers, Grothendieck-style correspondences with groupoid
actions, and the deck-transformation viewpoint on Galois groups.

## Key Results

- `EtalePiOne`: the etale pi1 modeled as the loop quotient.
- `monodromy`: the canonical pi1-action on covering fibers.
- `FiberFunctorObj`: a fiber together with its monodromy action.
- `grothendieckGaloisEquiv`: coverings correspond to groupoid actions.
- `GaloisGroup`: deck transformations as the Galois group of a covering.

## References

- Grothendieck, "SGA 1"
- Brown, "Topology and Groupoids"
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.GroupoidCovering
import ComputationalPaths.Path.Homotopy.CoveringFibrationAlgebra
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.GrothendieckConstruction
import ComputationalPaths.Path.Homotopy.UniversalCover
import ComputationalPaths.Path.Algebra.GroupActionOps

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace GaloisTheoryCovers

open Algebra
open CoveringSpace

universe u v

variable {A : Type u}

/-! ## Etale pi1 and monodromy -/

/-- The etale fundamental group, modeled as the loop quotient. -/
abbrev EtalePiOne (A : Type u) (a : A) : Type u :=
  PiOne A a

/-- Monodromy action of etale pi1 on a covering fiber. -/
noncomputable def monodromy (C : CoveringSpace.Covering A) (a : A) :
    EtalePiOne A a → C.fiber a → C.fiber a :=
  CoveringSpace.fiberAction (P := C.fiber) (a := a)

/-- Monodromy of the identity loop is the identity on the fiber. -/
@[simp] theorem monodromy_id {C : CoveringSpace.Covering A} {a : A} (x : C.fiber a) :
    monodromy (A := A) C a (PiOne.id (A := A) (a := a)) x = x := by
  simpa [monodromy, PiOne.id] using
    (CoveringSpace.fiberAction_id (P := C.fiber) (a := a) (x := x))

/-- Monodromy respects multiplication in etale pi1. -/
@[simp] theorem monodromy_mul {C : CoveringSpace.Covering A} {a : A}
    (g h : EtalePiOne A a) (x : C.fiber a) :
    monodromy (A := A) C a g (monodromy (A := A) C a h x) =
      monodromy (A := A) C a (PiOne.mul g h) x := by
  simp [monodromy, PiOne.mul]

/-- Monodromy packaged as a strict group action. -/
noncomputable def monodromyAction (C : CoveringSpace.Covering A) (a : A) :
    GroupAction (EtalePiOne A a)
      (CoveringFibrationAlgebra.loopGroupStructure A a) (C.fiber a) :=
  CoveringFibrationAlgebra.fiberActionGroupAction (P := C.fiber) a

/-! ## Fiber functors -/

/-- A fiber equipped with its monodromy action. -/
structure FiberFunctorObj (A : Type u) (a : A) where
  /-- Underlying carrier of the fiber. -/
  carrier : Type u
  /-- Monodromy action of etale pi1. -/
  action : GroupAction (EtalePiOne A a)
    (CoveringFibrationAlgebra.loopGroupStructure A a) carrier

/-- The fiber functor applied to a covering. -/
noncomputable def fiberFunctorObj (C : CoveringSpace.Covering A) (a : A) :
    FiberFunctorObj A a :=
  ⟨C.fiber a, monodromyAction (A := A) C a⟩

/-- The underlying fiber of the fiber functor. -/
abbrev fiberFunctor (a : A) (C : CoveringSpace.Covering A) : Type u :=
  (fiberFunctorObj (A := A) C a).carrier

/-! ## Grothendieck Galois correspondence -/

/-- Grothendieck-style Galois correspondence: coverings vs. groupoid actions. -/
def grothendieckGaloisEquiv (A : Type u) :
    SimpleEquiv (CoveringSpace.Covering A) (CoveringSpace.GroupoidAction A) :=
  CoveringSpace.coveringGroupoidActionEquiv A

/-! ## Etale and Galois coverings -/

/-- An etale covering: a covering with abstract finiteness of fibers. -/
structure EtaleCovering (A : Type u) : Type (u + 1) where
  /-- Underlying covering. -/
  covering : CoveringSpace.Covering A
  /-- Finiteness of fibers (abstract placeholder). -/
  finiteFiber : (a : A) → True

/-- The fiber of an etale covering. -/
abbrev EtaleCovering.fiber (E : EtaleCovering A) (a : A) : Type u :=
  E.covering.fiber a

/-- Monodromy for an etale covering. -/
noncomputable def etaleMonodromy (E : EtaleCovering A) (a : A) :
    EtalePiOne A a → E.fiber a → E.fiber a :=
  monodromy (A := A) E.covering a

/-- A Galois covering: a covering equipped with abstract normality/connectedness. -/
structure GaloisCovering (A : Type u) : Type (u + 1) where
  /-- Underlying covering. -/
  covering : CoveringSpace.Covering A
  /-- Connectedness of the cover (abstract placeholder). -/
  isConnected : True
  /-- Normality of the cover (abstract placeholder). -/
  isNormal : True

/-- Deck transformations as the Galois group of a covering. -/
abbrev GaloisGroup (C : CoveringSpace.Covering A) : Type u :=
  CoveringSpace.DeckTransformation C.fiber

/-- The Galois group of a Galois covering. -/
abbrev galoisGroup (C : GaloisCovering A) : Type u :=
  GaloisGroup (A := A) C.covering

/-- Identity element in the Galois group. -/
def galoisId (C : CoveringSpace.Covering A) : GaloisGroup (A := A) C :=
  CoveringSpace.DeckTransformation.id

/-- Composition in the Galois group. -/
def galoisComp (C : CoveringSpace.Covering A) :
    GaloisGroup (A := A) C → GaloisGroup (A := A) C → GaloisGroup (A := A) C :=
  CoveringSpace.DeckTransformation.comp

/-- Right identity for deck composition. -/
@[simp] theorem galoisComp_id (C : CoveringSpace.Covering A) (f : GaloisGroup (A := A) C) :
    galoisComp (A := A) C f (galoisId (A := A) C) = f := by
  simp [galoisComp, galoisId]

/-- Left identity for deck composition. -/
@[simp] theorem galoisId_comp (C : CoveringSpace.Covering A) (f : GaloisGroup (A := A) C) :
    galoisComp (A := A) C (galoisId (A := A) C) f = f := by
  simp [galoisComp, galoisId]

/-- Associativity of deck composition. -/
@[simp] theorem galoisComp_assoc (C : CoveringSpace.Covering A)
    (f g h : GaloisGroup (A := A) C) :
    galoisComp (A := A) C (galoisComp (A := A) C f g) h =
      galoisComp (A := A) C f (galoisComp (A := A) C g h) := by
  simp [galoisComp]

/-! ## Summary -/

/-!
We introduced the etale pi1 alias, monodromy on covering fibers, fiber-functor
objects with their actions, the Grothendieck correspondence between coverings
and groupoid actions, and the deck-transformation description of Galois groups.
-/

end GaloisTheoryCovers
end Homotopy
end Path
end ComputationalPaths
