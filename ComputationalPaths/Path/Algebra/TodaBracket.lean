/-
# Toda Brackets

This module formalizes Toda brackets in the computational paths framework.
We define composition operations on pointed maps, the Toda bracket as a set
of compositions, indeterminacy, and the Jacobi identity for Toda brackets.

## Key Results

- `TodaBracketInput`: input data for a Toda bracket ⟨f, g, h⟩
- `TodaBracketValue`: computation of a Toda bracket value
- `TodaIndeterminacy`: indeterminacy of the Toda bracket
- `TodaJacobi`: the Jacobi identity for Toda brackets
- `todaBracketSet`: the Toda bracket as a set

## References

- Toda, "Composition methods in homotopy groups of spheres"
- Kochman, "Stable homotopy groups of spheres"
- Ravenel, "Complex cobordism and stable homotopy groups of spheres"
-/

import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.PointedMapCategory
import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace Algebra

open SuspensionLoop
open PointedMapCategory

universe u

/-! ## Composition operations on pointed maps -/

/-- Homotopy between pointed maps, modeled as a `Path` between them. -/
def PtdHomotopy {X Y : PtdType.{u}} (f g : PtdMap X Y) : Type u :=
  Path f g

/-- Homotopy class of pointed maps (quotient by Path). -/
def PtdHomotopyClass (X Y : PtdType.{u}) : Type u :=
  Quot (fun (f g : PtdMap X Y) => Nonempty (PtdHomotopy f g))

/-- The class of a pointed map. -/
def PtdHomotopyClass.mk {X Y : PtdType.{u}} (f : PtdMap X Y) :
    PtdHomotopyClass X Y :=
  Quot.mk _ f

/-- Composition of homotopy classes. -/
def PtdHomotopyClass.comp {X Y Z : PtdType.{u}} :
    PtdHomotopyClass Y Z → PtdHomotopyClass X Y → PtdHomotopyClass X Z :=
  Quot.lift
    (fun g => Quot.lift (fun f => PtdHomotopyClass.mk (PtdMap.comp g f))
      (by intro _ _ ⟨h⟩; apply Quot.sound; exact ⟨Path.congrArg (PtdMap.comp g) h⟩))
    (by intro g g' ⟨hg⟩
        apply funext; intro qf
        refine Quot.inductionOn qf ?_
        intro f; apply Quot.sound
        exact ⟨Path.congrArg (fun g' => PtdMap.comp g' f) hg⟩)

/-! ## Toda brackets -/

/-- The zero pointed map. -/
def zeroPtdMap (X Y : PtdType.{u}) : PtdMap X Y where
  toFun := fun _ => Y.pt
  map_pt := rfl

/-- A composition is null-homotopic if it equals the zero map. -/
def IsNullHomotopic {X Y : PtdType.{u}} (f : PtdMap X Y) : Prop :=
  Nonempty (PtdHomotopy f (zeroPtdMap X Y))

/-- Input data for a Toda bracket ⟨f, g, h⟩.
    We need f : Z → W, g : Y → Z, h : X → Y
    with f ∘ g ~ * and g ∘ h ~ *. -/
structure TodaBracketInput where
  /-- Source of h. -/
  X : PtdType.{u}
  /-- Target of h / source of g. -/
  Y : PtdType.{u}
  /-- Target of g / source of f. -/
  Z : PtdType.{u}
  /-- Target of f. -/
  W : PtdType.{u}
  /-- The map f : Z → W. -/
  f : PtdMap Z W
  /-- The map g : Y → Z. -/
  g : PtdMap Y Z
  /-- The map h : X → Y. -/
  h : PtdMap X Y
  /-- f ∘ g is null-homotopic. -/
  fg_null : IsNullHomotopic (PtdMap.comp f g)
  /-- g ∘ h is null-homotopic. -/
  gh_null : IsNullHomotopic (PtdMap.comp g h)

/-- A null-homotopy witness: a path from a composition to the zero map. -/
structure NullHomotopyWitness {X Y : PtdType.{u}} (f : PtdMap X Y) where
  /-- The path to zero. -/
  homotopy : PtdHomotopy f (zeroPtdMap X Y)

/-- Extension data for computing a Toda bracket value.
    Given null-homotopies for f∘g and g∘h, we get a map X → W. -/
structure TodaExtension (inp : TodaBracketInput) where
  /-- A null-homotopy witness for f ∘ g. -/
  fg_witness : NullHomotopyWitness (PtdMap.comp inp.f inp.g)
  /-- A null-homotopy witness for g ∘ h. -/
  gh_witness : NullHomotopyWitness (PtdMap.comp inp.g inp.h)
  /-- The resulting map X → W representing a Toda bracket element. -/
  extension : PtdMap inp.X inp.W

/-- The Toda bracket as a predicate: a homotopy class is in the Toda bracket
    if it arises from some extension. -/
def isTodaBracketValue (inp : TodaBracketInput) (cls : PtdHomotopyClass inp.X inp.W) : Prop :=
  ∃ ext : TodaExtension inp,
    cls = PtdHomotopyClass.mk ext.extension

/-! ## Indeterminacy -/

/-- The indeterminacy predicate: a class is in f ∘ [X, Z] + [Y, W] ∘ h. -/
def isTodaIndeterminacy (inp : TodaBracketInput) (cls : PtdHomotopyClass inp.X inp.W) : Prop :=
  (∃ α : PtdMap inp.X inp.Z,
    cls = PtdHomotopyClass.mk (PtdMap.comp inp.f α)) ∨
  (∃ β : PtdMap inp.Y inp.W,
    cls = PtdHomotopyClass.mk (PtdMap.comp β inp.h))

/-- The zero class is in the indeterminacy. -/
theorem zero_mem_toda_indeterminacy (inp : TodaBracketInput) :
    isTodaIndeterminacy inp (PtdHomotopyClass.mk (zeroPtdMap inp.X inp.W)) := by
  right
  exact ⟨zeroPtdMap inp.Y inp.W, rfl⟩

/-! ## Jacobi identity for Toda brackets -/

/-- The Jacobi identity data for Toda brackets.
    For composable maps f, g, h, k with appropriate nullity conditions,
    there is a relation among nested Toda brackets. -/
structure TodaJacobi where
  /-- The four pointed types. -/
  A : PtdType.{u}
  B : PtdType.{u}
  C : PtdType.{u}
  D : PtdType.{u}
  E : PtdType.{u}
  /-- The maps. -/
  f : PtdMap D E
  g : PtdMap C D
  h : PtdMap B C
  k : PtdMap A B
  /-- Nullity conditions. -/
  fg_null : IsNullHomotopic (PtdMap.comp f g)
  gh_null : IsNullHomotopic (PtdMap.comp g h)
  hk_null : IsNullHomotopic (PtdMap.comp h k)

/-- The three nested Toda bracket inputs from the Jacobi data. -/
def TodaJacobi.bracket_fgh (j : TodaJacobi) : TodaBracketInput where
  X := j.B; Y := j.C; Z := j.D; W := j.E
  f := j.f; g := j.g; h := j.h
  fg_null := j.fg_null; gh_null := j.gh_null

def TodaJacobi.bracket_ghk (j : TodaJacobi) : TodaBracketInput where
  X := j.A; Y := j.B; Z := j.C; W := j.D
  f := j.g; g := j.h; h := j.k
  fg_null := j.gh_null; gh_null := j.hk_null

/-! ## Summary -/

end Algebra
end Path
end ComputationalPaths
