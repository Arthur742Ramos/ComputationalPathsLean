/-
# Generalized cohomology theories (computational paths)

This module introduces a lightweight interface for reduced generalized
cohomology theories on pointed types in the computational-path setting.
Functoriality and suspension isomorphisms are recorded with `Path`.

## Key Results

- `PathSimpleEquiv`, `ReducedCohomologyTheory`
- `ReducedCohomologyTheory.trivial`

## References

- Adams, "Stable Homotopy and Generalized Homology"
- HoTT Book, Chapter 8
-/

import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace GeneralizedCohomology

open SuspensionLoop

universe u

/-! ## Path-valued equivalences -/

/-- Path-based equivalence structure. -/
structure PathSimpleEquiv (α : Type u) (β : Type u) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Left inverse law witnessed by a path. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Right inverse law witnessed by a path. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Identity path equivalence. -/
def pathSimpleEquivRefl (α : Type u) : PathSimpleEquiv α α :=
  { toFun := _root_.id
    invFun := _root_.id
    left_inv := fun x => Path.refl x
    right_inv := fun x => Path.refl x }

/-- Composition of path equivalences. -/
def pathSimpleEquivComp {α β γ : Type u} (e : PathSimpleEquiv α β)
    (f : PathSimpleEquiv β γ) : PathSimpleEquiv α γ :=
  { toFun := fun x => f.toFun (e.toFun x)
    invFun := fun z => e.invFun (f.invFun z)
    left_inv := fun x =>
      Path.trans
        (Path.congrArg e.invFun (f.left_inv (e.toFun x)))
        (e.left_inv x)
    right_inv := fun z =>
      Path.trans
        (Path.congrArg f.toFun (e.right_inv (f.invFun z)))
        (f.right_inv z) }

/-! ## Reduced generalized cohomology theories -/

/-- Reduced generalized cohomology theory on pointed types. -/
structure ReducedCohomologyTheory where
  /-- Graded cohomology groups. -/
  cohomology : Nat → Pointed → Type u
  /-- Zero class in each degree. -/
  zero : ∀ (n : Nat) (X : Pointed), cohomology n X
  /-- Contravariant action on pointed maps. -/
  map : ∀ (n : Nat) {X Y : Pointed}, PointedMap X Y → cohomology n Y → cohomology n X
  /-- Functoriality on identities. -/
  mapId : ∀ (n : Nat) (X : Pointed) (x : cohomology n X),
      Path (map n (PointedMap.id X) x) x
  /-- Functoriality on compositions. -/
  mapComp :
    ∀ (n : Nat) {X Y Z : Pointed} (g : PointedMap Y Z) (f : PointedMap X Y)
      (x : cohomology n Z),
      Path (map n f (map n g x)) (map n (PointedMap.comp g f) x)
  /-- Suspension isomorphism. -/
  suspIso :
    ∀ (n : Nat) (X : Pointed),
      PathSimpleEquiv (cohomology n (suspPointed X.carrier)) (cohomology (n + 1) X)

namespace ReducedCohomologyTheory

/-- The trivial reduced cohomology theory. -/
def trivial : ReducedCohomologyTheory :=
  { cohomology := fun _ _ => PUnit
    zero := fun _ _ => PUnit.unit
    map := by intro _ _ _ _ _; exact PUnit.unit
    mapId := by
      intro n X x
      cases x
      exact Path.refl PUnit.unit
    mapComp := by
      intro n _ _ _ g f x
      cases x
      exact Path.refl PUnit.unit
    suspIso := fun _ _ => pathSimpleEquivRefl PUnit }

end ReducedCohomologyTheory

/-! ## Summary -/

end GeneralizedCohomology
end Homotopy
end Path
end ComputationalPaths
