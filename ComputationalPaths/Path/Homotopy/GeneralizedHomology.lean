/-
# Generalized Homology Theories (Path-based)

This module provides a minimal, compilable interface for generalized homology
theories on pointed types. Functoriality and suspension equivalences are recorded
as definitional equalities, with `Path` witnesses derived from them.

## Key Results

- `GeneralizedHomologyTheory`: data of a reduced generalized homology theory.
- `map_id_path`, `map_comp_path`, `map_zero_path`: `Path` witnesses of functoriality.
- `suspension_roundtrip_path`, `suspension_fwd_roundtrip_path`: `Path` witnesses
  for suspension equivalences.
- `trivialTheory`: constant homology theory on `PUnit`.

## References

- Hatcher, *Algebraic Topology*, Chapter 4
- Switzer, *Algebraic Topology - Homotopy and Homology*
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.PointedMapCategory

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace GeneralizedHomology

open PointedMapCategory

universe u v

/-! ## Generalized homology data -/

/-- Data for a reduced generalized homology theory on pointed types. -/
structure GeneralizedHomologyTheory where
  /-- The graded homology groups. -/
  H : PtdType.{u} → Nat → Type v
  /-- Zero element in each degree. -/
  zero : (X : PtdType.{u}) → (n : Nat) → H X n
  /-- Functoriality on pointed maps. -/
  map : {X Y : PtdType.{u}} → PtdMap X Y → (n : Nat) → H X n → H Y n
  /-- Maps send zero to zero. -/
  map_zero : ∀ {X Y : PtdType.{u}} (f : PtdMap X Y) (n : Nat),
    map f n (zero X n) = zero Y n
  /-- Identity law. -/
  map_id : ∀ X n, map (PtdMap.id X) n = _root_.id
  /-- Composition law. -/
  map_comp : ∀ {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat),
    map (PtdMap.comp g f) n = (map g n) ∘ (map f n)
  /-- Chosen suspension endofunctor. -/
  susp : PtdType.{u} → PtdType.{u}
  /-- Suspension isomorphism on homology. -/
  suspensionIso : ∀ X n, SimpleEquiv (H X n) (H (susp X) (n + 1))

namespace GeneralizedHomologyTheory

variable (E : GeneralizedHomologyTheory.{u, v})

/-! ## Path witnesses -/

/-- Path witness that maps preserve zero. -/
def map_zero_path {X Y : PtdType.{u}} (f : PtdMap X Y) (n : Nat) :
    Path (E.map f n (E.zero X n)) (E.zero Y n) :=
  Path.stepChain (E.map_zero f n)

/-- Path witness for identity functoriality. -/
def map_id_path (X : PtdType.{u}) (n : Nat) :
    Path (E.map (PtdMap.id X) n) _root_.id :=
  Path.stepChain (E.map_id X n)

/-- Path witness for composition. -/
def map_comp_path {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    Path (E.map (PtdMap.comp g f) n) ((E.map g n) ∘ (E.map f n)) :=
  Path.stepChain (E.map_comp g f n)

/-- Path witness for the suspension round-trip (left inverse). -/
def suspension_roundtrip_path (X : PtdType.{u}) (n : Nat) (x : E.H X n) :
    Path ((E.suspensionIso X n).invFun ((E.suspensionIso X n).toFun x)) x :=
  Path.stepChain ((E.suspensionIso X n).left_inv x)

/-- Path witness for the forward round-trip. -/
def suspension_fwd_roundtrip_path (X : PtdType.{u}) (n : Nat)
    (y : E.H (E.susp X) (n + 1)) :
    Path ((E.suspensionIso X n).toFun ((E.suspensionIso X n).invFun y)) y :=
  Path.stepChain ((E.suspensionIso X n).right_inv y)

end GeneralizedHomologyTheory

/-! ## Trivial example -/

/-- The trivial generalized homology theory with `PUnit` in every degree. -/
def trivialTheory : GeneralizedHomologyTheory.{u, v} where
  H := fun _ _ => PUnit
  zero := fun _ _ => PUnit.unit
  map := @fun _ _ _ _ _ => PUnit.unit
  map_zero := by
    intro X Y f n
    rfl
  map_id := by
    intro X n
    funext x
    cases x
    rfl
  map_comp := by
    intro X Y Z g f n
    funext x
    cases x
    rfl
  susp := fun X => X
  suspensionIso := fun _ _ => SimpleEquiv.refl _

/-! ## Summary

We introduce a minimal generalized homology theory interface on pointed types,
record functoriality and suspension equivalences, and provide `Path` witnesses
for the key round-trip laws. A trivial constant theory is included as a concrete
example.
-/

end GeneralizedHomology
end Homotopy
end Path
end ComputationalPaths
