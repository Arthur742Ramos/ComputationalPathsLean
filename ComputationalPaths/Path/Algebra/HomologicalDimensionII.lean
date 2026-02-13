/-
# Extended Homological Dimension Data

Tor/Ext computation data with dimension shifts and bounds, using Path-valued laws.

## Key Definitions
- `TorData`, `ExtData`, `DimensionShift`
- `ProjectiveDimBound`, `InjectiveDimBound`, `GlobalDimension`
- Trivial PUnit instances

## References
- Weibel, "An Introduction to Homological Algebra"
- Mac Lane, "Homology"
-/
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u

/-! ## Zero objects -/

/-- A pointed set is path-zero if every element is path-equal to zero. -/
def IsZeroPointed (A : PointedSet.{u}) : Type u :=
  ∀ x : A.carrier, Path x A.zero

private def punitPointed : PointedSet.{u} where
  carrier := PUnit
  zero := PUnit.unit

/-! ## Tor computation data -/

/-- Tor computation data for all degrees with Path-valued functoriality. -/
structure TorData where
  /-- Object assignment for Tor. -/
  obj : Nat → PointedSet.{u} → PointedSet.{u} → PointedSet.{u}
  /-- Morphism action for Tor. -/
  mapMor : {n : Nat} → {A A' : PointedSet.{u}} → {B B' : PointedSet.{u}} →
    PointedHom A A' → PointedHom B B' → PointedHom (obj n A B) (obj n A' B')
  /-- Identity law. -/
  map_id : ∀ n A B,
    Path (mapMor (n := n) (PointedHom.id A) (PointedHom.id B))
      (PointedHom.id (obj n A B))

/-! ## Ext computation data -/

/-- Ext computation data, contravariant in the first argument. -/
structure ExtData where
  /-- Object assignment for Ext. -/
  obj : Nat → PointedSet.{u} → PointedSet.{u} → PointedSet.{u}
  /-- Contravariant action on the first argument. -/
  map_left : {n : Nat} → {A A' : PointedSet.{u}} → {B : PointedSet.{u}} →
    PointedHom A A' → PointedHom (obj n A' B) (obj n A B)
  /-- Covariant action on the second argument. -/
  map_right : {n : Nat} → {A : PointedSet.{u}} → {B B' : PointedSet.{u}} →
    PointedHom B B' → PointedHom (obj n A B) (obj n A B')
  /-- Left identity law. -/
  map_left_id : ∀ n A B,
    Path (map_left (n := n) (B := B) (PointedHom.id A)) (PointedHom.id (obj n A B))
  /-- Right identity law. -/
  map_right_id : ∀ n A B,
    Path (map_right (n := n) (A := A) (PointedHom.id B)) (PointedHom.id (obj n A B))

/-! ## Dimension shifts -/

/-- A dimension shift relating Tor_{n+1} to Tor_n. -/
structure DimensionShift (T : TorData.{u}) where
  /-- Shift map from Tor_{n+1} to Tor_n. -/
  shift :
    ∀ n (A : PointedSet.{u}) (B : PointedSet.{u}),
      PointedHom (T.obj (Nat.succ n) A B) (T.obj n A B)
  /-- Naturality of the shift map. -/
  shift_natural :
    ∀ n {A A' : PointedSet.{u}} {B B' : PointedSet.{u}}
      (f : PointedHom A A') (g : PointedHom B B'),
      Path
        (PointedHom.comp (T.mapMor (n := n) f g) (shift n A B))
        (PointedHom.comp (shift n A' B') (T.mapMor (n := Nat.succ n) f g))

/-! ## Dimension bounds -/

/-- Projective dimension bound via vanishing Tor (for a fixed module A). -/
structure ProjectiveDimBound (T : TorData.{u}) (A : PointedSet.{u}) (bound : Nat) where
  /-- Vanishing of Tor above the bound for any B. -/
  vanish : ∀ n (B : PointedSet.{u}), bound < n → IsZeroPointed (T.obj n A B)

/-- Injective dimension bound via vanishing Ext (for a fixed module B). -/
structure InjectiveDimBound (E : ExtData.{u}) (B : PointedSet.{u}) (bound : Nat) where
  /-- Vanishing of Ext above the bound for any A. -/
  vanish : ∀ n (A : PointedSet.{u}), bound < n → IsZeroPointed (E.obj n A B)

/-- Global dimension bound for all modules. -/
structure GlobalDimension (T : TorData.{u}) (E : ExtData.{u}) (bound : Nat) where
  /-- Projective dimension bound for all modules. -/
  projective_bound : ∀ A, ProjectiveDimBound T A bound
  /-- Injective dimension bound for all modules. -/
  injective_bound : ∀ B, InjectiveDimBound E B bound

/-! ## Trivial PUnit instances -/

namespace TorData

/-- Trivial Tor data constant on the one-point set. -/
def trivial : TorData.{u} where
  obj := fun _ _ _ => punitPointed
  mapMor := fun _ _ => PointedHom.id punitPointed
  map_id := fun _ _ _ => Path.ofEqChain rfl

end TorData

namespace ExtData

/-- Trivial Ext data constant on the one-point set. -/
def trivial : ExtData.{u} where
  obj := fun _ _ _ => punitPointed
  map_left := fun _ => PointedHom.id punitPointed
  map_right := fun _ => PointedHom.id punitPointed
  map_left_id := fun _ _ _ => Path.ofEqChain rfl
  map_right_id := fun _ _ _ => Path.ofEqChain rfl

end ExtData

namespace DimensionShift

/-- The trivial dimension shift for the trivial Tor data. -/
def trivial : DimensionShift (TorData.trivial.{u}) where
  shift := fun _ _ _ => PointedHom.id punitPointed
  shift_natural := fun _ {_ _} {_ _} _ _ => Path.ofEqChain rfl

end DimensionShift

/-- Trivial projective dimension bound for the trivial Tor data. -/
def trivialProjectiveDimBound (bound : Nat) (A : PointedSet.{u}) :
    ProjectiveDimBound (TorData.trivial.{u}) A bound where
  vanish := fun _ _ _ x => by cases x; exact Path.refl _

/-- Trivial injective dimension bound for the trivial Ext data. -/
def trivialInjectiveDimBound (bound : Nat) (B : PointedSet.{u}) :
    InjectiveDimBound (ExtData.trivial.{u}) B bound where
  vanish := fun _ _ _ x => by cases x; exact Path.refl _

/-- Trivial global dimension bound for the trivial Tor/Ext data. -/
def trivialGlobalDimension (bound : Nat) :
    GlobalDimension (TorData.trivial.{u}) (ExtData.trivial.{u}) bound where
  projective_bound := fun A => trivialProjectiveDimBound bound A
  injective_bound := fun B => trivialInjectiveDimBound bound B

end Algebra
end Path
end ComputationalPaths
