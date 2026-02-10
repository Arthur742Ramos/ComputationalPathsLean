/-
# Equivariant Homotopy Theory

Lightweight definitions:
- G-spaces for strict group actions
- equivariant maps/equivalences
- fixed points
- Borel construction as a quotient

All proofs are complete.
-/

import ComputationalPaths.Path.EquivariantPaths
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace EquivariantHomotopy

open Algebra

universe u

/-- A G-space: a type with a strict group action. -/
structure GSpace (G : Type u) (S : StrictGroup G) where
  carrier : Type u
  action : GroupAction G S carrier

/-- Equivariant map. -/
structure GMap {G : Type u} {S : StrictGroup G} (X Y : GSpace G S) where
  toFun : X.carrier → Y.carrier
  equivariant : ∀ g x, toFun (X.action.act g x) = Y.action.act g (toFun x)

/-- Fixed points X^G. -/
def FixedPoints {G : Type u} {S : StrictGroup G} (X : GSpace G S) : Type u :=
  { x : X.carrier // ∀ g : G, X.action.act g x = x }

/-- Restriction of an equivariant map to fixed points. -/
def GMap.onFixedPoints {G : Type u} {S : StrictGroup G} {X Y : GSpace G S}
    (f : GMap X Y) : FixedPoints X → FixedPoints Y
  | ⟨x, hx⟩ => ⟨f.toFun x, fun g => by rw [← f.equivariant, hx g]⟩

/-- Borel data: EG as a contractible G-space. -/
structure BorelData (G : Type u) (S : StrictGroup G) where
  eg : GSpace G S
  contractible : ∀ x y : eg.carrier, x = y

/-- The Borel construction EG ×_G X as a quotient by the diagonal action relation. -/
def BorelSpace {G : Type u} {S : StrictGroup G}
    (bd : BorelData G S) (X : GSpace G S) : Type u :=
  Quot (fun (p q : bd.eg.carrier × X.carrier) =>
    ∃ g : G, bd.eg.action.act g p.1 = q.1 ∧ X.action.act g p.2 = q.2)

/-- Map into the Borel quotient. -/
def BorelSpace.mk {G : Type u} {S : StrictGroup G}
    (bd : BorelData G S) (X : GSpace G S) :
    bd.eg.carrier × X.carrier → BorelSpace bd X :=
  fun p => Quot.mk _ p

/-- Soundness lemma for the Borel quotient. -/
theorem BorelSpace.sound {G : Type u} {S : StrictGroup G}
    (bd : BorelData G S) (X : GSpace G S)
    (p : bd.eg.carrier × X.carrier) (g : G) :
    BorelSpace.mk bd X p =
      BorelSpace.mk bd X (bd.eg.action.act g p.1, X.action.act g p.2) :=
  Quot.sound ⟨g, rfl, rfl⟩

/-- Equivariant equivalence (strict inverse on points). -/
structure GEquiv {G : Type u} {S : StrictGroup G} (X Y : GSpace G S) where
  toFun : GMap X Y
  invFun : GMap Y X
  right_inv : ∀ y, toFun.toFun (invFun.toFun y) = y
  left_inv : ∀ x, invFun.toFun (toFun.toFun x) = x

end EquivariantHomotopy
end Homotopy
end Path
end ComputationalPaths
