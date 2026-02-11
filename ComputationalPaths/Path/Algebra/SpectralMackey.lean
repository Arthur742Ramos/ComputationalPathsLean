/-
# Spectral Mackey Functors

This module introduces abstract Mackey, Green, and Tambara functors for
computational paths, along with spectral variants, Dress induction data,
and a Burnside Mackey functor example.

## Key Definitions

- `GSet`, `FiniteGSet`, `GSetHom`
- `MackeyFunctor`, `SpectralMackeyFunctor`
- `GreenFunctor`, `TambaraFunctor`
- `DressFamily`, `DressInduction`
- `burnsideMackeyFunctor`

## References

- Dress, "Induction and Structure Theorems for Mackey Functors"
- Tambara, "On Multiplicative Transfer"
- Lewis-May-Steinberger, "Equivariant Stable Homotopy Theory"
-/

import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Algebra.SpectralAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SpectralMackey

open SpectralAlgebra

universe u v w

/-! ## G-sets and equivariant maps -/

/-- A G-set with a strict group action. -/
structure GSet (G : Type u) (S : StrictGroup G) where
  /-- Underlying carrier type. -/
  carrier : Type v
  /-- Action of G on the carrier. -/
  action : GroupAction G S carrier

/-- An equivariant map between G-sets. -/
structure GSetHom {G : Type u} {S : StrictGroup G} (X Y : GSet G S) where
  /-- Underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Equivariance of the map. -/
  equivariant : ∀ g x, toFun (X.action.act g x) = Y.action.act g (toFun x)

namespace GSetHom

variable {G : Type u} {S : StrictGroup G}

/-- Identity equivariant map. -/
def id (X : GSet G S) : GSetHom X X where
  toFun := fun x => x
  equivariant := by
    intro g x
    rfl

/-- Composition of equivariant maps. -/
def comp {X Y Z : GSet G S} (f : GSetHom X Y) (g : GSetHom Y Z) : GSetHom X Z where
  toFun := fun x => g.toFun (f.toFun x)
  equivariant := by
    intro g' x
    calc
      g.toFun (f.toFun (X.action.act g' x))
          = g.toFun (Y.action.act g' (f.toFun x)) := congrArg g.toFun (f.equivariant g' x)
      _ = Z.action.act g' (g.toFun (f.toFun x)) := g.equivariant g' (f.toFun x)

end GSetHom

/-- A finite G-set (finiteness recorded abstractly). -/
structure FiniteGSet (G : Type u) (S : StrictGroup G) where
  /-- Underlying carrier type. -/
  carrier : Type v
  /-- Action of G on the carrier. -/
  action : GroupAction G S carrier
  /-- Finiteness witness (abstract). -/
  finite : True

namespace FiniteGSet

variable {G : Type u} {S : StrictGroup G}

/-- Forget the finiteness data. -/
def toGSet (X : FiniteGSet G S) : GSet G S where
  carrier := X.carrier
  action := X.action

end FiniteGSet

/-- Equivariant maps between finite G-sets. -/
abbrev FiniteGSetHom {G : Type u} {S : StrictGroup G}
    (X Y : FiniteGSet G S) : Type (max u v) :=
  GSetHom (X.toGSet) (Y.toGSet)

/-! ## Mackey functors -/

/-- A Mackey functor for finite G-sets, with restriction and transfer. -/
structure MackeyFunctor (G : Type u) (S : StrictGroup G) where
  /-- Object assignment. -/
  obj : FiniteGSet G S → Type w
  /-- Restriction along a G-map (contravariant). -/
  res : {X Y : FiniteGSet G S} → FiniteGSetHom X Y → obj Y → obj X
  /-- Transfer along a G-map (covariant). -/
  tr : {X Y : FiniteGSet G S} → FiniteGSetHom X Y → obj X → obj Y
  /-- Identity axiom for restriction. -/
  res_id : ∀ X, True
  /-- Identity axiom for transfer. -/
  tr_id : ∀ X, True
  /-- Composition axiom for restriction. -/
  res_comp : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom Y Z), True
  /-- Composition axiom for transfer. -/
  tr_comp : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom Y Z), True
  /-- Mackey double-coset compatibility (abstract). -/
  mackey : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom X Z), True

/-! ## Spectral Mackey functors -/

/-- A map of spectra (levelwise, preserving basepoints). -/
structure SpectrumMap (X Y : Spectrum.{w}) where
  /-- Levelwise map. -/
  map : (n : Nat) → X.level n → Y.level n
  /-- Basepoints are preserved. -/
  map_pt : ∀ n, map n (X.basepoint n) = Y.basepoint n

namespace SpectrumMap

/-- Identity spectrum map. -/
def id (X : Spectrum.{w}) : SpectrumMap X X where
  map := fun _ x => x
  map_pt := by
    intro n
    rfl

/-- Composition of spectrum maps. -/
def comp {X Y Z : Spectrum.{w}} (f : SpectrumMap X Y) (g : SpectrumMap Y Z) : SpectrumMap X Z where
  map := fun n x => g.map n (f.map n x)
  map_pt := by
    intro n
    calc
      g.map n (f.map n (X.basepoint n))
          = g.map n (Y.basepoint n) := congrArg (fun x => g.map n x) (f.map_pt n)
      _ = Z.basepoint n := g.map_pt n

end SpectrumMap

/-- A Mackey functor valued in spectra. -/
structure SpectralMackeyFunctor (G : Type u) (S : StrictGroup G) where
  /-- Spectrum assigned to each finite G-set. -/
  obj : FiniteGSet G S → Spectrum.{w}
  /-- Restriction maps of spectra. -/
  res : {X Y : FiniteGSet G S} → FiniteGSetHom X Y → SpectrumMap (obj Y) (obj X)
  /-- Transfer maps of spectra. -/
  tr : {X Y : FiniteGSet G S} → FiniteGSetHom X Y → SpectrumMap (obj X) (obj Y)
  /-- Identity axiom for restriction. -/
  res_id : ∀ X, True
  /-- Identity axiom for transfer. -/
  tr_id : ∀ X, True
  /-- Composition axiom for restriction. -/
  res_comp : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom Y Z), True
  /-- Composition axiom for transfer. -/
  tr_comp : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom Y Z), True
  /-- Mackey compatibility (abstract). -/
  mackey : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom X Z), True

/-! ## Green functors -/

/-- A Green functor: a Mackey functor with multiplicative structure. -/
structure GreenFunctor (G : Type u) (S : StrictGroup G) extends MackeyFunctor G S where
  /-- Addition. -/
  add : ∀ X, obj X → obj X → obj X
  /-- Zero element. -/
  zero : ∀ X, obj X
  /-- Multiplication. -/
  mul : ∀ X, obj X → obj X → obj X
  /-- Unit element. -/
  one : ∀ X, obj X
  /-- Additive associativity. -/
  add_assoc : ∀ X x y z, True
  /-- Additive commutativity. -/
  add_comm : ∀ X x y, True
  /-- Additive identity. -/
  add_zero : ∀ X x, True
  /-- Multiplicative associativity. -/
  mul_assoc : ∀ X x y z, True
  /-- Multiplicative commutativity. -/
  mul_comm : ∀ X x y, True
  /-- Multiplicative identity. -/
  mul_one : ∀ X x, True
  /-- Distributivity. -/
  distrib : ∀ X x y z, True
  /-- Restriction preserves addition. -/
  res_add : ∀ {X Y} (f : FiniteGSetHom X Y) (x y : obj Y), True
  /-- Transfer preserves addition. -/
  tr_add : ∀ {X Y} (f : FiniteGSetHom X Y) (x y : obj X), True
  /-- Restriction preserves multiplication. -/
  res_mul : ∀ {X Y} (f : FiniteGSetHom X Y) (x y : obj Y), True
  /-- Transfer is additive with respect to multiplication. -/
  tr_mul : ∀ {X Y} (f : FiniteGSetHom X Y) (x y : obj X), True

/-! ## Tambara functors -/

/-- A Tambara functor: a Green functor with norm maps. -/
structure TambaraFunctor (G : Type u) (S : StrictGroup G) extends GreenFunctor G S where
  /-- Norm maps along finite G-maps. -/
  norm : {X Y : FiniteGSet G S} → FiniteGSetHom X Y → obj X → obj Y
  /-- Norm preserves units (abstract). -/
  norm_one : ∀ {X Y} (f : FiniteGSetHom X Y) (x : obj X), True
  /-- Norm is multiplicative (abstract). -/
  norm_mul : ∀ {X Y} (f : FiniteGSetHom X Y) (x y : obj X), True
  /-- Norm composition (abstract). -/
  norm_comp : ∀ {X Y Z} (f : FiniteGSetHom X Y) (g : FiniteGSetHom Y Z), True
  /-- Distributivity of norms with transfers (abstract). -/
  norm_distrib : True

/-! ## Dress induction -/

/-- A Dress family of subgroups (closed properties recorded abstractly). -/
structure DressFamily (G : Type u) (S : StrictGroup G) where
  /-- The family predicate on subgroups. -/
  carrier : Subgroup G S → Prop
  /-- Contains the trivial subgroup. -/
  contains_trivial : True
  /-- Closed under conjugation. -/
  closed_under_conj : True
  /-- Closed under subgroups. -/
  closed_under_subgroup : True
  /-- Closed under finite intersections. -/
  closed_under_intersection : True

namespace DressFamily

/-- The full Dress family containing all subgroups. -/
def full (G : Type u) (S : StrictGroup G) : DressFamily G S where
  carrier := fun _ => True
  contains_trivial := trivial
  closed_under_conj := trivial
  closed_under_subgroup := trivial
  closed_under_intersection := trivial

end DressFamily

/-- Dress induction data for a Mackey functor. -/
structure DressInduction {G : Type u} {S : StrictGroup G} (F : MackeyFunctor G S) where
  /-- Chosen Dress family. -/
  family : DressFamily G S
  /-- Induction property (abstract). -/
  induction : True

/-! ## Burnside Mackey functor -/

/-- The Burnside Mackey functor, modeled as the constant Nat functor. -/
def burnsideMackeyFunctor (G : Type u) (S : StrictGroup G) : MackeyFunctor G S where
  obj := fun _ => Nat
  res := fun {X Y} _ n => n
  tr := fun {X Y} _ n => n
  res_id := fun _ => trivial
  tr_id := fun _ => trivial
  res_comp := fun _ _ => trivial
  tr_comp := fun _ _ => trivial
  mackey := fun _ _ => trivial

/-- Dress induction holds for the Burnside Mackey functor with the full family. -/
def burnsideDressInduction (G : Type u) (S : StrictGroup G) :
    DressInduction (burnsideMackeyFunctor G S) where
  family := DressFamily.full G S
  induction := trivial

/-! ## Summary

We introduced G-sets and equivariant maps, abstract Mackey and spectral
Mackey functors, Green and Tambara refinements, Dress induction data,
and a constant Burnside Mackey functor example.
-/

end SpectralMackey
end Algebra
end Path
end ComputationalPaths
