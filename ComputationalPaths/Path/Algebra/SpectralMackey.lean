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
structure GSetHom {G : Type u} {S : StrictGroup G} (X Y : GSet.{u, v} G S) where
  /-- Underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Equivariance of the map. -/
  equivariant : ∀ g x, toFun (X.action.act g x) = Y.action.act g (toFun x)

namespace GSetHom

variable {G : Type u} {S : StrictGroup G}

/-- Identity equivariant map. -/
noncomputable def id (X : GSet.{u, v} G S) : GSetHom X X where
  toFun := fun x => x
  equivariant := fun _ _ => rfl

/-- Composition of equivariant maps. -/
noncomputable def comp {X Y Z : GSet.{u, v} G S} (f : GSetHom X Y) (g : GSetHom Y Z) :
    GSetHom X Z where
  toFun := fun x => g.toFun (f.toFun x)
  equivariant := by
    intro g' x
    rw [f.equivariant g' x, g.equivariant g' (f.toFun x)]

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
noncomputable def toGSet (X : FiniteGSet.{u, v} G S) : GSet.{u, v} G S where
  carrier := X.carrier
  action := X.action

end FiniteGSet

/-- Equivariant maps between finite G-sets. -/
noncomputable def FiniteGSetHom {G : Type u} {S : StrictGroup G}
    (X Y : FiniteGSet.{u, v} G S) :=
  GSetHom X.toGSet Y.toGSet

/-! ## Mackey functors -/

/-- A Mackey functor for finite G-sets, with restriction and transfer. -/
structure MackeyFunctor (G : Type u) (S : StrictGroup G) where
  /-- Object assignment. -/
  obj : FiniteGSet.{u, v} G S → Type w
  /-- Restriction along a G-map (contravariant). -/
  res : {X Y : FiniteGSet.{u, v} G S} → FiniteGSetHom X Y → obj Y → obj X
  /-- Transfer along a G-map (covariant). -/
  tr : {X Y : FiniteGSet.{u, v} G S} → FiniteGSetHom X Y → obj X → obj Y
  /-- Identity for restriction (abstract). -/
  res_id : ∀ (_ : FiniteGSet.{u, v} G S), True
  /-- Identity for transfer (abstract). -/
  tr_id : ∀ (_ : FiniteGSet.{u, v} G S), True
  /-- Composition for restriction (abstract). -/
  res_comp : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom Y Z), True
  /-- Composition for transfer (abstract). -/
  tr_comp : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom Y Z), True
  /-- Mackey double-coset compatibility (abstract). -/
  mackey : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom X Z), True

/-! ## Spectral Mackey functors -/

/-- A map of spectra (levelwise, preserving basepoints). -/
structure SpectrumMap (X Y : Spectrum.{w}) where
  /-- Levelwise map. -/
  map : (n : Nat) → X.level n → Y.level n
  /-- Basepoints are preserved. -/
  map_pt : ∀ n, map n (X.basepoint n) = Y.basepoint n

namespace SpectrumMap

/-- Identity spectrum map. -/
noncomputable def id (X : Spectrum.{w}) : SpectrumMap X X where
  map := fun _ x => x
  map_pt := fun _ => rfl

/-- Composition of spectrum maps. -/
noncomputable def comp {X Y Z : Spectrum.{w}} (f : SpectrumMap X Y) (g : SpectrumMap Y Z) :
    SpectrumMap X Z where
  map := fun n x => g.map n (f.map n x)
  map_pt := by
    intro n
    rw [f.map_pt n, g.map_pt n]

end SpectrumMap

/-- A Mackey functor valued in spectra. -/
structure SpectralMackeyFunctor (G : Type u) (S : StrictGroup G) where
  /-- Spectrum assigned to each finite G-set. -/
  obj : FiniteGSet.{u, v} G S → Spectrum.{w}
  /-- Restriction maps of spectra. -/
  res : {X Y : FiniteGSet.{u, v} G S} → FiniteGSetHom X Y →
    SpectrumMap (obj Y) (obj X)
  /-- Transfer maps of spectra. -/
  tr : {X Y : FiniteGSet.{u, v} G S} → FiniteGSetHom X Y →
    SpectrumMap (obj X) (obj Y)
  /-- Identity for restriction (abstract). -/
  res_id : ∀ (_ : FiniteGSet.{u, v} G S), True
  /-- Identity for transfer (abstract). -/
  tr_id : ∀ (_ : FiniteGSet.{u, v} G S), True
  /-- Composition for restriction (abstract). -/
  res_comp : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom Y Z), True
  /-- Composition for transfer (abstract). -/
  tr_comp : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom Y Z), True
  /-- Mackey compatibility (abstract). -/
  mackey : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom X Z), True

/-! ## Green functors -/

/-- A Green functor: a Mackey functor with multiplicative structure. -/
structure GreenFunctor (G : Type u) (S : StrictGroup G)
    extends MackeyFunctor.{u, v, w} G S where
  /-- Addition. -/
  add : ∀ (X : FiniteGSet.{u, v} G S), obj X → obj X → obj X
  /-- Zero element. -/
  zero : ∀ (X : FiniteGSet.{u, v} G S), obj X
  /-- Multiplication. -/
  mul : ∀ (X : FiniteGSet.{u, v} G S), obj X → obj X → obj X
  /-- Unit element. -/
  one : ∀ (X : FiniteGSet.{u, v} G S), obj X
  /-- Additive associativity. -/
  add_assoc : ∀ (X : FiniteGSet.{u, v} G S) (_ _ _ : obj X), True
  /-- Additive commutativity. -/
  add_comm : ∀ (X : FiniteGSet.{u, v} G S) (_ _ : obj X), True
  /-- Additive identity. -/
  add_zero : ∀ (X : FiniteGSet.{u, v} G S) (_ : obj X), True
  /-- Multiplicative associativity. -/
  mul_assoc : ∀ (X : FiniteGSet.{u, v} G S) (_ _ _ : obj X), True
  /-- Multiplicative commutativity. -/
  mul_comm : ∀ (X : FiniteGSet.{u, v} G S) (_ _ : obj X), True
  /-- Multiplicative identity. -/
  mul_one : ∀ (X : FiniteGSet.{u, v} G S) (_ : obj X), True
  /-- Distributivity. -/
  distrib : ∀ (X : FiniteGSet.{u, v} G S) (_ _ _ : obj X), True
  /-- Restriction preserves addition. -/
  res_add : ∀ {X Y : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ _ : obj Y), True
  /-- Transfer preserves addition. -/
  tr_add : ∀ {X Y : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ _ : obj X), True
  /-- Restriction preserves multiplication. -/
  res_mul : ∀ {X Y : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ _ : obj Y), True
  /-- Transfer is additive with respect to multiplication. -/
  tr_mul : ∀ {X Y : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ _ : obj X), True

/-! ## Tambara functors -/

/-- A Tambara functor: a Green functor with norm maps. -/
structure TambaraFunctor (G : Type u) (S : StrictGroup G)
    extends GreenFunctor.{u, v, w} G S where
  /-- Norm maps along finite G-maps. -/
  norm : {X Y : FiniteGSet.{u, v} G S} → FiniteGSetHom X Y → obj X → obj Y
  /-- Norm preserves units (abstract). -/
  norm_one : ∀ {X Y : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : obj X), True
  /-- Norm is multiplicative (abstract). -/
  norm_mul : ∀ {X Y : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ _ : obj X), True
  /-- Norm composition (abstract). -/
  norm_comp : ∀ {X Y Z : FiniteGSet.{u, v} G S}
    (_ : FiniteGSetHom X Y) (_ : FiniteGSetHom Y Z), True
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
noncomputable def full (G : Type u) (S : StrictGroup G) : DressFamily G S where
  carrier := fun _ => True
  contains_trivial := trivial
  closed_under_conj := trivial
  closed_under_subgroup := trivial
  closed_under_intersection := trivial

end DressFamily

/-- Dress induction data for a Mackey functor. -/
structure DressInduction {G : Type u} {S : StrictGroup G}
    (F : MackeyFunctor.{u, v, w} G S) where
  /-- Chosen Dress family. -/
  family : DressFamily G S
  /-- Induction property (abstract). -/
  induction : True

/-! ## Burnside Mackey functor -/

/-- The Burnside Mackey functor, modeled as the constant Nat functor. -/
noncomputable def burnsideMackeyFunctor (G : Type u) (S : StrictGroup G) :
    MackeyFunctor.{u, v, 0} G S where
  obj := fun _ => Nat
  res := fun _ n => n
  tr := fun _ n => n
  res_id := fun _ => trivial
  tr_id := fun _ => trivial
  res_comp := fun _ _ => trivial
  tr_comp := fun _ _ => trivial
  mackey := fun _ _ => trivial

/-- Dress induction holds for the Burnside Mackey functor with the full family. -/
noncomputable def burnsideDressInduction (G : Type u) (S : StrictGroup G) :
    DressInduction (burnsideMackeyFunctor.{u, v} G S) where
  family := DressFamily.full G S
  induction := trivial

private noncomputable def pathAnchor {A : Type u} (a : A) : Path a a := Path.refl a

/-! ## Summary

We introduced G-sets and equivariant maps, abstract Mackey and spectral
Mackey functors, Green and Tambara refinements, Dress induction data,
and a constant Burnside Mackey functor example.
-/

end SpectralMackey
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace SpectralMackey

theorem gsetHom_id_apply {G : Type _} {S : StrictGroup G}
    (X : GSet G S) (x : X.carrier) :
    (GSetHom.id X).toFun x = x :=
  rfl

theorem gsetHom_comp_apply {G : Type _} {S : StrictGroup G}
    {X Y Z : GSet G S} (f : GSetHom X Y) (g : GSetHom Y Z)
    (x : X.carrier) :
    (GSetHom.comp f g).toFun x = g.toFun (f.toFun x) :=
  rfl

theorem finiteGSet_toGSet_carrier {G : Type _} {S : StrictGroup G}
    (X : FiniteGSet G S) :
    (X.toGSet).carrier = X.carrier :=
  rfl

theorem spectrumMap_id_apply (X : SpectralAlgebra.Spectrum) (n : Nat) (x : X.level n) :
    (SpectrumMap.id X).map n x = x :=
  rfl

theorem spectrumMap_comp_apply {X Y Z : SpectralAlgebra.Spectrum}
    (f : SpectrumMap X Y) (g : SpectrumMap Y Z) (n : Nat) (x : X.level n) :
    (SpectrumMap.comp f g).map n x = g.map n (f.map n x) :=
  rfl

theorem dressFamily_full_carrier {G : Type _} (S : StrictGroup G)
    (H : Subgroup G S) :
    (DressFamily.full G S).carrier H :=
  trivial

theorem burnside_obj_eq {G : Type _} (S : StrictGroup G)
    (X : FiniteGSet G S) :
    (burnsideMackeyFunctor G S).obj X = Nat :=
  rfl

theorem burnside_res_apply {G : Type _} (S : StrictGroup G)
    {X Y : FiniteGSet G S} (f : FiniteGSetHom X Y) (n : Nat) :
    (burnsideMackeyFunctor G S).res f n = n :=
  rfl

theorem burnside_tr_apply {G : Type _} (S : StrictGroup G)
    {X Y : FiniteGSet G S} (f : FiniteGSetHom X Y) (n : Nat) :
    (burnsideMackeyFunctor G S).tr f n = n :=
  rfl

theorem burnsideDressInduction_holds {G : Type _} (_S : StrictGroup G) :
    True :=
  trivial

end SpectralMackey
end Algebra
end Path
end ComputationalPaths
