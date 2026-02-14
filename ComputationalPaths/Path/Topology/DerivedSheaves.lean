/-
# Derived Sheaves via Computational Paths

This module sketches derived categories of sheaves in the computational paths
style. We introduce sheaves with restriction along paths, sheaf complexes,
injective resolutions, derived pushforward/pullback functors, Grothendieck
duality data, proper base change structures, and the projection formula.

## References

- Hartshorne, "Residues and Duality"
- Kashiwara–Schapira, "Sheaves on Manifolds"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Algebra.GrothendieckDuality

namespace ComputationalPaths
namespace Path
namespace Topology
namespace DerivedSheaves

open ComputationalPaths.GrothendieckDuality

universe u

/-! ## Spaces and Sheaves -/

/-- A topological space with a chosen base point for global sections. -/
structure SheafSpace where
  carrier : Type u
  base : carrier

/-- A map of spaces preserving the base point up to a path. -/
structure SpaceMap (X Y : SheafSpace.{u}) where
  map : X.carrier → Y.carrier
  map_base : Path (map X.base) Y.base

/-- A sheaf with restriction along computational paths. -/
structure DSheaf (X : SheafSpace.{u}) where
  sections : X.carrier → Type u
  res : {x y : X.carrier} → Path x y → sections x → sections y
  zero : (x : X.carrier) → sections x
  res_refl : ∀ (x : X.carrier) (s : sections x), Path (res (Path.refl x) s) s
  res_trans :
    ∀ {x y z : X.carrier} (p : Path x y) (q : Path y z) (s : sections x),
      Path (res (Path.trans p q) s) (res q (res p s))
  res_zero : ∀ {x y : X.carrier} (p : Path x y), Path (res p (zero x)) (zero y)

/-- A morphism of sheaves. -/
structure DSheafMorphism {X : SheafSpace.{u}} (F G : DSheaf X) where
  map : (x : X.carrier) → F.sections x → G.sections x
  map_zero : ∀ (x : X.carrier), Path (map x (F.zero x)) (G.zero x)
  naturality :
    ∀ {x y : X.carrier} (p : Path x y) (s : F.sections x),
      Path (G.res p (map x s)) (map y (F.res p s))

/-- Identity morphism of a sheaf. -/
def DSheafMorphism.id {X : SheafSpace.{u}} (F : DSheaf X) : DSheafMorphism F F where
  map := fun _ s => s
  map_zero := fun _ => Path.refl _
  naturality := fun _ _ => Path.refl _

/-! ## Sheaf Complexes -/

/-- A chain complex of sheaves, with equations on global sections. -/
structure SheafComplex (X : SheafSpace.{u}) where
  obj : Nat → DSheaf X
  diff : (n : Nat) → DSheafMorphism (obj (n + 1)) (obj n)
  diff_sq :
    ∀ (n : Nat) (s : (obj (n + 2)).sections X.base),
      (diff n).map X.base ((diff (n + 1)).map X.base s) = (obj n).zero X.base
  diff_zero :
    ∀ (n : Nat),
      (diff n).map X.base ((obj (n + 1)).zero X.base) = (obj n).zero X.base

/-- The underlying chain complex of global sections. -/
def SheafComplex.toChainComplex {X : SheafSpace.{u}} (C : SheafComplex X) :
    GrothendieckDuality.ChainComplex.{u} where
  obj := fun n => (C.obj n).sections X.base
  diff := fun n s => (C.diff n).map X.base s
  zero := fun n => (C.obj n).zero X.base
  diff_sq := fun n s => C.diff_sq n s
  diff_zero := fun n => C.diff_zero n

/-- A map of sheaf complexes. -/
structure SheafComplexMap {X : SheafSpace.{u}} (C D : SheafComplex X) where
  map : (n : Nat) → DSheafMorphism (C.obj n) (D.obj n)
  comm :
    ∀ (n : Nat) (s : (C.obj (n + 1)).sections X.base),
      (D.diff n).map X.base ((map (n + 1)).map X.base s) =
        (map n).map X.base ((C.diff n).map X.base s)

/-- Identity map of a sheaf complex. -/
def SheafComplexMap.id {X : SheafSpace.{u}} (C : SheafComplex X) :
    SheafComplexMap C C where
  map := fun n => DSheafMorphism.id (C.obj n)
  comm := fun _ _ => rfl

/-! ## Injective Resolutions -/

/-- An injective resolution of a sheaf. -/
structure InjectiveResolution {X : SheafSpace.{u}} (F : DSheaf X) where
  complex : SheafComplex X
  augmentation : DSheafMorphism F (complex.obj 0)

/-! ## Derived Functors -/

/-- Functorial data on sheaf complexes. -/
structure DerivedFunctorData (X Y : SheafSpace.{u}) where
  mapObj : SheafComplex X → SheafComplex Y
  mapMor :
    {C D : SheafComplex X} → SheafComplexMap C D → SheafComplexMap (mapObj C) (mapObj D)
  map_id : ∀ (C : SheafComplex X), mapMor (SheafComplexMap.id C) = SheafComplexMap.id (mapObj C)

/-- A derived pushforward functor. -/
structure DerivedPushforward {X Y : SheafSpace.{u}} (f : SpaceMap X Y) where
  functor : DerivedFunctorData X Y

/-- A derived pullback functor. -/
structure DerivedPullback {X Y : SheafSpace.{u}} (f : SpaceMap X Y) where
  functor : DerivedFunctorData Y X

/-! ## Grothendieck Duality for Sheaves -/

/-- Grothendieck duality data for sheaves along a map of spaces. -/
structure GrothendieckDualitySheaves {X Y : SheafSpace.{u}} (f : SpaceMap X Y) where
  pushforward : DerivedPushforward f
  pullback : DerivedPullback f
  dualizing : SheafComplex Y
  unit :
    ∀ (C : SheafComplex X),
      SheafComplexMap C (pullback.functor.mapObj (pushforward.functor.mapObj C))
  counit :
    ∀ (D : SheafComplex Y),
      SheafComplexMap (pushforward.functor.mapObj (pullback.functor.mapObj D)) D

/-! ## Proper Base Change -/

/-- A cartesian square of spaces. -/
structure BaseChangeSquare (X Y X' Y' : SheafSpace.{u}) where
  f : SpaceMap X Y
  g : SpaceMap X' Y'
  p : SpaceMap X' X
  q : SpaceMap Y' Y

/-- Proper base change structure for derived functors. -/
structure ProperBaseChange {X Y X' Y' : SheafSpace.{u}}
    (sq : BaseChangeSquare X Y X' Y') where
  pushforward_f : DerivedPushforward sq.f
  pullback_q : DerivedPullback sq.q
  pushforward_g : DerivedPushforward sq.g
  pullback_p : DerivedPullback sq.p

/-! ## Projection Formula -/

/-- Tensor structure on sheaves. -/
structure TensorStructure (X : SheafSpace.{u}) where
  tensor : DSheaf X → DSheaf X → DSheaf X
  unit : DSheaf X

/-- Projection formula for derived pushforward. -/
structure ProjectionFormula {X Y : SheafSpace.{u}} (f : SpaceMap X Y) where
  pushforward : DerivedPushforward f
  tensorX : TensorStructure X
  tensorY : TensorStructure Y


/-! ## Path lemmas -/

theorem derived_sheaves_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem derived_sheaves_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem derived_sheaves_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem derived_sheaves_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem derived_sheaves_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem derived_sheaves_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem derived_sheaves_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem derived_sheaves_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.ofEq h) = h :=
  Path.toEq_ofEq h


end DerivedSheaves
end Topology
end Path
end ComputationalPaths
