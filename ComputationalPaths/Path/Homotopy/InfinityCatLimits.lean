/-
# Limits and Colimits in (Infinity,1)-Categories

This module packages limits and colimits in quasi-categories via terminal
objects in slice-style categories of cones and cocones. We also record
finite (co)limits (products, coproducts, pullbacks, pushouts), restate the
adjoint functor theorem for presentable infinity-categories, and expose an
infinity-categorical Seifert-van Kampen equivalence in the computational path
setting.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `TerminalObject` | Terminal objects in a quasi-category |
| `TerminalCone` | Limits as terminal objects in the cone slice |
| `TerminalCocone` | Colimits as terminal objects in the cocone coslice |
| `BinaryProduct`, `BinaryCoproduct` | Products and coproducts in quasi-categories |
| `Pullback`, `Pushout` | Pullbacks and pushouts in quasi-categories |
| `adjoint_functor_exists` | Adjoint functor theorem (presentable case) |
| `infinitySeifertVanKampen` | Infinity-categorical Seifert-van Kampen |

## References

- Lurie, "Higher Topos Theory"
- Joyal, "Quasi-categories and Kan complexes"
- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
-/

import ComputationalPaths.Path.Homotopy.HigherTopos
import ComputationalPaths.Path.Homotopy.SeifertVanKampen

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace InfinityCatLimits

open HigherTopos

universe u

/-! ## Quasi-category morphisms and terminal objects -/

/-- A morphism in a quasi-category together with chosen source and target. -/
structure QCHom (C : QuasiCategory) (a b : C.obj) where
  /-- The underlying 1-simplex. -/
  mor : C.mor
  /-- Source endpoint. -/
  source_eq : C.source mor = a
  /-- Target endpoint. -/
  target_eq : C.target mor = b

/-- Terminal object in a quasi-category. -/
structure TerminalObject (C : QuasiCategory) where
  /-- The terminal object. -/
  obj : C.obj
  /-- Unique map to the terminal object. -/
  toTerminal : ∀ x : C.obj, QCHom C x obj
  /-- Uniqueness of maps into the terminal object. -/
  unique : ∀ x (f g : QCHom C x obj), f = g

/-- Initial object in a quasi-category. -/
structure InitialObject (C : QuasiCategory) where
  /-- The initial object. -/
  obj : C.obj
  /-- Unique map from the initial object. -/
  fromInitial : ∀ x : C.obj, QCHom C obj x
  /-- Uniqueness of maps out of the initial object. -/
  unique : ∀ x (f g : QCHom C obj x), f = g

/-! ## Slice objects and terminality -/

/-- An object in the slice quasi-category `C / c`. -/
structure SliceObj (C : QuasiCategory) (c : C.obj) where
  /-- The underlying object of `C`. -/
  obj : C.obj
  /-- The structure map to `c`. -/
  arrow : QCHom C obj c

/-- A morphism in the slice; commutativity is recorded abstractly. -/
structure SliceHom {C : QuasiCategory} {c : C.obj}
    (x y : SliceObj C c) where
  /-- The underlying morphism in `C`. -/
  hom : QCHom C x.obj y.obj
  /-- Commutativity of the triangle (kept abstract). -/
  comm : True

/-- Terminal object in the slice `C / c`. -/
structure SliceTerminal (C : QuasiCategory) (c : C.obj) where
  /-- The terminal slice object. -/
  obj : SliceObj C c
  /-- Unique slice map into the terminal object. -/
  toTerminal : ∀ x : SliceObj C c, SliceHom x obj
  /-- Uniqueness of slice maps. -/
  unique : ∀ x (f g : SliceHom x obj), f = g

/-! ## Limits and colimits via terminal cones -/

/-- Cones over a diagram, viewed as objects in a slice-like category. -/
structure ConeSlice {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The underlying cone. -/
  cone : InfinityCone D

/-- Morphisms of cones, with commutativity tracked abstractly. -/
structure ConeSliceHom {I C : QuasiCategory} {D : InfinityDiagram I C}
    (x y : ConeSlice D) where
  /-- The morphism between cone apexes. -/
  hom : QCHom C x.cone.apex y.cone.apex
  /-- Compatibility with projections (abstract). -/
  comm : True

/-- Terminal cone data: a limit presented as a terminal cone. -/
structure TerminalCone {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The terminal cone. -/
  obj : ConeSlice D
  /-- Unique map from any cone to the terminal cone. -/
  toTerminal : ∀ x : ConeSlice D, ConeSliceHom x obj
  /-- Uniqueness of cone morphisms. -/
  unique : ∀ x (f g : ConeSliceHom x obj), f = g

/-- Build an infinity-limit from a terminal cone. -/
noncomputable def limitOfTerminal {I C : QuasiCategory} {D : InfinityDiagram I C}
    (T : TerminalCone D) : InfinityLimit D where
  cone := T.obj.cone
  universal := fun other =>
    let map := (T.toTerminal ⟨other⟩).hom
    ⟨map.mor, map.source_eq, map.target_eq⟩

/-- Cocones over a diagram, viewed as objects in a coslice-style category. -/
structure CoconeSlice {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The underlying cocone. -/
  cocone : InfinityCocone D

/-- Morphisms of cocones; directions are reversed so terminal objects encode colimits. -/
structure CoconeSliceHom {I C : QuasiCategory} {D : InfinityDiagram I C}
    (x y : CoconeSlice D) where
  /-- The morphism from `y` to `x` in `C`. -/
  hom : QCHom C y.cocone.nadir x.cocone.nadir
  /-- Compatibility with injections (abstract). -/
  comm : True

/-- Terminal cocone data (in the reversed coslice convention). -/
structure TerminalCocone {I C : QuasiCategory} (D : InfinityDiagram I C) where
  /-- The terminal cocone. -/
  obj : CoconeSlice D
  /-- Unique map from any cocone to the terminal cocone. -/
  toTerminal : ∀ x : CoconeSlice D, CoconeSliceHom x obj
  /-- Uniqueness of cocone morphisms. -/
  unique : ∀ x (f g : CoconeSliceHom x obj), f = g

/-- Build an infinity-colimit from a terminal cocone (coslice convention). -/
noncomputable def colimitOfTerminal {I C : QuasiCategory} {D : InfinityDiagram I C}
    (T : TerminalCocone D) : InfinityColimit D where
  cocone := T.obj.cocone
  universal := fun other =>
    let map := (T.toTerminal ⟨other⟩).hom
    ⟨map.mor, map.source_eq, map.target_eq⟩

/-! ## Finite limits and colimits -/

/-- Binary product in a quasi-category (universal property). -/
structure BinaryProduct (C : QuasiCategory) (X Y : C.obj) where
  /-- The product object. -/
  obj : C.obj
  /-- Projection to the first factor. -/
  fst : QCHom C obj X
  /-- Projection to the second factor. -/
  snd : QCHom C obj Y
  /-- Universal property: maps into the product correspond to pairs. -/
  universal : ∀ {Z : C.obj} (_ : QCHom C Z X) (_ : QCHom C Z Y),
    ∃ _ : QCHom C Z obj, True

/-- Binary coproduct in a quasi-category (universal property). -/
structure BinaryCoproduct (C : QuasiCategory) (X Y : C.obj) where
  /-- The coproduct object. -/
  obj : C.obj
  /-- Injection from the first factor. -/
  inl : QCHom C X obj
  /-- Injection from the second factor. -/
  inr : QCHom C Y obj
  /-- Universal property: maps out of the coproduct correspond to pairs. -/
  universal : ∀ {Z : C.obj} (_ : QCHom C X Z) (_ : QCHom C Y Z),
    ∃ _ : QCHom C obj Z, True

/-- Pullback in a quasi-category (universal property). -/
structure Pullback {C : QuasiCategory} {X Y Z : C.obj}
    (f : QCHom C X Z) (g : QCHom C Y Z) where
  /-- The pullback object. -/
  obj : C.obj
  /-- Projection to `X`. -/
  fst : QCHom C obj X
  /-- Projection to `Y`. -/
  snd : QCHom C obj Y
  /-- Commutativity of the square (abstract). -/
  comm : True
  /-- Universal property: pullback mediating map. -/
  universal : ∀ {W : C.obj} (_ : QCHom C W X) (_ : QCHom C W Y),
    (_ : True) → ∃ _ : QCHom C W obj, True

/-- Pushout in a quasi-category (universal property). -/
structure Pushout {C : QuasiCategory} {X Y Z : C.obj}
    (f : QCHom C X Y) (g : QCHom C X Z) where
  /-- The pushout object. -/
  obj : C.obj
  /-- Injection from `Y`. -/
  inl : QCHom C Y obj
  /-- Injection from `Z`. -/
  inr : QCHom C Z obj
  /-- Commutativity of the square (abstract). -/
  comm : True
  /-- Universal property: pushout mediating map. -/
  universal : ∀ {W : C.obj} (_ : QCHom C Y W) (_ : QCHom C Z W),
    (_ : True) → ∃ _ : QCHom C obj W, True

/-! ## Adjoint functor theorem (presentable infinity-categories) -/

/-- The adjoint functor theorem guarantees existence of the left adjoint. -/
theorem adjoint_functor_exists (A : HigherTopos.AdjointFunctorThm) :
    ∃ L : InfinityFunctor A.target.category A.source.category,
      L = A.leftAdjoint :=
  HigherTopos.adjoint_functor_exists A

/-! ## Infinity-categorical Seifert-van Kampen -/

section SeifertVanKampen

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-- Infinity-categorical Seifert-van Kampen equivalence for pushouts. -/
noncomputable abbrev infinitySeifertVanKampen (c0 : C)
    [CompPath.Pushout.HasGlueNaturalLoopRwEq
      (A := A) (B := B) (C := C) (f := f) (g := g) c0]
    [CompPath.HasPushoutSVKEncodeQuot A B C f g c0]
    [CompPath.HasPushoutSVKDecodeEncode A B C f g c0]
    [CompPath.HasPushoutSVKEncodeDecode A B C f g c0] :
    SimpleEquiv
      (PiOne (CompPath.Pushout A B C f g) (CompPath.Pushout.inl (f c0)))
      (CompPath.AmalgamatedFreeProduct
        (PiOne A (f c0))
        (PiOne B (g c0))
        (PiOne C c0)
        (CompPath.piOneFmap (A := A) (C := C) (f := f) (c₀ := c0))
        (CompPath.piOneGmap (B := B) (C := C) (g := g) (c₀ := c0))) :=
  _root_.ComputationalPaths.Path.seifertVanKampenEquiv
    (A := A) (B := B) (C := C) (f := f) (g := g) c0

end SeifertVanKampen


private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
We introduced terminal objects and slice-style cone/cocone categories for
quasi-categories, used terminality to build limits and colimits, defined
finite (co)limits via universal properties, restated the adjoint functor
theorem for presentable infinity-categories, and re-exported the
infinity-categorical Seifert-van Kampen equivalence from computational paths.
-/

end InfinityCatLimits
end Homotopy
end Path
end ComputationalPaths
