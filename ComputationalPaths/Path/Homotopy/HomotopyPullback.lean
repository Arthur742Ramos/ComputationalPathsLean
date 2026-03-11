/-
# Homotopy Properties of Pullback Squares

This module records basic homotopy-invariance properties for pullback squares in
the computational paths setting.

## Key Results

- `HomotopyPullbackSquare`: squares commuting up to Path-valued homotopy.
- `HomotopyPullbackSquare.of_eq`: strict commutation gives a homotopy square.
- `pullback_square_commutes`: the canonical computational pullback square commutes.

## References

- HoTT Book, Chapter 2 (pullbacks and homotopies).
-/

import ComputationalPaths.Path.CompPath.PullbackPaths
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace HomotopyPullback

open HoTT
open CompPath

universe u

/-! ## Definition -/

/-- A pullback square that commutes up to homotopy.
    For maps f : X → Z and g : Y → Z with projections p1 : P → X and p2 : P → Y,
    the square commutes up to homotopy if f ∘ p1 is homotopic to g ∘ p2. -/
structure HomotopyPullbackSquare {X Y Z P : Type u}
    (f : X → Z) (g : Y → Z) (p1 : P → X) (p2 : P → Y) : Type u where
  /-- Pointwise homotopy witnessing the commutative square. -/
  comm : FunHomotopy (fun p => f (p1 p)) (fun p => g (p2 p))

namespace HomotopyPullbackSquare

/-! ## Basic properties -/

/-- A strictly commuting square yields a homotopy pullback square. -/
noncomputable def of_eq {X Y Z P : Type u} {f : X → Z} {g : Y → Z}
    {p1 : P → X} {p2 : P → Y}
    (h : (fun p => f (p1 p)) = (fun p => g (p2 p))) :
    HomotopyPullbackSquare f g p1 p2 where
  comm := fun p =>
    Path.stepChain (_root_.congrArg (fun k => k p) h)

/-- Homotopy pullback squares are symmetric in composition order. -/
noncomputable def symm {X Y Z P : Type u} {f : X → Z} {g : Y → Z}
    {p1 : P → X} {p2 : P → Y} (h : HomotopyPullbackSquare f g p1 p2) :
    FunHomotopy (fun p => g (p2 p)) (fun p => f (p1 p)) :=
  fun p => Path.symm (h.comm p)

/-- Applying `of_eq` recovers the original strict commutativity witness pointwise. -/
noncomputable def of_eq_apply_path {X Y Z P : Type u} {f : X → Z} {g : Y → Z}
    {p1 : P → X} {p2 : P → Y}
    (h : (fun p => f (p1 p)) = (fun p => g (p2 p))) (p : P) :
    Path ((of_eq h).comm p) (Path.stepChain (_root_.congrArg (fun k => k p) h)) :=
  Path.refl _

end HomotopyPullbackSquare

/-! ## Pullback square in the path setting -/

/-- `Path` witness for the first projection of a pullback constructor. -/
noncomputable def pullback_fst_mk_path {A B C : Type u} {f : A → C} {g : B → C}
    (a : A) (b : B) (h : Path (f a) (g b)) :
    Path
      (CompPath.Pullback.fst (CompPath.Pullback.mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h))
      a :=
  Path.stepChain (CompPath.Pullback.fst_mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h)

/-- `Path` witness for the second projection of a pullback constructor. -/
noncomputable def pullback_snd_mk_path {A B C : Type u} {f : A → C} {g : B → C}
    (a : A) (b : B) (h : Path (f a) (g b)) :
    Path
      (CompPath.Pullback.snd (CompPath.Pullback.mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h))
      b :=
  Path.stepChain (CompPath.Pullback.snd_mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h)

/-- `Path` witness for the commuting path of a pullback constructor. -/
noncomputable def pullback_comm_mk_path {A B C : Type u} {f : A → C} {g : B → C}
    (a : A) (b : B) (h : Path (f a) (g b)) :
    Path
      (CompPath.Pullback.comm (CompPath.Pullback.mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h))
      h :=
  Path.stepChain (CompPath.Pullback.comm_mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h)

/-- `Path` witness for eta expansion of pullback elements. -/
noncomputable def pullback_mk_eta_path {A B C : Type u} {f : A → C} {g : B → C}
    (x : CompPath.Pullback A B C f g) :
    Path
      (CompPath.Pullback.mk (A := A) (B := B) (C := C) (f := f) (g := g)
        (CompPath.Pullback.fst x) (CompPath.Pullback.snd x) (CompPath.Pullback.comm x))
      x :=
  Path.stepChain (CompPath.Pullback.mk_eta (A := A) (B := B) (C := C) (f := f) (g := g) x)

/-- `Path` witness for the first projection of a lifted pullback cone. -/
noncomputable def pullback_fst_lift_path {A B C X : Type u} {f : A → C} {g : B → C}
    (p : X → A) (q : X → B) (h : ∀ x : X, Path (f (p x)) (g (q x))) (x : X) :
    Path
      (CompPath.Pullback.fst (CompPath.Pullback.lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x))
      (p x) :=
  Path.stepChain (CompPath.Pullback.fst_lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x)

/-- `Path` witness for the second projection of a lifted pullback cone. -/
noncomputable def pullback_snd_lift_path {A B C X : Type u} {f : A → C} {g : B → C}
    (p : X → A) (q : X → B) (h : ∀ x : X, Path (f (p x)) (g (q x))) (x : X) :
    Path
      (CompPath.Pullback.snd (CompPath.Pullback.lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x))
      (q x) :=
  Path.stepChain (CompPath.Pullback.snd_lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x)

/-- `Path` witness for the commuting component of a lifted pullback cone. -/
noncomputable def pullback_comm_lift_path {A B C X : Type u} {f : A → C} {g : B → C}
    (p : X → A) (q : X → B) (h : ∀ x : X, Path (f (p x)) (g (q x))) (x : X) :
    Path
      (CompPath.Pullback.comm (CompPath.Pullback.lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x))
      (h x) :=
  Path.stepChain (CompPath.Pullback.comm_lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x)

/-- `Path` witness for the left round-trip of the pullback universal property. -/
noncomputable def pullback_cone_left_inv_path {A B C X : Type u} {f : A → C} {g : B → C}
    (k : X → CompPath.Pullback A B C f g) :
    Path
      ((CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X).invFun
        ((CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X).toFun k))
      k :=
  Path.stepChain
    ((CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X).left_inv k)

/-- `Path` witness for the right round-trip of the pullback universal property. -/
noncomputable def pullback_cone_right_inv_path {A B C X : Type u} {f : A → C} {g : B → C}
    (c : CompPath.Pullback.Cone (A := A) (B := B) (C := C) (f := f) (g := g) X) :
    Path
      ((CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X).toFun
        ((CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X).invFun c))
      c :=
  Path.stepChain
    ((CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X).right_inv c)

/-- Re-export the sigma-style path eta witness for computational pullbacks. -/
noncomputable def pullback_path_eta {A B C : Type u} {f : A → C} {g : B → C}
    {x y : CompPath.Pullback A B C f g} (p : Path x y) :
    RwEq
      (CompPath.Pullback.pathFromData (A := A) (B := B) (C := C) (f := f) (g := g)
        (CompPath.Pullback.pathToData (A := A) (B := B) (C := C) (f := f) (g := g) p))
      p :=
  CompPath.Pullback.path_eta (A := A) (B := B) (C := C) (f := f) (g := g) p

/-- The canonical pullback square in the computational pullback type commutes. -/
noncomputable def pullback_square_commutes {A B C : Type u} (f : A → C) (g : B → C) :
    HomotopyPullbackSquare f g
      (CompPath.Pullback.fst (f := f) (g := g))
      (CompPath.Pullback.snd (f := f) (g := g)) where
  comm := fun x => CompPath.Pullback.comm (f := f) (g := g) x

/-- Pointwise access to the commuting path of the canonical computational pullback square. -/
noncomputable def pullback_square_commutes_path {A B C : Type u} (f : A → C) (g : B → C)
    (x : CompPath.Pullback A B C f g) :
    Path (f (CompPath.Pullback.fst x)) (g (CompPath.Pullback.snd x)) :=
  (pullback_square_commutes f g).comm x

/-! ## Summary

We defined homotopy pullback squares using computational paths, showed that
strict commutation yields a Path-valued homotopy, and recorded the canonical
pullback square for the computational pullback type.
-/

end HomotopyPullback
end Path
end ComputationalPaths
