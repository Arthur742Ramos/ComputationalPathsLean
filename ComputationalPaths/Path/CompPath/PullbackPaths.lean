/- 
# Path Characterization for Pullbacks

This module defines pullbacks using computational paths and describes the
associated path spaces. It is dual to `PushoutPaths`: paths in a pullback are
captured by a base path in the product together with a compatible path in `C`.

## Key Results

- `Pullback`: pullback type of a span `A → C ← B`.
- `Pullback.coneEquiv`: universal property for maps into the pullback.
- `Pullback.PathSpace`: pullback path space data.
- `Pullback.path_eta`: reconstructs a pullback path from its components (RwEq).

## References

- HoTT Book, Chapter 2 (pullbacks and Sigma types).
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.ProductSigmaDerived

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u x

/-! ## Pullback type -/

/-- Pullback of a span `A → C ← B` as a dependent pair over `A × B`. -/
def Pullback (A : Type u) (B : Type u) (C : Type u)
    (f : A → C) (g : B → C) : Type u :=
  Sigma fun ab : A × B => Path (f ab.1) (g ab.2)

namespace Pullback

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : A → C} {g : B → C}

/-- The underlying product pair of a pullback element. -/
@[simp] def pair (x : Pullback A B C f g) : A × B := x.1

/-- First projection from the pullback. -/
@[simp] def fst (x : Pullback A B C f g) : A := x.1.1

/-- Second projection from the pullback. -/
@[simp] def snd (x : Pullback A B C f g) : B := x.1.2

/-- The commuting path in the pullback. -/
@[simp] def comm (x : Pullback A B C f g) : Path (f (fst x)) (g (snd x)) := x.2

/-- Constructor for pullback elements. -/
def mk (a : A) (b : B) (h : Path (f a) (g b)) : Pullback A B C f g :=
  ⟨(a, b), h⟩

@[simp] theorem pair_mk (a : A) (b : B) (h : Path (f a) (g b)) :
    pair (mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h) = (a, b) := rfl

@[simp] theorem fst_mk (a : A) (b : B) (h : Path (f a) (g b)) :
    fst (mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h) = a := rfl

@[simp] theorem snd_mk (a : A) (b : B) (h : Path (f a) (g b)) :
    snd (mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h) = b := rfl

@[simp] theorem comm_mk (a : A) (b : B) (h : Path (f a) (g b)) :
    comm (mk (A := A) (B := B) (C := C) (f := f) (g := g) a b h) = h := rfl

/-- Eta expansion for pullback elements. -/
theorem mk_eta (x : Pullback A B C f g) :
    mk (A := A) (B := B) (C := C) (f := f) (g := g) (fst x) (snd x) (comm x) = x := by
  cases x with
  | mk ab hcomm =>
      cases ab with
      | mk a b => rfl

/-! ## Universal property -/

/-- A pullback cone with vertex `X`. -/
def Cone (X : Type x) : Type (max u x) :=
  Σ p : X → A, Σ q : X → B, ∀ x : X, Path (f (p x)) (g (q x))

/-- The canonical lift into the pullback. -/
def lift {X : Type x} (p : X → A) (q : X → B)
    (h : ∀ x : X, Path (f (p x)) (g (q x))) :
    X → Pullback A B C f g :=
  fun x => mk (A := A) (B := B) (C := C) (f := f) (g := g) (p x) (q x) (h x)

@[simp] theorem fst_lift {X : Type x} (p : X → A) (q : X → B)
    (h : ∀ x : X, Path (f (p x)) (g (q x))) (x : X) :
    fst (lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x) = p x := rfl

@[simp] theorem snd_lift {X : Type x} (p : X → A) (q : X → B)
    (h : ∀ x : X, Path (f (p x)) (g (q x))) (x : X) :
    snd (lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x) = q x := rfl

@[simp] theorem comm_lift {X : Type x} (p : X → A) (q : X → B)
    (h : ∀ x : X, Path (f (p x)) (g (q x))) (x : X) :
    comm (lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h x) = h x := rfl

/-- Extract the pullback cone from a map into the pullback. -/
def coneMap {X : Type x} (k : X → Pullback A B C f g) : Cone (A := A) (B := B) (C := C)
    (f := f) (g := g) X :=
  ⟨fun x => fst (k x), ⟨fun x => snd (k x), fun x => comm (k x)⟩⟩

/-- Convert a pullback cone into the corresponding map. -/
def coneInv {X : Type x} : Cone (A := A) (B := B) (C := C) (f := f) (g := g) X →
    X → Pullback A B C f g
  | ⟨p, ⟨q, h⟩⟩ => lift (A := A) (B := B) (C := C) (f := f) (g := g) p q h

/-- Universal property: maps into the pullback are equivalent to pullback cones. -/
def coneEquiv (X : Type x) :
    SimpleEquiv (X → Pullback A B C f g)
      (Cone (A := A) (B := B) (C := C) (f := f) (g := g) X) where
  toFun := coneMap (A := A) (B := B) (C := C) (f := f) (g := g)
  invFun := coneInv (A := A) (B := B) (C := C) (f := f) (g := g)
  left_inv := by
    intro k
    funext x
    simpa [coneInv, coneMap, lift] using
      (mk_eta (A := A) (B := B) (C := C) (f := f) (g := g) (x := k x))
  right_inv := by
    intro c
    cases c with
    | mk p rest =>
        cases rest with
        | mk q h => rfl

/-! ## Pullback path spaces -/

/-- Pullback path space data between `x` and `y`. -/
def PathSpace (x y : Pullback A B C f g) : Type u :=
  Sigma fun p : Path (pair x) (pair y) =>
    Path
      (Path.transport (A := A × B)
        (D := fun ab => Path (f ab.1) (g ab.2)) p (comm x))
      (comm y)

/-- Convert a pullback path into pullback path-space data. -/
def pathToData {x y : Pullback A B C f g} (p : Path x y) : PathSpace (A := A) (B := B)
    (C := C) (f := f) (g := g) x y :=
  ⟨Path.sigmaFst p, Path.sigmaSnd p⟩

/-- Assemble a pullback path from pullback path-space data. -/
def pathFromData {x y : Pullback A B C f g} :
    PathSpace (A := A) (B := B) (C := C) (f := f) (g := g) x y → Path x y
  | ⟨p, q⟩ => Path.sigmaMk p q

/-- Pullback paths are determined by their components (sigma eta). -/
noncomputable def path_eta {x y : Pullback A B C f g} (p : Path x y) :
    RwEq (pathFromData (A := A) (B := B) (C := C) (f := f) (g := g)
      (pathToData (A := A) (B := B) (C := C) (f := f) (g := g) p)) p :=
  ProductSigmaDerived.rweq_sigmaMk_sigmaFst_sigmaSnd p

/-! ## Summary

We define the pullback of a span, describe its universal property via cones,
and show that pullback paths are determined by their sigma components.
-/

end Pullback
end CompPath
end Path
end ComputationalPaths
