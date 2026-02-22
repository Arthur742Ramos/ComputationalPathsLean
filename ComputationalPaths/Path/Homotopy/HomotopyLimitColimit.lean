/-
# Homotopy Limits and Colimits via Computational Paths

This module packages homotopy pullbacks and pushouts as homotopy limits and
colimits using Path-valued homotopies. We expose homotopy cones and cocones,
relate them to computational pullbacks, and give a recursor out of the
computational pushout.

## Key Results

- `HomotopyCone`, `homotopyLimitConeEquiv`: homotopy cones and their pullback
  universal property.
- `HomotopyCocone`, `homotopyColimitDesc`: homotopy cocones and the pushout
  recursor.
- `HomotopyLimit`, `HomotopyColimit`: pullback/pushout abbreviations.

## References

- HoTT Book, Chapter 2 (homotopy limits and colimits).
-/

import ComputationalPaths.Path.CompPath.PullbackPaths
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Homotopy.HoTT
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace HomotopyLimitColimit

open HoTT
open CompPath

universe u x

/-! ## Homotopy limits (pullbacks) -/

section HomotopyLimit

variable {A B C : Type u}

/-- Homotopy limit of a cospan, implemented as the computational pullback. -/
abbrev HomotopyLimit (f : A → C) (g : B → C) : Type u :=
  CompPath.Pullback A B C f g

/-- A homotopy cone over a cospan with vertex `X`. -/
structure HomotopyCone (X : Type x) (f : A → C) (g : B → C) : Type (max u x) where
  /-- Left leg of the cone. -/
  left : X → A
  /-- Right leg of the cone. -/
  right : X → B
  /-- Homotopy witnessing commutativity. -/
  comm : FunHomotopy (fun x => f (left x)) (fun x => g (right x))

namespace HomotopyCone

/-- A strictly commuting cone yields a homotopy cone. -/
noncomputable def of_eq {X : Type x} {f : A → C} {g : B → C}
    (left : X → A) (right : X → B)
    (h : (fun x => f (left x)) = (fun x => g (right x))) :
    HomotopyCone (X := X) f g :=
  { left := left
    right := right
    comm := fun x => Path.stepChain (_root_.congrArg (fun k => k x) h) }

/-- Convert a homotopy cone into a pullback cone. -/
noncomputable def toPullbackCone {X : Type x} {f : A → C} {g : B → C}
    (cone : HomotopyCone (X := X) f g) :
    CompPath.Pullback.Cone (A := A) (B := B) (C := C) (f := f) (g := g) X :=
  ⟨cone.left, ⟨cone.right, cone.comm⟩⟩

/-- Convert a pullback cone into a homotopy cone. -/
noncomputable def ofPullbackCone {X : Type x} {f : A → C} {g : B → C}
    (cone : CompPath.Pullback.Cone (A := A) (B := B) (C := C) (f := f) (g := g) X) :
    HomotopyCone (X := X) f g :=
  ⟨cone.1, cone.2.1, cone.2.2⟩

/-- Homotopy cones are equivalent to pullback cones. -/
noncomputable def pullbackConeEquiv {X : Type x} {f : A → C} {g : B → C} :
    SimpleEquiv
      (CompPath.Pullback.Cone (A := A) (B := B) (C := C) (f := f) (g := g) X)
      (HomotopyCone (X := X) f g) where
  toFun := ofPullbackCone (A := A) (B := B) (C := C) (f := f) (g := g)
  invFun := toPullbackCone (A := A) (B := B) (C := C) (f := f) (g := g)
  left_inv := by
    intro cone
    cases cone with
    | mk left rest =>
        cases rest with
        | mk right comm => rfl
  right_inv := by
    intro cone
    cases cone
    rfl

end HomotopyCone

/-- Maps into the homotopy limit correspond to homotopy cones. -/
noncomputable def homotopyLimitConeEquiv {X : Type x} {f : A → C} {g : B → C} :
    SimpleEquiv
      (X → HomotopyLimit (A := A) (B := B) (C := C) f g)
      (HomotopyCone (X := X) f g) :=
  SimpleEquiv.comp
    (CompPath.Pullback.coneEquiv (A := A) (B := B) (C := C) (f := f) (g := g) X)
    (HomotopyCone.pullbackConeEquiv (A := A) (B := B) (C := C) (f := f) (g := g) (X := X))

end HomotopyLimit

/-! ## Homotopy colimits (pushouts) -/

section HomotopyColimit

variable {A B C : Type u}

/-- Homotopy colimit of a span, implemented as the computational pushout. -/
abbrev HomotopyColimit (f : C → A) (g : C → B) : Type u :=
  CompPath.PushoutCompPath A B C f g

/-- A homotopy cocone over a span with vertex `X`. -/
structure HomotopyCocone (X : Type x) (f : C → A) (g : C → B) : Type (max u x) where
  /-- Left injection into the cocone. -/
  inl : A → X
  /-- Right injection into the cocone. -/
  inr : B → X
  /-- Homotopy witnessing the cocone condition. -/
  comm : FunHomotopy (fun c => inl (f c)) (fun c => inr (g c))

namespace HomotopyCocone

/-- A strictly commuting cocone yields a homotopy cocone. -/
noncomputable def of_eq {X : Type x} {f : C → A} {g : C → B}
    (inl : A → X) (inr : B → X)
    (h : (fun c => inl (f c)) = (fun c => inr (g c))) :
    HomotopyCocone (X := X) f g :=
  { inl := inl
    inr := inr
    comm := fun c => Path.stepChain (_root_.congrArg (fun k => k c) h) }

/-- Convert the homotopy commutativity into propositional equality. -/
noncomputable def commEq {X : Type x} {f : C → A} {g : C → B}
    (cone : HomotopyCocone (X := X) f g) :
    ∀ c : C, cone.inl (f c) = cone.inr (g c) :=
  fun c => (cone.comm c).toEq

end HomotopyCocone

/-- The canonical homotopy cocone on the pushout. -/
noncomputable def homotopyColimitCocone {A B C : Type u} (f : C → A) (g : C → B) :
    HomotopyCocone
      (X := HomotopyColimit (A := A) (B := B) (C := C) f g) f g :=
  { inl := fun a => PushoutCompPath.inl (A := A) (B := B) (C := C) (f := f) (g := g) a
    inr := fun b => PushoutCompPath.inr (A := A) (B := B) (C := C) (f := f) (g := g) b
    comm := fun c => PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c }

/-- Map out of the homotopy colimit using a homotopy cocone. -/
noncomputable def homotopyColimitDesc {X : Type x} {f : C → A} {g : C → B}
    (cone : HomotopyCocone (X := X) f g) :
    HomotopyColimit (A := A) (B := B) (C := C) f g → X :=
  Quot.lift
    (fun s =>
      match s with
      | Sum.inl a => cone.inl a
      | Sum.inr b => cone.inr b)
    (fun _ _ h => by
      cases h with
      | glue c => exact (cone.comm c).toEq)

/-- Evaluate the homotopy colimit descent on a left injection. -/
@[simp] theorem homotopyColimitDesc_inl {X : Type x} {f : C → A} {g : C → B}
    (cone : HomotopyCocone (X := X) f g) (a : A) :
    homotopyColimitDesc (f := f) (g := g) cone
        (PushoutCompPath.inl (A := A) (B := B) (C := C) (f := f) (g := g) a) =
      cone.inl a := rfl

/-- Evaluate the homotopy colimit descent on a right injection. -/
@[simp] theorem homotopyColimitDesc_inr {X : Type x} {f : C → A} {g : C → B}
    (cone : HomotopyCocone (X := X) f g) (b : B) :
    homotopyColimitDesc (f := f) (g := g) cone
        (PushoutCompPath.inr (A := A) (B := B) (C := C) (f := f) (g := g) b) =
      cone.inr b := rfl

/-- Turn a map out of the homotopy colimit into a homotopy cocone. -/
noncomputable def homotopyColimitCoconeMap {X : Type x} {f : C → A} {g : C → B}
    (h : HomotopyColimit (A := A) (B := B) (C := C) f g → X) :
    HomotopyCocone (X := X) f g :=
  { inl := fun a => h (PushoutCompPath.inl (A := A) (B := B) (C := C) (f := f) (g := g) a)
    inr := fun b => h (PushoutCompPath.inr (A := A) (B := B) (C := C) (f := f) (g := g) b)
    comm := fun c =>
      Path.congrArg h (PushoutCompPath.glue (A := A) (B := B) (C := C) (f := f) (g := g) c) }

/-- Descent is a left inverse to the cocone map. -/
theorem homotopyColimitDesc_coconeMap {X : Type x} {f : C → A} {g : C → B}
    (h : HomotopyColimit (A := A) (B := B) (C := C) f g → X) :
    homotopyColimitDesc (f := f) (g := g)
        (homotopyColimitCoconeMap (f := f) (g := g) h) = h := by
  funext x
  refine Quot.inductionOn x (fun s => ?_)
  cases s <;> rfl

end HomotopyColimit

/-! ## Summary -/

/-!
We packaged homotopy pullbacks as homotopy limits with Path-valued cones and
provided the cone equivalence, and we defined homotopy cocones and the pushout
recursor for homotopy colimits, all using computational paths.
-/

end HomotopyLimitColimit
end Path
end ComputationalPaths
