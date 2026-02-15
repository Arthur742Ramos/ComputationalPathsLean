/-
# Loop space recognition (computational paths)

This module packages a lightweight recognition principle for loop spaces using
computational paths.  A type is recognized as a loop space once it is equipped
with a `Path`-based equivalence to `LoopSpace` at some basepoint.

## Key Results

- `PathSimpleEquiv`: equivalence whose inverse laws are witnessed by `Path`
- `LoopSpaceRecognition`: data recognizing a type as a loop space
- `recognizeLoopSpace`, `recognizeLoopSpaceOfSimpleEquiv`: basic constructors

## References

- HoTT Book, Chapter 2 (loop spaces)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace LoopSpaceRecognition

universe u v

/-! ## Path-based equivalences -/

/-- Path-based equivalence structure (inverse laws witnessed by `Path`). -/
structure PathSimpleEquiv (α : Type u) (β : Type v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse after forward map is the identity, as a `Path`. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Forward after inverse map is the identity, as a `Path`. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Identity `PathSimpleEquiv`. -/
def pathSimpleEquivRefl (α : Type u) : PathSimpleEquiv α α :=
  { toFun := _root_.id
    invFun := _root_.id
    left_inv := fun x => Path.refl x
    right_inv := fun x => Path.refl x }

/-- Convert a `SimpleEquiv` into a `PathSimpleEquiv`. -/
def simpleEquivToPathSimpleEquiv {α : Type u} {β : Type v} (e : SimpleEquiv α β) :
    PathSimpleEquiv α β :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := fun x => Path.stepChain (e.left_inv x)
    right_inv := fun y => Path.stepChain (e.right_inv y) }

/-! ## Recognition data -/

/-- Data recognizing a type as a loop space. -/
structure LoopSpaceRecognition (L : Type u) : Type (u + 1) where
  /-- Underlying space whose loop space is recognized. -/
  space : Type u
  /-- Basepoint of the underlying space. -/
  base : space
  /-- Path-based equivalence to the loop space. -/
  equiv : PathSimpleEquiv L (LoopSpace space base)

/-- Any loop space recognizes itself. -/
def recognizeLoopSpace (A : Type u) (a : A) :
    LoopSpaceRecognition (LoopSpace A a) :=
  { space := A
    base := a
    equiv := pathSimpleEquivRefl (LoopSpace A a) }

/-- Recognition obtained from a `SimpleEquiv` to a loop space. -/
def recognizeLoopSpaceOfSimpleEquiv {L : Type u} {A : Type u} (a : A)
    (e : SimpleEquiv L (LoopSpace A a)) : LoopSpaceRecognition L :=
  { space := A
    base := a
    equiv := simpleEquivToPathSimpleEquiv e }

/-! ## Basic theorem placeholders -/

theorem pathSimpleEquivRefl_toFun_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).toFun x = x := by
  sorry

theorem pathSimpleEquivRefl_invFun_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).invFun x = x := by
  sorry

theorem pathSimpleEquivRefl_left_inv_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).left_inv x = Path.refl x := by
  sorry

theorem pathSimpleEquivRefl_right_inv_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).right_inv x = Path.refl x := by
  sorry

theorem simpleEquivToPathSimpleEquiv_toFun_apply {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    (simpleEquivToPathSimpleEquiv e).toFun x = e.toFun x := by
  sorry

theorem simpleEquivToPathSimpleEquiv_invFun_apply {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    (simpleEquivToPathSimpleEquiv e).invFun y = e.invFun y := by
  sorry

theorem simpleEquivToPathSimpleEquiv_left_inv_toEq {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    Path.toEq ((simpleEquivToPathSimpleEquiv e).left_inv x) = e.left_inv x := by
  sorry

theorem simpleEquivToPathSimpleEquiv_right_inv_toEq {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    Path.toEq ((simpleEquivToPathSimpleEquiv e).right_inv y) = e.right_inv y := by
  sorry

theorem recognizeLoopSpace_space (A : Type u) (a : A) :
    (recognizeLoopSpace A a).space = A := by
  sorry

theorem recognizeLoopSpace_base (A : Type u) (a : A) :
    (recognizeLoopSpace A a).base = a := by
  sorry

theorem recognizeLoopSpace_equiv_toFun_apply (A : Type u) (a : A)
    (p : LoopSpace A a) :
    (recognizeLoopSpace A a).equiv.toFun p = p := by
  sorry

theorem recognizeLoopSpace_equiv_invFun_apply (A : Type u) (a : A)
    (p : LoopSpace A a) :
    (recognizeLoopSpace A a).equiv.invFun p = p := by
  sorry

theorem recognizeLoopSpaceOfSimpleEquiv_space {L : Type u} {A : Type u} (a : A)
    (e : SimpleEquiv L (LoopSpace A a)) :
    (recognizeLoopSpaceOfSimpleEquiv a e).space = A := by
  sorry

theorem recognizeLoopSpaceOfSimpleEquiv_base {L : Type u} {A : Type u} (a : A)
    (e : SimpleEquiv L (LoopSpace A a)) :
    (recognizeLoopSpaceOfSimpleEquiv a e).base = a := by
  sorry

theorem recognizeLoopSpaceOfSimpleEquiv_left_inv_toEq {L : Type u} {A : Type u}
    (a : A) (e : SimpleEquiv L (LoopSpace A a)) (x : L) :
    Path.toEq ((recognizeLoopSpaceOfSimpleEquiv a e).equiv.left_inv x) = e.left_inv x := by
  sorry

/-! ## Summary -/

end LoopSpaceRecognition
end CompPath
end Path
end ComputationalPaths
