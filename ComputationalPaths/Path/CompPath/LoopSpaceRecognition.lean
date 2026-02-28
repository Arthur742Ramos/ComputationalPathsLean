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

namespace PathSimpleEquiv

variable {α : Type u} {β : Type v}

/-- Right-unit coherence on the left inverse witness. -/
noncomputable def left_inv_unit_rweq (e : PathSimpleEquiv α β) (x : α) :
    RwEq (Path.trans (e.left_inv x) (Path.refl x)) (e.left_inv x) :=
  rweq_cmpA_refl_right (e.left_inv x)

/-- Left-unit coherence on the right inverse witness. -/
noncomputable def right_inv_unit_rweq (e : PathSimpleEquiv α β) (y : β) :
    RwEq (Path.trans (Path.refl (e.toFun (e.invFun y))) (e.right_inv y)) (e.right_inv y) :=
  rweq_cmpA_refl_left (e.right_inv y)

/-- Cancellation on the left inverse witness. -/
noncomputable def left_inv_cancel_rweq (e : PathSimpleEquiv α β) (x : α) :
    RwEq (Path.trans (Path.symm (e.left_inv x)) (e.left_inv x)) (Path.refl x) :=
  rweq_cmpA_inv_left (e.left_inv x)

/-- Cancellation on the right inverse witness. -/
noncomputable def right_inv_cancel_rweq (e : PathSimpleEquiv α β) (y : β) :
    RwEq (Path.trans (e.right_inv y) (Path.symm (e.right_inv y)))
      (Path.refl (e.toFun (e.invFun y))) :=
  rweq_cmpA_inv_right (e.right_inv y)

/-- Symmetric form of left-cancellation. -/
noncomputable def left_inv_cancel_rweq_symm (e : PathSimpleEquiv α β) (x : α) :
    RwEq (Path.refl x) (Path.trans (Path.symm (e.left_inv x)) (e.left_inv x)) :=
  rweq_symm (left_inv_cancel_rweq e x)

/-- Symmetric form of right-cancellation. -/
noncomputable def right_inv_cancel_rweq_symm (e : PathSimpleEquiv α β) (y : β) :
    RwEq (Path.refl (e.toFun (e.invFun y)))
      (Path.trans (e.right_inv y) (Path.symm (e.right_inv y))) :=
  rweq_symm (right_inv_cancel_rweq e y)

/-- Double symmetry on the left inverse witness collapses via rewrite equality. -/
noncomputable def left_inv_double_symm_rweq (e : PathSimpleEquiv α β) (x : α) :
    RwEq (Path.symm (Path.symm (e.left_inv x))) (e.left_inv x) :=
  rweq_ss (e.left_inv x)

/-- Double symmetry on the right inverse witness collapses via rewrite equality. -/
noncomputable def right_inv_double_symm_rweq (e : PathSimpleEquiv α β) (y : β) :
    RwEq (Path.symm (Path.symm (e.right_inv y))) (e.right_inv y) :=
  rweq_ss (e.right_inv y)

/-- Associativity + unit + inverse coherence on the left inverse witness. -/
noncomputable def left_inv_assoc_cancel_rweq (e : PathSimpleEquiv α β) (x : α) :
    RwEq
      (Path.trans (Path.trans (Path.symm (e.left_inv x)) (e.left_inv x)) (Path.refl x))
      (Path.refl x) := by
  refine RwEq.trans (rweq_tt (Path.symm (e.left_inv x)) (e.left_inv x) (Path.refl x)) ?_
  refine RwEq.trans (rweq_trans_congr_right (Path.symm (e.left_inv x)) (left_inv_unit_rweq e x)) ?_
  exact left_inv_cancel_rweq e x

/-- Right-unit coherence transported through right-cancellation. -/
noncomputable def right_inv_refl_cancel_rweq (e : PathSimpleEquiv α β) (y : β) :
    RwEq
      (Path.trans (Path.refl (e.toFun (e.invFun y)))
        (Path.trans (e.right_inv y) (Path.symm (e.right_inv y))))
      (Path.refl (e.toFun (e.invFun y))) := by
  refine RwEq.trans
    (rweq_trans_congr_right (Path.refl (e.toFun (e.invFun y))) (right_inv_cancel_rweq e y)) ?_
  exact rweq_cmpA_refl_left (Path.refl (e.toFun (e.invFun y)))

end PathSimpleEquiv

/-- Identity `PathSimpleEquiv`. -/
noncomputable def pathSimpleEquivRefl (α : Type u) : PathSimpleEquiv α α :=
  { toFun := _root_.id
    invFun := _root_.id
    left_inv := fun x => Path.refl x
    right_inv := fun x => Path.refl x }

/-- Convert a `SimpleEquiv` into a `PathSimpleEquiv`. -/
noncomputable def simpleEquivToPathSimpleEquiv {α : Type u} {β : Type v} (e : SimpleEquiv α β) :
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
noncomputable def recognizeLoopSpace (A : Type u) (a : A) :
    LoopSpaceRecognition (LoopSpace A a) :=
  { space := A
    base := a
    equiv := pathSimpleEquivRefl (LoopSpace A a) }

/-- Recognition obtained from a `SimpleEquiv` to a loop space. -/
noncomputable def recognizeLoopSpaceOfPathSimpleEquiv {L : Type u} {A : Type u} (a : A)
    (e : PathSimpleEquiv L (LoopSpace A a)) : LoopSpaceRecognition L :=
  { space := A
    base := a
    equiv := e }

/-- Recognition obtained from a `SimpleEquiv` to a loop space. -/
noncomputable def recognizeLoopSpaceOfSimpleEquiv {L : Type u} {A : Type u} (a : A)
    (e : SimpleEquiv L (LoopSpace A a)) : LoopSpaceRecognition L :=
  recognizeLoopSpaceOfPathSimpleEquiv a (simpleEquivToPathSimpleEquiv e)

/-! ## Basic theorem placeholders -/

theorem pathSimpleEquivRefl_toFun_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).toFun x = x := by
  rfl

theorem pathSimpleEquivRefl_invFun_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).invFun x = x := by
  rfl

theorem pathSimpleEquivRefl_left_inv_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).left_inv x = Path.refl x := by
  rfl

theorem pathSimpleEquivRefl_right_inv_apply (α : Type u) (x : α) :
    (pathSimpleEquivRefl α).right_inv x = Path.refl x := by
  rfl

theorem simpleEquivToPathSimpleEquiv_toFun_apply {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    (simpleEquivToPathSimpleEquiv e).toFun x = e.toFun x := by
  rfl

theorem simpleEquivToPathSimpleEquiv_invFun_apply {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    (simpleEquivToPathSimpleEquiv e).invFun y = e.invFun y := by
  rfl

theorem simpleEquivToPathSimpleEquiv_left_inv_path {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    (simpleEquivToPathSimpleEquiv e).left_inv x = Path.stepChain (e.left_inv x) := by
  rfl

theorem simpleEquivToPathSimpleEquiv_right_inv_path {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    (simpleEquivToPathSimpleEquiv e).right_inv y = Path.stepChain (e.right_inv y) := by
  rfl

theorem simpleEquivToPathSimpleEquiv_left_inv_toEq {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    Path.toEq ((simpleEquivToPathSimpleEquiv e).left_inv x) = e.left_inv x := by
  rfl

theorem simpleEquivToPathSimpleEquiv_right_inv_toEq {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    Path.toEq ((simpleEquivToPathSimpleEquiv e).right_inv y) = e.right_inv y := by
  rfl

theorem recognizeLoopSpace_space (A : Type u) (a : A) :
    (recognizeLoopSpace A a).space = A := by
  rfl

theorem recognizeLoopSpace_base (A : Type u) (a : A) :
    (recognizeLoopSpace A a).base = a := by
  rfl

theorem recognizeLoopSpace_equiv_toFun_apply (A : Type u) (a : A)
    (p : LoopSpace A a) :
    (recognizeLoopSpace A a).equiv.toFun p = p := by
  rfl

theorem recognizeLoopSpace_equiv_invFun_apply (A : Type u) (a : A)
    (p : LoopSpace A a) :
    (recognizeLoopSpace A a).equiv.invFun p = p := by
  rfl

theorem recognizeLoopSpaceOfSimpleEquiv_space {L : Type u} {A : Type u} (a : A)
    (e : SimpleEquiv L (LoopSpace A a)) :
    (recognizeLoopSpaceOfSimpleEquiv a e).space = A := by
  rfl

theorem recognizeLoopSpaceOfSimpleEquiv_base {L : Type u} {A : Type u} (a : A)
    (e : SimpleEquiv L (LoopSpace A a)) :
    (recognizeLoopSpaceOfSimpleEquiv a e).base = a := by
  rfl

theorem recognizeLoopSpaceOfSimpleEquiv_left_inv_path {L : Type u} {A : Type u}
    (a : A) (e : SimpleEquiv L (LoopSpace A a)) (x : L) :
    (recognizeLoopSpaceOfSimpleEquiv a e).equiv.left_inv x = Path.stepChain (e.left_inv x) := by
  rfl

theorem recognizeLoopSpaceOfSimpleEquiv_left_inv_toEq {L : Type u} {A : Type u}
    (a : A) (e : SimpleEquiv L (LoopSpace A a)) (x : L) :
    Path.toEq ((recognizeLoopSpaceOfSimpleEquiv a e).equiv.left_inv x) = e.left_inv x := by
  rfl

noncomputable def simpleEquivToPathSimpleEquiv_left_inv_assoc_cancel_rweq {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (x : α) :
    RwEq
      (Path.trans
        (Path.trans
          (Path.symm ((simpleEquivToPathSimpleEquiv e).left_inv x))
          ((simpleEquivToPathSimpleEquiv e).left_inv x))
        (Path.refl x))
      (Path.refl x) := by
  exact PathSimpleEquiv.left_inv_assoc_cancel_rweq (simpleEquivToPathSimpleEquiv e) x

noncomputable def simpleEquivToPathSimpleEquiv_right_inv_refl_cancel_rweq {α : Type u} {β : Type v}
    (e : SimpleEquiv α β) (y : β) :
    RwEq
      (Path.trans
        (Path.refl ((simpleEquivToPathSimpleEquiv e).toFun ((simpleEquivToPathSimpleEquiv e).invFun y)))
        (Path.trans
          ((simpleEquivToPathSimpleEquiv e).right_inv y)
          (Path.symm ((simpleEquivToPathSimpleEquiv e).right_inv y)))
      )
      (Path.refl ((simpleEquivToPathSimpleEquiv e).toFun ((simpleEquivToPathSimpleEquiv e).invFun y))) := by
  exact PathSimpleEquiv.right_inv_refl_cancel_rweq (simpleEquivToPathSimpleEquiv e) y

noncomputable def recognizeLoopSpaceOfSimpleEquiv_left_inv_double_symm_rweq {L : Type u} {A : Type u}
    (a : A) (e : SimpleEquiv L (LoopSpace A a)) (x : L) :
    RwEq
      (Path.symm (Path.symm ((recognizeLoopSpaceOfSimpleEquiv a e).equiv.left_inv x)))
      ((recognizeLoopSpaceOfSimpleEquiv a e).equiv.left_inv x) := by
  exact PathSimpleEquiv.left_inv_double_symm_rweq (recognizeLoopSpaceOfSimpleEquiv a e).equiv x

/-! ## Summary -/

end LoopSpaceRecognition
end CompPath
end Path
end ComputationalPaths
